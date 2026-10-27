module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.Walter.ReeOrder.JT.Defs

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup

section Product

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_le_centralizer {t : G} {B : Subgroup G}
    (htB : zpowers t ≤ centralizer (B : Set G)) {x : G} (hx : x ∈ zpowers t ⊔ B) :
    ∃ i : ℤ, ∃ z ∈ B, x = t ^ i * z := by
  have hcomm : ∀ (i : ℤ) {z : G}, z ∈ B → z * t ^ i = t ^ i * z := fun i z hz =>
    (mem_centralizer_iff.mp (htB (zpow_mem (mem_zpowers t) i)) z hz)
  let S : Subgroup G :=
    { carrier := {x | ∃ i : ℤ, ∃ z ∈ B, x = t ^ i * z}
      mul_mem' := by
        rintro _ _ ⟨i, z, hz, rfl⟩ ⟨j, w, hw, rfl⟩
        refine ⟨i + j, z * w, mul_mem hz hw, ?_⟩
        rw [zpow_add, mul_assoc, ← mul_assoc z, hcomm j hz]
        group
      one_mem' := ⟨0, 1, one_mem B, by rw [zpow_zero, one_mul]⟩
      inv_mem' := by
        rintro _ ⟨i, z, hz, rfl⟩
        refine ⟨-i, z⁻¹, inv_mem hz, ?_⟩
        have h := hcomm (-i) (inv_mem hz)
        rw [zpow_neg] at h
        rw [mul_inv_rev, zpow_neg, h] }
  have hle : zpowers t ⊔ B ≤ S := sup_le
    (zpowers_le.mpr ⟨1, 1, one_mem B, by rw [zpow_one, mul_one]⟩)
    (fun z hz => ⟨0, z, hz, by rw [zpow_zero, one_mul]⟩)
  exact hle hx

theorem eq_of_isComponentOf_sup_zpowers [Finite G] {t : G} {B X : Subgroup G}
    (htB : zpowers t ≤ centralizer (B : Set G)) (hB : IsSimpleGroup B)
    (hBnab : ∃ x y : B, x * y ≠ y * x) (hX : CFSG.Assembly.IsComponentOf X (zpowers t ⊔ B)) :
    X = B := by
  have hZ := center_eq_bot_of_isSimpleGroup hBnab
  have hcomm : ∀ (i : ℤ) {z : G}, z ∈ B → z * t ^ i = t ^ i * z := fun i z hz =>
    (mem_centralizer_iff.mp (htB (zpow_mem (mem_zpowers t) i)) z hz)
  have hcen : ∀ x ∈ zpowers t ⊔ B, x ∈ centralizer (B : Set G) → x ∈ zpowers t := by
    intro x hx hxc
    obtain ⟨i, z, hz, rfl⟩ := mem_sup_zpowers_of_le_centralizer htB hx
    have hzc : (⟨z, hz⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro w
      apply Subtype.ext
      have h1 := mem_centralizer_iff.mp hxc w w.2
      change (w : G) * z = z * w
      have h2 : (w : G) * t ^ i = t ^ i * w := hcomm i w.2
      calc (w : G) * z = (t ^ i)⁻¹ * (t ^ i * w * z) := by group
        _ = (t ^ i)⁻¹ * (w * t ^ i * z) := by rw [h2]
        _ = (t ^ i)⁻¹ * (w * (t ^ i * z)) := by group
        _ = (t ^ i)⁻¹ * (t ^ i * z * w) := by rw [h1]
        _ = z * w := by group
    rw [hZ, mem_bot] at hzc
    have hz1 : z = 1 := congrArg Subtype.val hzc
    rw [hz1, mul_one]
    exact zpow_mem (mem_zpowers t) i
  have hfwd : ∀ y ∈ zpowers t ⊔ B, ∀ g ∈ B, y * g * y⁻¹ ∈ B := by
    intro y hy g hg
    obtain ⟨i, z, hz, rfl⟩ := mem_sup_zpowers_of_le_centralizer htB hy
    have hzg : z * g * z⁻¹ ∈ B := mul_mem (mul_mem hz hg) (inv_mem hz)
    have h1 : t ^ i * z * g * (t ^ i * z)⁻¹ = z * g * z⁻¹ := by
      calc t ^ i * z * g * (t ^ i * z)⁻¹ = (t ^ i * (z * g * z⁻¹)) * (t ^ i)⁻¹ := by group
        _ = (z * g * z⁻¹ * t ^ i) * (t ^ i)⁻¹ := by rw [hcomm i hzg]
        _ = z * g * z⁻¹ := by group
    rw [h1]
    exact hzg
  refine eq_of_isComponentOf_simple hB (isComponentOf_of_normal_of_comm le_sup_right
    (fun y hy => ?_) (fun x hx hxc y hy hyc => ?_) hX)
  · rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hfwd y hy g hg, fun hg => ?_⟩
    have h := hfwd y⁻¹ (inv_mem hy) _ hg
    rwa [show y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g by group] at h
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hcen x hx hxc)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hcen y hy hyc)
    exact (Commute.zpow_zpow_self t i j).eq

end Product

theorem mem_centralizer_conj_iff {P : Type*} [Group P] (hZ : center P = ⊥) (β : MulAut P)
    (t : P) : β ∈ centralizer {MulAut.conj t} ↔ β t = t := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply conj_injective_of_center_eq_bot hZ
    rw [← mulAut_mul_conj_mul_inv, h, mul_inv_cancel_right]
  · intro h
    have h1 : β * MulAut.conj t * β⁻¹ = MulAut.conj t := by rw [mulAut_mul_conj_mul_inv, h]
    calc β * MulAut.conj t = β * MulAut.conj t * β⁻¹ * β := by group
      _ = MulAut.conj t * β := by rw [h1]

theorem isInternalDirectProduct_map_iff {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {X Y Z : Subgroup G} :
    CFSG.Walter.JT.IsInternalDirectProduct (X.map f) (Y.map f) (Z.map f) ↔
      CFSG.Walter.JT.IsInternalDirectProduct X Y Z := by
  have hcen : ∀ {X Y : Subgroup G}, X.map f ≤ centralizer ((Y.map f : Subgroup H) : Set H) ↔
      X ≤ centralizer (Y : Set G) := by
    intro X Y
    constructor
    · intro h x hx
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := mem_centralizer_iff.mp (h (mem_map_of_mem f hx)) (f y) (mem_map_of_mem f hy)
      apply hf
      rw [map_mul, map_mul, h1]
    · rintro h _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (h hx) y hy]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨map_injective hf (by rw [Subgroup.map_sup, h1]), ?_, hcen.mp h3⟩
    rw [disjoint_iff] at h2 ⊢
    apply map_injective hf
    rw [map_inf_eq _ _ f hf, h2, Subgroup.map_bot]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by rw [← Subgroup.map_sup, h1], ?_, hcen.mpr h3⟩
    rw [disjoint_iff] at h2 ⊢
    rw [← map_inf_eq _ _ f hf, h2, Subgroup.map_bot]

theorem exists_quotient_mulEquiv_of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {T N : Subgroup G} {R : Subgroup H} (hmap : T.map f = R) (hker : T ⊓ f.ker = N) :
    ∃ _ : (N.subgroupOf T).Normal, ∃ e : T ⧸ N.subgroupOf T ≃* R,
      ∀ v : T, (e (QuotientGroup.mk v) : H) = f v := by
  let fT : T →* R := (f.comp T.subtype).codRestrict R fun v => by
    rw [← hmap]
    exact mem_map_of_mem f v.2
  have hs : Function.Surjective fT := by
    rintro ⟨r, hr⟩
    rw [← hmap] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    exact ⟨⟨v, hv⟩, rfl⟩
  have hk : fT.ker = N.subgroupOf T := by
    ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hker]
    constructor
    · intro h
      exact mem_inf.mpr ⟨v.2, MonoidHom.mem_ker.mpr (congrArg Subtype.val h)⟩
    · intro h
      exact Subtype.ext (MonoidHom.mem_ker.mp (mem_inf.mp h).2)
  have hn : (N.subgroupOf T).Normal := hk ▸ fT.normal_ker
  exact ⟨hn, (QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective fT hs), fun v => rfl⟩

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
theorem map_inf_centralizer_conj (hZ : center P = ⊥) {t : P}
    (hfus : ∀ x : P, orderOf x = 2 → ∃ y : P, y * x * y⁻¹ = t) (ht : orderOf t = 2)
    {U : Subgroup (MulAut P)} (hU : OuterAutomorphisms.inner P ≤ U) :
    (U ⊓ centralizer {MulAut.conj t}).map (QuotientGroup.mk' (OuterAutomorphisms.inner P)) =
        U.map (QuotientGroup.mk' (OuterAutomorphisms.inner P)) ∧
      U ⊓ centralizer {MulAut.conj t} ⊓ (QuotientGroup.mk' (OuterAutomorphisms.inner P)).ker =
        (centralizer {t}).map MulAut.conj := by
  have hconj := conj_injective_of_center_eq_bot hZ
  have hNt : OuterAutomorphisms.inner P ⊓ centralizer {MulAut.conj t} =
      (centralizer {t}).map MulAut.conj := by
    rw [SymmetricLocal.map_centralizer_singleton_of_injective _ hconj t]
    rfl
  refine ⟨le_antisymm (map_mono inf_le_left) ?_, ?_⟩
  · rintro _ ⟨β, hβ, rfl⟩
    have h2 : orderOf (β t) = 2 := (orderOf_injective β.toMonoidHom β.injective t).trans ht
    obtain ⟨y, hy⟩ := hfus (β t) h2
    have hyI : MulAut.conj y ∈ OuterAutomorphisms.inner P :=
      (show MulAut.conj y ∈ (MulAut.conj : P →* MulAut P).range from ⟨y, rfl⟩)
    refine ⟨MulAut.conj y * β, mem_inf.mpr ⟨mul_mem (hU hyI) hβ, ?_⟩, ?_⟩
    · rw [mem_centralizer_conj_iff hZ]
      rw [MulAut.mul_apply, MulAut.conj_apply, hy]
    · have h1 : QuotientGroup.mk' (OuterAutomorphisms.inner P) (MulAut.conj y) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hyI
      rw [map_mul, h1, one_mul]
  · rw [QuotientGroup.ker_mk', inf_assoc, inf_comm (centralizer _), ← inf_assoc,
      inf_eq_right.mpr hU, hNt]

theorem fixed_outer_structure (hZ : center P = ⊥) {t : P}
    (hfus : ∀ x : P, orderOf x = 2 → ∃ y : P, y * x * y⁻¹ = t) (ht : orderOf t = 2)
    {Fld : Subgroup (MulAut P)} (hFM : Fld ≤ centralizer {MulAut.conj t})
    (hFinj : Nat.card Fld = Nat.card (Fld.map (QuotientGroup.mk' (OuterAutomorphisms.inner P))))
    {R : Subgroup (Outer P)} (hRn : R.Normal)
    (hRF : R.IsComplement' (Fld.map (QuotientGroup.mk' (OuterAutomorphisms.inner P)))) :
    (∀ β : MulAut P, β ∈ centralizer {MulAut.conj t} ↔ β t = t) ∧
    centralizer {MulAut.conj t} ⊓ OuterAutomorphisms.inner P =
      (centralizer {t}).map MulAut.conj ∧
    (centralizer {MulAut.conj t}).map (QuotientGroup.mk' (OuterAutomorphisms.inner P)) = ⊤ ∧
    centralizer {MulAut.conj t} ⊓ (QuotientGroup.mk' (OuterAutomorphisms.inner P)).ker =
      (centralizer {t}).map MulAut.conj ∧
    (centralizer {t}).map MulAut.conj ≤
      centralizer {MulAut.conj t} ⊓ R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P)) ∧
    (((centralizer {t}).map MulAut.conj).subgroupOf
      (centralizer {MulAut.conj t} ⊓
        R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P)))).Normal ∧
    ((centralizer {MulAut.conj t} ⊓
        R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P))).subgroupOf
      (centralizer {MulAut.conj t})).Normal ∧
    (centralizer {MulAut.conj t} ⊓ R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P))).map
      (QuotientGroup.mk' (OuterAutomorphisms.inner P)) = R ∧
    centralizer {MulAut.conj t} ⊓ R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P)) ⊓
      (QuotientGroup.mk' (OuterAutomorphisms.inner P)).ker = (centralizer {t}).map MulAut.conj ∧
    centralizer {MulAut.conj t} ⊓ R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P)) ⊓
      Fld = ⊥ ∧
    ∀ β ∈ centralizer {MulAut.conj t}, ∃! vτ : ↥(centralizer {MulAut.conj t} ⊓
      R.comap (QuotientGroup.mk' (OuterAutomorphisms.inner P))) × Fld,
        (vτ.1 : MulAut P) * vτ.2 = β := by
  classical
  set π := QuotientGroup.mk' (OuterAutomorphisms.inner P) with hπ
  set Mt := centralizer {MulAut.conj t} with hMt
  set Nt := (centralizer {t}).map MulAut.conj with hNt
  set Tt := Mt ⊓ R.comap π with hTt
  obtain ⟨hsurj, hker⟩ := map_inf_centralizer_conj hZ hfus ht (U := ⊤) le_top
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hsurj
  rw [top_inf_eq] at hker
  have hconj := conj_injective_of_center_eq_bot hZ
  have hinnN : Mt ⊓ OuterAutomorphisms.inner P = Nt := by
    rw [inf_comm, hNt, SymmetricLocal.map_centralizer_singleton_of_injective _ hconj t]
    rfl
  have hNM : Nt ≤ Mt := hinnN ▸ inf_le_left
  have hNinn : Nt ≤ OuterAutomorphisms.inner P := hinnN ▸ inf_le_right
  have hπ1 : ∀ x ∈ OuterAutomorphisms.inner P, π x = 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
    exact hx
  have hNT : Nt ≤ Tt := le_inf hNM fun x hx => by
    rw [mem_comap, hπ1 x (hNinn hx)]
    exact one_mem R
  have hinnormal := OuterAutomorphisms.inner_normal P
  have hTmap : Tt.map π = R := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro r hr
      obtain ⟨β, hβ, hβr⟩ := (Subgroup.eq_top_iff' _).mp hsurj r
      exact ⟨β, mem_inf.mpr ⟨hβ, by rw [mem_comap, hβr]; exact hr⟩, hβr⟩
  have hTker : Tt ⊓ π.ker = Nt := by
    apply le_antisymm
    · rintro x ⟨hxT, hxk⟩
      rw [← hinnN]
      exact mem_inf.mpr ⟨hxT.1, (QuotientGroup.ker_mk' (OuterAutomorphisms.inner P)) ▸ hxk⟩
    · exact le_inf hNT fun x hx => by
        rw [QuotientGroup.ker_mk']
        exact hNinn hx
  have : Finite (MulAut P) :=
    Finite.of_injective (fun χ : MulAut P => (χ : P → P)) (fun _ _ h => MulEquiv.ext (congrFun h))
  have hπF : ∀ τ ∈ Fld, π τ = 1 → τ = 1 := by
    let πF : Fld →* Fld.map π :=
      (π.comp Fld.subtype).codRestrict _ fun x => mem_map_of_mem π x.2
    have hsF : Function.Surjective πF := by
      rintro ⟨_, ⟨τ, hτ, rfl⟩⟩
      exact ⟨⟨τ, hτ⟩, rfl⟩
    have hbij := (Nat.bijective_iff_surjective_and_card πF).mpr ⟨hsF, hFinj⟩
    intro τ hτ h1
    have h2 : πF ⟨τ, hτ⟩ = πF 1 := Subtype.ext (by rw [map_one]; exact h1)
    exact congrArg Subtype.val (hbij.1 h2)
  have hNTn : (Nt.subgroupOf Tt).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    rw [← hinnN] at hx ⊢
    exact mem_inf.mpr ⟨mul_mem (mul_mem g.2.1 hx.1) (inv_mem g.2.1),
      hinnormal.conj_mem _ hx.2 _⟩⟩
  have hTMn : (Tt.subgroupOf Mt).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    refine mem_inf.mpr ⟨mul_mem (mul_mem g.2 hx.1) (inv_mem g.2), ?_⟩
    rw [mem_comap, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    exact hRn.conj_mem _ hx.2 _⟩
  have hTF : Tt ⊓ Fld = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxT, hxF⟩ := mem_inf.mp hx
    have h1 : π x ∈ R ⊓ Fld.map π := mem_inf.mpr ⟨hxT.2, mem_map_of_mem π hxF⟩
    rw [disjoint_iff.mp hRF.disjoint, mem_bot] at h1
    rw [mem_bot]
    exact hπF x hxF h1
  refine ⟨fun β => mem_centralizer_conj_iff hZ β t, hinnN, hsurj, hker, hNT, hNTn, hTMn,
    hTmap, hTker, hTF, fun β hβ => ?_⟩
  obtain ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hrs, -⟩ := hRF.existsUnique (π β)
  obtain ⟨τ, hτ, rfl⟩ := hs
  have hv : β * τ⁻¹ ∈ Tt := by
    refine mem_inf.mpr ⟨mul_mem hβ (inv_mem (hFM hτ)), ?_⟩
    rw [mem_comap, map_mul, map_inv, ← hrs, mul_inv_cancel_right]
    exact hr
  refine ⟨(⟨β * τ⁻¹, hv⟩, ⟨τ, hτ⟩), by simp, ?_⟩
  rintro ⟨⟨v', hv'⟩, ⟨τ', hτ'⟩⟩ h
  have h1 : (v' : MulAut P) * τ' = β := h
  have h2 : (β * τ⁻¹)⁻¹ * v' = τ * τ'⁻¹ := by
    rw [← h1]
    group
  have h3 : τ * τ'⁻¹ ∈ Tt ⊓ Fld := mem_inf.mpr ⟨h2 ▸ mul_mem (inv_mem hv) hv',
    mul_mem hτ (inv_mem hτ')⟩
  rw [hTF, mem_bot, mul_inv_eq_one] at h3
  subst h3
  have h4 : v' = β * τ⁻¹ := by
    rw [← h1]
    group
  subst h4
  rfl

end Outer

theorem socle_outer_restrict {A P : Type*} [Group A] [Group P] {W : Subgroup A} {a : A}
    {ρ : A →* MulAut P} (hinj : Function.Injective ρ)
    (hW : W.map ρ = OuterAutomorphisms.inner P) (hZ : center P = ⊥) {z : P}
    (hz2 : orderOf z = 2) (hfus : ∀ x : P, orderOf x = 2 → ∃ y : P, y * x * y⁻¹ = z)
    (hρz : ρ a = MulAut.conj z) :
    ((centralizer {a}).map ρ).map (QuotientGroup.mk' (OuterAutomorphisms.inner P)) =
        ρ.range.map (QuotientGroup.mk' (OuterAutomorphisms.inner P)) ∧
      (centralizer {a}).map ρ ⊓ (QuotientGroup.mk' (OuterAutomorphisms.inner P)).ker =
        (W ⊓ centralizer {a}).map ρ := by
  have hconj := conj_injective_of_center_eq_bot hZ
  have hWle : OuterAutomorphisms.inner P ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  obtain ⟨hπs, hπk⟩ := map_inf_centralizer_conj hZ hfus hz2 hWle
  have hCAz : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {MulAut.conj z} := by
    rw [hCAimg, hρz]
  have hCWz : (W ⊓ centralizer {a}).map ρ = (centralizer {z}).map MulAut.conj := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle, hρz,
      SymmetricLocal.map_centralizer_singleton_of_injective _ hconj z]
    rfl
  exact ⟨by rw [hCAz, hπs], by rw [hCAz, hπk, hCWz]⟩

theorem socle_conj_component {A P : Type*} [Group A] [Group P] [Finite P] {W : Subgroup A}
    {a : A} {L : Subgroup A} (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    {ρ : A →* MulAut P} (hinj : Function.Injective ρ)
    (hW : W.map ρ = OuterAutomorphisms.inner P) (hZ : center P = ⊥) {t : P} {B : Subgroup P}
    (hIDP : CFSG.Walter.JT.IsInternalDirectProduct (zpowers t) B (centralizer {t}))
    (hBs : IsSimpleGroup B) (hBnab : ∃ x y : B, x * y ≠ y * x) {g : P}
    (hρa : ρ a = MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹) :
    (centralizer {a}).map ρ = ρ.range ⊓
        (centralizer {MulAut.conj t}).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      (W ⊓ centralizer {a}).map ρ =
        ((centralizer {t}).map MulAut.conj).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      L.map ρ = (B.map MulAut.conj).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      ∃ θ : L ≃* B, ∀ l : L,
        MulAut.conj (θ l : P) = (MulAut.conj g)⁻¹ * ρ l * MulAut.conj g := by
  have hconj := conj_injective_of_center_eq_bot hZ
  obtain ⟨χ, hχ⟩ : ∃ χ : MulAut P, χ = MulAut.conj g := ⟨_, rfl⟩
  rw [← hχ] at hρa ⊢
  have hWle : OuterAutomorphisms.inner P ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner P ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hNt : OuterAutomorphisms.inner P ⊓ centralizer {MulAut.conj t} =
      (centralizer {t}).map MulAut.conj := by
    rw [SymmetricLocal.map_centralizer_singleton_of_injective _ hconj t]
    rfl
  have hCA' : (centralizer {a}).map ρ = ρ.range ⊓
      (centralizer {MulAut.conj t}).map (MulAut.conj χ).toMonoidHom := by
    rw [hCAimg, hρa, map_conj_centralizer_singleton']
  have hCW' : (W ⊓ centralizer {a}).map ρ =
      ((centralizer {t}).map MulAut.conj).map (MulAut.conj χ).toMonoidHom := by
    rw [hCWimg, hρa, ← map_conj_inner_inf_centralizer, hNt]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (((centralizer {t}).map MulAut.conj).map (MulAut.conj χ).toMonoidHom) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCW'] at this
  have hid : (MulAut.conj χ⁻¹).toMonoidHom.comp (MulAut.conj χ).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hid' : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : Subgroup (MulAut P),
      L₀ = (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ ((centralizer {t}).map MulAut.conj) := by
    have := LocalAnalysis.ComponentInitial.isComponentOf_map_conj hL₁ χ⁻¹
    rwa [Subgroup.map_map _ (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj χ).toMonoidHom, hid,
      Subgroup.map_id, ← hL₀def] at this
  have hsupN : (centralizer {t}).map MulAut.conj =
      zpowers (MulAut.conj t) ⊔ B.map MulAut.conj := by
    rw [← hIDP.1, Subgroup.map_sup, MonoidHom.map_zpowers]
  have : Finite (MulAut P) :=
    Finite.of_injective (fun χ : MulAut P => (χ : P → P)) (fun _ _ h => MulEquiv.ext (congrFun h))
  have htB : zpowers (MulAut.conj t) ≤
      centralizer ((B.map MulAut.conj : Subgroup (MulAut P)) : Set (MulAut P)) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h1 := mem_centralizer_iff.mp (hIDP.2.2 (mem_zpowers t)) b hb
    rw [← map_mul, h1, map_mul]
  have hBs' : IsSimpleGroup (B.map MulAut.conj) :=
    (B.equivMapOfInjective _ hconj).symm.isSimpleGroup
  have hBnab' : ∃ x y : B.map MulAut.conj, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hBnab
    refine ⟨B.equivMapOfInjective _ hconj x, B.equivMapOfInjective _ hconj y, fun h => hxy ?_⟩
    apply (B.equivMapOfInjective _ hconj).injective
    rw [map_mul, map_mul, h]
  have hL₀' : CFSG.Assembly.IsComponentOf L₀ (zpowers (MulAut.conj t) ⊔ B.map MulAut.conj) := by
    rw [← hsupN]
    exact hL₀
  have hL₀eq : L₀ = B.map MulAut.conj := eq_of_isComponentOf_sup_zpowers htB hBs' hBnab' hL₀'
  have hLimg : L.map ρ = (B.map MulAut.conj).map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, Subgroup.map_map _ (MulAut.conj χ).toMonoidHom
      (MulAut.conj χ⁻¹).toMonoidHom, hid', Subgroup.map_id]
  rw [hL₀def] at hL₀eq
  let e₄ := B.equivMapOfInjective _ hconj
  let θ : L ≃* B := ((L.equivMapOfInjective ρ hinj).trans
    (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective).trans
      (MulEquiv.subgroupCongr hL₀eq))).trans e₄.symm
  refine ⟨hCA', hCW', hLimg, θ, fun l => ?_⟩
  have h1 : (e₄ (θ l) : MulAut P) = MulAut.conj (θ l : P) := rfl
  have h2 : e₄ (θ l) = MulEquiv.subgroupCongr hL₀eq
      (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective)
        (L.equivMapOfInjective ρ hinj l)) := e₄.apply_symm_apply _
  rw [← h1, h2]
  change MulAut.conj χ⁻¹ (ρ l) = _
  rw [MulAut.conj_apply, inv_inv]

end CFSG.ComponentClassification.OutcomeLocal
