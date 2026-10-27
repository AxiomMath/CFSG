module

public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.DDLocal
import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer
import CFSG.LocalAnalysis.GH72.Sec2

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn isElemAbelian_two_iff comm_of_mul_self)

section Generic

variable {G : Type*} [Group G]

theorem IsDih.exists_four_mem_of_comm {D : Subgroup G} (hD : IsDih D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) :
    ∃ V, IsFourIn D V ∧ a ∈ V ∧ b ∈ V := by
  by_cases hca : ∃ y ∈ D, y * a ≠ a * y
  · exact ⟨D ⊓ C a, hD.isFourIn_inf_centralizer ha ha2 hca,
      mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 rfl⟩,
      mem_inf.2 ⟨hb, mem_centralizer_singleton_iff.2 hab.symm⟩⟩
  by_cases hcb : ∃ y ∈ D, y * b ≠ b * y
  · exact ⟨D ⊓ C b, hD.isFourIn_inf_centralizer hb hb2 hcb,
      mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 hab⟩,
      mem_inf.2 ⟨hb, mem_centralizer_singleton_iff.2 rfl⟩⟩
  push Not at hca hcb
  obtain ⟨V, hV⟩ := hD.exists_four
  exact ⟨V, hV, hD.mem_four_of_central hV ha hca, hD.mem_four_of_central hV hb hcb⟩

variable [Finite G]

theorem exists_conj_mem_of_thompson_of_min_order {K T U : Subgroup G} (hT : IsSylowOf 2 T K)
    (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T) (hxU : x ∉ U)
    (hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y)
    (hno : ∀ N : Subgroup ↥K, N.Normal → N.index ≠ 2) :
    ∃ k ∈ K, k * x * k⁻¹ ∈ U ∧ ∀ c ∈ T ⊓ C x, k * c * k⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : T ≤ K := hT.le
  obtain ⟨-, hTp, hTidx⟩ := isSylowOf_iff.1 hT
  let x' : K := ⟨x, hTK hxT⟩
  have hT'p : IsPGroup 2 (T.subgroupOf K) := hTp.comap_subtype
  have hU'T' : U.subgroupOf K ≤ T.subgroupOf K := fun u hu => hUT hu
  have hU'idx : (U.subgroupOf K).relIndex (T.subgroupOf K) = 2 := by
    rw [relIndex_subgroupOf hTK]
    exact hUidx
  have hmin' : ∀ y ∈ T.subgroupOf K, y ∉ U.subgroupOf K → orderOf x' ≤ orderOf y := by
    intro y hyT hyU
    rw [Subgroup.orderOf_mk (H := K) x (hTK hxT),
      Subgroup.orderOf_mk (H := K) (y : K) y.2]
    exact hmin (y : K) (Subgroup.mem_subgroupOf.mp hyT)
      (fun hy => hyU (Subgroup.mem_subgroupOf.mpr hy))
  obtain ⟨g, hgU, hgext⟩ := CFSG.EvenSporTransfer.exists_extremal_conj_of_thompson hT'p hTidx
    hU'T' hU'idx (x := x') hxT hxU hmin' hno
  have hext : IsSylowOf 2 (T.subgroupOf K ⊓ centralizer {g⁻¹ * x' * g})
      (centralizer {g⁻¹ * x' * g}) := isSylowOf_iff.2 hgext
  have hQC : (T.subgroupOf K ⊓ centralizer {x'}).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer {g⁻¹ * x' * g} := by
    rintro _ ⟨d, hd, rfl⟩
    have hdc := mem_centralizer_singleton_iff.1 (mem_inf.1 hd).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * d * g⁻¹⁻¹ * (g⁻¹ * x' * g) = g⁻¹ * (d * x') * g := by group
      _ = g⁻¹ * (x' * d) * g := by rw [hdc]
      _ = g⁻¹ * x' * g * (g⁻¹ * d * g⁻¹⁻¹) := by group
  have hQp : IsPGroup 2 ((T.subgroupOf K ⊓ centralizer {x'}).map (MulAut.conj g⁻¹).toMonoidHom) :=
    hT'p.to_inf_left.map _
  obtain ⟨c, hcC, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hext hQC hQp
  have hcv : c * (g⁻¹ * x' * g) * c⁻¹ = g⁻¹ * x' * g := by
    have h := mem_centralizer_singleton_iff.1 hcC
    calc c * (g⁻¹ * x' * g) * c⁻¹ = g⁻¹ * x' * g * c * c⁻¹ := by rw [h]
      _ = g⁻¹ * x' * g := by group
  refine ⟨((c * g⁻¹ : K) : G), (c * g⁻¹).2, ?_, ?_⟩
  · have e : (c * g⁻¹) * x' * (c * g⁻¹)⁻¹ = g⁻¹ * x' * g := by
      rw [← hcv]
      group
    have h : (((c * g⁻¹) * x' * (c * g⁻¹)⁻¹ : K) : G) ∈ U := by
      rw [e]
      exact hgU
    simpa using h
  · intro d hd
    obtain ⟨hdT, hdC⟩ := mem_inf.1 hd
    let d' : K := ⟨d, hTK hdT⟩
    have hd' : d' ∈ T.subgroupOf K ⊓ centralizer {x'} := by
      refine mem_inf.2 ⟨hdT, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hdC)
    have h1 : c * (g⁻¹ * d' * g⁻¹⁻¹) * c⁻¹ ∈ T.subgroupOf K ⊓ centralizer {g⁻¹ * x' * g} :=
      hc ⟨_, ⟨d', hd', rfl⟩, rfl⟩
    have e : c * (g⁻¹ * d' * g⁻¹⁻¹) * c⁻¹ = (c * g⁻¹) * d' * (c * g⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 : (((c * g⁻¹) * d' * (c * g⁻¹)⁻¹ : K) : G) ∈ T := (mem_inf.1 h1).1
    simpa using h2

theorem exists_conj_mem_of_thompson {K T U : Subgroup G} (hT : IsSylowOf 2 T K) (hUT : U ≤ T)
    (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T) (hxU : x ∉ U) (hx2 : orderOf x = 2)
    (hno : ∀ N : Subgroup ↥K, N.Normal → N.index ≠ 2) :
    ∃ k ∈ K, k * x * k⁻¹ ∈ U ∧ ∀ c ∈ T ⊓ C x, k * c * k⁻¹ ∈ T := by
  have hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y := by
    intro y _ hyU
    rw [hx2]
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ one_mem U)
    have h0 := orderOf_pos y
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    omega
  exact exists_conj_mem_of_thompson_of_min_order hT hUT hUidx hxT hxU hmin hno

theorem not_conj_mem_of_normal {D C T W M : Subgroup G} (hCD : C ≤ D) (hT : IsSylowOf 2 T C)
    (hWn : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W) (hWD : W ≤ D) (hDM : D ≤ normalizer (M : Set G))
    (hpow : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ M) {y : G} (hyM : ∀ w ∈ W, y⁻¹ * w ∉ M) {c : G}
    (hc : c ∈ C) : c * y * c⁻¹ ∉ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcW
  have hMn : (M.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hDM (hCD g.2)) n).1 hn⟩
  have h2 : IsPGroup 2 (↥C ⧸ M.subgroupOf C) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow x (hCD x.2)
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]; simpa using hk⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  have hle : C ≤ T ⊔ M := le_sup_of_isSylowOf_of_relIndex hT (k := n) hn
  have hTM : T ≤ normalizer (M : Set G) := (hT.le.trans hCD).trans hDM
  obtain ⟨m, hm, t, ht, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (H := M) (K := T) hTM).1 (sup_comm T M ▸ hle hc)
  have htD : t ∈ D := hCD (hT.le ht)
  have hw' : t⁻¹ * (m * t * y * (m * t)⁻¹) * t⁻¹⁻¹ ∈ W := hWn t⁻¹ (inv_mem ht) _ hcW
  apply hyM _ hw'
  have hwD : m * t * y * (m * t)⁻¹ ∈ D := hWD hcW
  have h1 : (m * t * y * (m * t)⁻¹)⁻¹ * m * (m * t * y * (m * t)⁻¹)⁻¹⁻¹ ∈ M :=
    (mem_normalizer_iff.1 (hDM (inv_mem hwD)) m).1 hm
  have h3 := mul_mem (inv_mem hm) h1
  have h4 := (mem_normalizer_iff.1 (hDM (inv_mem htD)) _).1 h3
  have e : y⁻¹ * (t⁻¹ * (m * t * y * (m * t)⁻¹) * t⁻¹⁻¹) =
      t⁻¹ * (m⁻¹ * ((m * t * y * (m * t)⁻¹)⁻¹ * m * (m * t * y * (m * t)⁻¹)⁻¹⁻¹)) * t⁻¹⁻¹ := by
    group
  rw [e]
  exact h4

theorem exists_normal_of_section {z : G} {P P' : Subgroup G} (hPz : P ≤ C z) (hP : IsPGroup 2 P)
    (hP'z : P' ≤ C z) {Hb : Subgroup (Bar (C z))} (hinf : bar (C z) P ⊓ Hb = ⊥)
    (hsup : bar (C z) P ⊔ Hb = ⊤) (hcomm : Hb ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hP' : bar (C z) P' ≤ Hb) :
    ∃ M : Subgroup G, C z ≤ normalizer (M : Set G) ∧ P' ≤ M ∧ (∀ x ∈ P, x ∈ M → x = 1) ∧
      ∀ x ∈ C z, ∃ k : ℕ, x ^ 2 ^ k ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHbn : Hb.Normal := by
    have hle : bar (C z) P ⊔ Hb ≤ normalizer (Hb : Set (Bar (C z))) := by
      refine sup_le (fun p hp => mem_normalizer_iff.2 fun h => ?_) le_normalizer
      constructor
      · intro hh
        have hph := mem_centralizer_iff.1 (hcomm hh) p hp
        rwa [hph, mul_inv_cancel_right]
      · intro hh
        have hph := mem_centralizer_iff.1 (hcomm hh) p hp
        have e : h = p * h * p⁻¹ := by
          calc h = p⁻¹ * ((p * h * p⁻¹) * p) := by group
            _ = p⁻¹ * (p * (p * h * p⁻¹)) := by rw [hph]
            _ = p * h * p⁻¹ := by group
        rw [e]
        exact hh
    rw [hsup] at hle
    exact normalizer_eq_top_iff.1 (top_le_iff.1 hle)
  haveI := hHbn
  set M := (Hb.comap (QuotientGroup.mk' (CFSG.oddCore (C z)))).map (C z).subtype with hM
  have hmem : ∀ x (hx : x ∈ C z), x ∈ M ↔ (QuotientGroup.mk ⟨x, hx⟩ : Bar (C z)) ∈ Hb := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  refine ⟨M, ?_, fun x hx => (hmem x (hP'z hx)).2 (hP' (mk_mem_bar (hP'z hx) hx)), ?_, ?_⟩
  · haveI := hHbn.comap (QuotientGroup.mk' (CFSG.oddCore (C z)))
    exact le_normalizer_map_subtype (C z) _
  · intro x hxP hxM
    have h2 : (QuotientGroup.mk ⟨x, hPz hxP⟩ : Bar (C z)) ∈ bar (C z) P ⊓ Hb :=
      mem_inf.2 ⟨mk_mem_bar _ hxP, (hmem x (hPz hxP)).1 hxM⟩
    rw [hinf, mem_bot, QuotientGroup.eq_one_iff] at h2
    exact eq_one_of_mem_O_of_isPGroup hP hxP ⟨_, h2, rfl⟩
  · intro x hx
    have hx' : (QuotientGroup.mk ⟨x, hx⟩ : Bar (C z)) ∈ Hb ⊔ bar (C z) P := by
      rw [sup_comm, hsup]
      exact mem_top _
    obtain ⟨h, hh, p, hp, he⟩ := (mem_sup_iff_of_le_normalizer (H := Hb) (K := bar (C z) P)
      (by rw [normalizer_eq_top_iff.2 hHbn]; exact le_top)).1 hx'
    obtain ⟨k, hk⟩ := isPGroup_bar (H := C z) hP ⟨p, hp⟩
    have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, (hmem _ (pow_mem hx _)).2 ?_⟩
    have e : (QuotientGroup.mk ⟨x ^ 2 ^ k, pow_mem hx _⟩ : Bar (C z)) = (h * p) ^ 2 ^ k := by
      rw [← he]
      rfl
    rw [e, ← QuotientGroup.eq_one_iff (N := Hb), QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff h).2 hh, one_mul, ← QuotientGroup.mk_pow, hpk,
      QuotientGroup.mk_one]

end Generic

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem S_le_C_z₂ : (𝔖.S : Subgroup G) ≤ C 𝔖.z₂ := by
  rw [← 𝔖.decomp.sup_eq]
  refine sup_le (fun x hx => ?_) 𝔖.hz₂.2.2
  rw [mem_centralizer_singleton_iff]
  exact 𝔖.decomp.comm hx 𝔖.hz₂.1

theorem S_le_C_z₁z₂ : (𝔖.S : Subgroup G) ≤ C (𝔖.z₁ * 𝔖.z₂) := by
  intro x hx
  have h₁ := mem_centralizer_singleton_iff.1 (𝔖.S_le_C_z₁ hx)
  have h₂ := mem_centralizer_singleton_iff.1 (𝔖.S_le_C_z₂ hx)
  rw [mem_centralizer_singleton_iff]
  calc x * (𝔖.z₁ * 𝔖.z₂) = x * 𝔖.z₁ * 𝔖.z₂ := (mul_assoc _ _ _).symm
    _ = 𝔖.z₁ * x * 𝔖.z₂ := by rw [h₁]
    _ = 𝔖.z₁ * (x * 𝔖.z₂) := mul_assoc _ _ _
    _ = 𝔖.z₁ * (𝔖.z₂ * x) := by rw [h₂]
    _ = 𝔖.z₁ * 𝔖.z₂ * x := (mul_assoc _ _ _).symm

theorem exists_e16_le_of_comm {T : Subgroup G} {V₁ V₂ : Subgroup G} (hV₁ : IsFourIn 𝔖.S₁ V₁)
    (hV₁T : V₁ ≤ T) (hV₂ : IsFourIn 𝔖.S₂ V₂) (hV₂T : V₂ ≤ T) {a b : G}
    (ha : a ∈ (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂)) (hb : b ∈ (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂)) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hab : a * b = b * a) :
    ∃ E, E ≤ (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) ∧ IsE16 E ∧ a ∈ E ∧ b ∈ E := by
  have hd := 𝔖.decomp
  have hc : ∀ x ∈ T ⊓ 𝔖.S₁, ∀ y ∈ T ⊓ 𝔖.S₂, x * y = y * x := fun x hx y hy =>
    hd.comm (mem_inf.1 hx).2 (mem_inf.1 hy).2
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hb
  obtain ⟨ha₁T, ha₁S⟩ := mem_inf.1 ha₁
  obtain ⟨ha₂T, ha₂S⟩ := mem_inf.1 ha₂
  obtain ⟨hb₁T, hb₁S⟩ := mem_inf.1 hb₁
  obtain ⟨hb₂T, hb₂S⟩ := mem_inf.1 hb₂
  obtain ⟨ha₁2, ha₂2⟩ := (hd.mul_self_iff ha₁S ha₂S).1 ha2
  obtain ⟨hb₁2, hb₂2⟩ := (hd.mul_self_iff hb₁S hb₂S).1 hb2
  have hcomm : a₁ * b₁ = b₁ * a₁ ∧ a₂ * b₂ = b₂ * a₂ := by
    refine hd.eq_and_eq (mul_mem ha₁S hb₁S) (mul_mem hb₁S ha₁S) (mul_mem ha₂S hb₂S)
      (mul_mem hb₂S ha₂S) ?_
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [hd.comm hb₁S ha₂S]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
      _ = b₁ * b₂ * (a₁ * a₂) := hab
      _ = b₁ * (b₂ * a₁) * a₂ := by group
      _ = b₁ * (a₁ * b₂) * a₂ := by rw [hd.comm ha₁S hb₂S]
      _ = b₁ * a₁ * (b₂ * a₂) := by group
  have hT₁ : IsDih (T ⊓ 𝔖.S₁) := hd.dih₁.of_le inf_le_right hV₁ (le_inf hV₁T hV₁.1)
  have hT₂ : IsDih (T ⊓ 𝔖.S₂) := hd.isDih₂.of_le inf_le_right hV₂ (le_inf hV₂T hV₂.1)
  obtain ⟨W₁, hW₁, haW₁, hbW₁⟩ := hT₁.exists_four_mem_of_comm ha₁ hb₁ ha₁2 hb₁2 hcomm.1
  obtain ⟨W₂, hW₂, haW₂, hbW₂⟩ := hT₂.exists_four_mem_of_comm ha₂ hb₂ ha₂2 hb₂2 hcomm.2
  have hW₁' : IsFourIn 𝔖.S₁ W₁ := ⟨hW₁.1.trans inf_le_right, hW₁.2⟩
  have hW₂' : IsFourIn 𝔖.S₂ W₂ := ⟨hW₂.1.trans inf_le_right, hW₂.2⟩
  exact ⟨W₁ ⊔ W₂, sup_le_sup hW₁.1 hW₂.1, hd.isE16_sup hW₁' hW₂',
    mul_mem (mem_sup_left haW₁) (mem_sup_right haW₂),
    mul_mem (mem_sup_left hbW₁) (mem_sup_right hbW₂)⟩

theorem conj_mem_inf_sup_inf {T : Subgroup G} (hTS : T ≤ 𝔖.S) {t w : G} (ht : t ∈ T)
    (hw : w ∈ (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂)) : t * w * t⁻¹ ∈ (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) := by
  have hd := 𝔖.decomp
  have hc : ∀ x ∈ T ⊓ 𝔖.S₁, ∀ y ∈ T ⊓ 𝔖.S₂, x * y = y * x := fun x hx y hy =>
    hd.comm (mem_inf.1 hx).2 (mem_inf.1 hy).2
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hw
  have e : t * (w₁ * w₂) * t⁻¹ = (t * w₁ * t⁻¹) * (t * w₂ * t⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨mul_mem (mul_mem ht (mem_inf.1 hw₁).1) (inv_mem ht),
      hd.conj_mem_left (hTS ht) (mem_inf.1 hw₁).2⟩))
    (mem_sup_right (mem_inf.2 ⟨mul_mem (mul_mem ht (mem_inf.1 hw₂).1) (inv_mem ht),
      hd.conj_mem_right (hTS ht) (mem_inf.1 hw₂).2⟩))

theorem eq_inf_sup_inf_of_isSylowOf_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    {K T : Subgroup G} (hno : ∀ N : Subgroup ↥K, N.Normal → N.index ≠ 2)
    (hT : IsSylowOf 2 T K) (hTS : T ≤ 𝔖.S) {V₁ V₂ : Subgroup G} (hV₁ : IsFourIn 𝔖.S₁ V₁)
    (hV₁T : V₁ ≤ T) (hV₂ : IsFourIn 𝔖.S₂ V₂) (hV₂T : V₂ ≤ T) :
    T = (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := 𝔖.decomp
  set W := (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) with hW
  have hc₁₂ : ∀ x ∈ T ⊓ 𝔖.S₁, ∀ y ∈ T ⊓ 𝔖.S₂, x * y = y * x := fun x hx y hy =>
    hd.comm (mem_inf.1 hx).2 (mem_inf.1 hy).2
  have hWT : W ≤ T := sup_le inf_le_left inf_le_left
  by_contra hne
  have hTW : ¬ T ≤ W := fun h => hne (le_antisymm h hWT)
  have hidx : W.relIndex T = 2 := by
    have h1 : W.relIndex T ≤ 2 := hd.relIndex_inf_sup_le_two hTS hV₂ hV₂T
    have h2 : W.relIndex T ≠ 1 := fun h => hTW (relIndex_eq_one.1 h)
    have h3 : W.relIndex T ≠ 0 := by
      intro h0
      have h4 := Subgroup.relIndex_mul_card W T
      rw [h0, zero_mul] at h4
      exact absurd h4.symm Nat.card_pos.ne'
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁T, hy₂T, hy₁2, hy₂2, hyT⟩ :=
    hd.exists_involution_not_mem hTS hV₁ hV₁T hV₂ hV₂T hTW
  have hy2 : y₁ * y₂ * (y₁ * y₂) = 1 := (hd.mul_self_iff hy₁ hy₂).2 ⟨hy₁2, hy₂2⟩
  have hdec : ∀ w ∈ W, ∃ w₁ ∈ T ⊓ 𝔖.S₁, ∃ w₂ ∈ T ⊓ 𝔖.S₂, w = w₁ * w₂ := fun w hw =>
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc₁₂)).1 hw
  have hyW : y₁ * y₂ ∉ W := by
    intro h
    obtain ⟨w₁, hw₁, w₂, hw₂, he⟩ := hdec _ h
    have e := (hd.eq_and_eq hy₁ (mem_inf.1 hw₁).2 hy₂ (mem_inf.1 hw₂).2 he).1
    exact hy₁T (e ▸ (mem_inf.1 hw₁).1)
  have hy1 : y₁ * y₂ ≠ 1 := fun h => hyW (h ▸ one_mem _)
  have hyord : orderOf (y₁ * y₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨k, hkK, hkW, hkT⟩ := exists_conj_mem_of_thompson hT hWT hidx hyT hyW hyord hno
  have hz₁V : 𝔖.z₁ ∈ V₁ := hd.dih₁.mem_four_of_central hV₁ 𝔖.hz₁.1 fun s hs =>
    mem_centralizer_singleton_iff.1 (𝔖.hz₁.2.2 hs)
  have hz₂V : 𝔖.z₂ ∈ V₂ := hd.isDih₂.mem_four_of_central hV₂ 𝔖.hz₂.1 fun s hs =>
    mem_centralizer_singleton_iff.1 (𝔖.hz₂.2.2 hs)
  have hzC : ∀ z, (𝔖.S : Subgroup G) ≤ C z → z ∈ T → z ∈ T ⊓ C (y₁ * y₂) := fun z hSz hzT =>
    mem_inf.2 ⟨hzT, mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (hSz (hTS hyT))).symm⟩
  have hkz₁ : k * 𝔖.z₁ * k⁻¹ ∈ T := hkT _ (hzC _ 𝔖.S_le_C_z₁ (hV₁T hz₁V))
  have hkz₂ : k * 𝔖.z₂ * k⁻¹ ∈ T := hkT _ (hzC _ 𝔖.S_le_C_z₂ (hV₂T hz₂V))
  have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
    have h := pow_orderOf_eq_one x
    rwa [hx, pow_two] at h
  have hz₁2 := hsq _ 𝔖.hz₁.2.1
  have hz₂2 := hsq _ 𝔖.hz₂.2.1
  obtain ⟨z, hz, hzW⟩ : ∃ z, (z = 𝔖.z₁ ∨ z = 𝔖.z₂ ∨ z = 𝔖.z₁ * 𝔖.z₂) ∧ k * z * k⁻¹ ∈ W := by
    by_cases h₁ : k * 𝔖.z₁ * k⁻¹ ∈ W
    · exact ⟨_, Or.inl rfl, h₁⟩
    by_cases h₂ : k * 𝔖.z₂ * k⁻¹ ∈ W
    · exact ⟨_, Or.inr (Or.inl rfl), h₂⟩
    refine ⟨_, Or.inr (Or.inr rfl), ?_⟩
    have h := CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hidx hkz₁ hkz₂ h₁ h₂
    have hz₁inv : 𝔖.z₁⁻¹ = 𝔖.z₁ := inv_eq_of_mul_eq_one_right hz₁2
    have e : (k * 𝔖.z₁ * k⁻¹)⁻¹ * (k * 𝔖.z₂ * k⁻¹) = k * (𝔖.z₁ * 𝔖.z₂) * k⁻¹ := by
      calc (k * 𝔖.z₁ * k⁻¹)⁻¹ * (k * 𝔖.z₂ * k⁻¹) = k * (𝔖.z₁⁻¹ * 𝔖.z₂) * k⁻¹ := by group
        _ = k * (𝔖.z₁ * 𝔖.z₂) * k⁻¹ := by rw [hz₁inv]
    rwa [e] at h
  have hSz : (𝔖.S : Subgroup G) ≤ C z := by
    rcases hz with rfl | rfl | rfl
    exacts [𝔖.S_le_C_z₁, 𝔖.S_le_C_z₂, 𝔖.S_le_C_z₁z₂]
  have hzT : z ∈ T := by
    rcases hz with rfl | rfl | rfl
    exacts [hV₁T hz₁V, hV₂T hz₂V, mul_mem (hV₁T hz₁V) (hV₂T hz₂V)]
  have hz2 : z * z = 1 := by
    rcases hz with rfl | rfl | rfl
    exacts [hz₁2, hz₂2, (hd.mul_self_iff 𝔖.hz₁.1 𝔖.hz₂.1).2 ⟨hz₁2, hz₂2⟩]
  have hconj2 : ∀ x : G, x * x = 1 → k * x * k⁻¹ * (k * x * k⁻¹) = 1 := fun x hx => by
    calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hzy : z * (y₁ * y₂) = y₁ * y₂ * z := (mem_centralizer_singleton_iff.1 (hSz (hTS hyT))).symm
  obtain ⟨E', hE'W, hE', hzE', hyE'⟩ := 𝔖.exists_e16_le_of_comm hV₁ hV₁T hV₂ hV₂T hzW hkW
    (hconj2 _ hz2) (hconj2 _ hy2) (by
      calc k * z * k⁻¹ * (k * (y₁ * y₂) * k⁻¹) = k * (z * (y₁ * y₂)) * k⁻¹ := by group
        _ = k * (y₁ * y₂ * z) * k⁻¹ := by rw [hzy]
        _ = k * (y₁ * y₂) * k⁻¹ * (k * z * k⁻¹) := by group)
  set E := E'.map (MulAut.conj k⁻¹).toMonoidHom with hE
  have hEK : E ≤ K := by
    rintro _ ⟨e, he, rfl⟩
    exact K.mul_mem (K.mul_mem (K.inv_mem hkK) (hT.le (hWT (hE'W he)))) (K.inv_mem (K.inv_mem hkK))
  have hE16 : IsE16 E := hE'.map _ (MulAut.conj k⁻¹).injective
  have hback : ∀ x : G, (MulAut.conj k⁻¹).toMonoidHom (k * x * k⁻¹) = x := fun x => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hzE : z ∈ E := ⟨_, hzE', hback z⟩
  have hyE : y₁ * y₂ ∈ E := ⟨_, hyE', hback _⟩
  have hE2 := isElemAbelian_two_iff.1 hE16.1
  have hEz : E ≤ C z := fun e he => mem_centralizer_singleton_iff.2 (comm_of_mul_self hE2 he hzE)
  have hTC : T ≤ K ⊓ C z := le_inf hT.le (hTS.trans hSz)
  have hTsyl : IsSylowOf 2 T (K ⊓ C z) := hT.of_le hTC inf_le_left
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hE16.2]; norm_num)
  obtain ⟨c, hcC, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hTsyl (le_inf hEK hEz) hEp
  have hyc : c * (y₁ * y₂) * c⁻¹ ∈ T := hc ⟨_, hyE, rfl⟩
  have hle16 : 16 ≤ Nat.card ↥(T ⊓ C (c * (y₁ * y₂) * c⁻¹)) := by
    have hsub : E.map (MulAut.conj c).toMonoidHom ≤ T ⊓ C (c * (y₁ * y₂) * c⁻¹) := by
      refine le_inf hc ?_
      rintro _ ⟨e, he, rfl⟩
      have hey := comm_of_mul_self hE2 he hyE
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * e * c⁻¹ * (c * (y₁ * y₂) * c⁻¹) = c * (e * (y₁ * y₂)) * c⁻¹ := by group
        _ = c * (y₁ * y₂ * e) * c⁻¹ := by rw [hey]
        _ = c * (y₁ * y₂) * c⁻¹ * (c * e * c⁻¹) := by group
    have h := card_le_of_le hsub
    rwa [card_map_of_injective (MulAut.conj c).injective, hE16.2] at h
  obtain ⟨M, hzM, hpowM, hyM⟩ : ∃ M : Subgroup G, C z ≤ normalizer (M : Set G) ∧
      (∀ x ∈ C z, ∃ k : ℕ, x ^ 2 ^ k ∈ M) ∧ ∀ w ∈ W, (y₁ * y₂)⁻¹ * w ∉ M := by
    have hsplit : ∀ w₁ ∈ 𝔖.S₁, ∀ w₂ ∈ 𝔖.S₂,
        (y₁ * y₂)⁻¹ * (w₁ * w₂) = (y₁⁻¹ * w₁) * (y₂⁻¹ * w₂) := fun w₁ hw₁ w₂ hw₂ => by
      have hcm := hd.comm (mul_mem (inv_mem hy₁) hw₁) (inv_mem hy₂)
      calc (y₁ * y₂)⁻¹ * (w₁ * w₂) = y₂⁻¹ * (y₁⁻¹ * w₁) * w₂ := by group
        _ = y₁⁻¹ * w₁ * y₂⁻¹ * w₂ := by rw [← hcm]
        _ = (y₁⁻¹ * w₁) * (y₂⁻¹ * w₂) := by group
    rcases hz with rfl | rfl | rfl
    · obtain ⟨H₁, hinf, hsup, hcomm, hS₂, -⟩ := (h315 _ _ 𝔖.hz₁ 𝔖.hz₂).1
      obtain ⟨M, hMn, hS₂M, hS₁M, hpow⟩ := exists_normal_of_section (z := 𝔖.z₁) 𝔖.hz₁.2.2
        (𝔖.S.isPGroup'.to_le hd.le_left) (hd.le_right.trans 𝔖.S_le_C_z₁) hinf hsup hcomm
        (hS₂.trans (commutator_le.2 fun a ha b hb => mul_mem (mul_mem (mul_mem ha hb)
          (inv_mem ha)) (inv_mem hb)))
      refine ⟨M, hMn, hpow, fun w hw hwM => ?_⟩
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec w hw
      rw [hsplit w₁ (mem_inf.1 hw₁).2 w₂ (mem_inf.1 hw₂).2] at hwM
      have h2 : y₂⁻¹ * w₂ ∈ M := hS₂M (mul_mem (inv_mem hy₂) (mem_inf.1 hw₂).2)
      have h1 : y₁⁻¹ * w₁ ∈ M := by
        have := mul_mem hwM (inv_mem h2)
        rwa [mul_inv_cancel_right] at this
      have h3 := hS₁M _ (mul_mem (inv_mem hy₁) (mem_inf.1 hw₁).2) h1
      exact hy₁T ((inv_mul_eq_one.1 h3) ▸ (mem_inf.1 hw₁).1)
    · obtain ⟨K₁, hinf, hsup, hcomm, hS₁, -⟩ := (h315 _ _ 𝔖.hz₁ 𝔖.hz₂).2
      obtain ⟨M, hMn, hS₁M, hS₂M, hpow⟩ := exists_normal_of_section (z := 𝔖.z₂) 𝔖.hz₂.2.2
        (𝔖.S.isPGroup'.to_le hd.le_right) (hd.le_left.trans 𝔖.S_le_C_z₂) hinf hsup hcomm
        (hS₁.trans (commutator_le.2 fun a ha b hb => mul_mem (mul_mem (mul_mem ha hb)
          (inv_mem ha)) (inv_mem hb)))
      refine ⟨M, hMn, hpow, fun w hw hwM => ?_⟩
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec w hw
      rw [hsplit w₁ (mem_inf.1 hw₁).2 w₂ (mem_inf.1 hw₂).2] at hwM
      have h1 : y₁⁻¹ * w₁ ∈ M := hS₁M (mul_mem (inv_mem hy₁) (mem_inf.1 hw₁).2)
      have h2 : y₂⁻¹ * w₂ ∈ M := by
        have := mul_mem (inv_mem h1) hwM
        rwa [inv_mul_cancel_left] at this
      have h3 := hS₂M _ (mul_mem (inv_mem hy₂) (mem_inf.1 hw₂).2) h2
      exact hy₂T ((inv_mul_eq_one.1 h3) ▸ (mem_inf.1 hw₂).1)
    · obtain ⟨N, hNC, hNn, hNodd, n, hn⟩ := h317 _ _ 𝔖.hz₁ 𝔖.hz₂
      refine ⟨N, (normal_subgroupOf_iff_le_normalizer hNC).1 hNn,
        fun x hx => ⟨n, pow_mem_of_relIndex_eq hNn hn hx⟩, fun w hw hwN => ?_⟩
      have hT2 : IsPGroup 2 T := hT.isPGroup
      have h1 := eq_one_of_mem_of_isPGroup_of_odd hT2 hNodd
        (mul_mem (inv_mem hyT) (hWT hw)) hwN
      exact hyW ((inv_mul_eq_one.1 h1) ▸ hw)
  have hy'W : c * (y₁ * y₂) * c⁻¹ ∉ W :=
    not_conj_mem_of_normal (D := C z) inf_le_right hTsyl (fun t ht w hw =>
      𝔖.conj_mem_inf_sup_inf hTS ht hw) (hWT.trans (hTS.trans hSz)) hzM hpowM hyM hcC
  have hy'2 : c * (y₁ * y₂) * c⁻¹ * (c * (y₁ * y₂) * c⁻¹) = 1 := by
    calc c * (y₁ * y₂) * c⁻¹ * (c * (y₁ * y₂) * c⁻¹) = c * (y₁ * y₂ * (y₁ * y₂)) * c⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have h8 := hd.card_inf_centralizer_of_not_mem hTS hV₁ hV₁T hV₂ hV₂T hyc hy'W hy'2
  omega

end Sec4Setting

end CFSG.GH72
