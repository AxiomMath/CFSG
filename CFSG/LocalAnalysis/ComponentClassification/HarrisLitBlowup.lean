module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement

theorem eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {w y : G} (hw : orderOf w = 2)
    (hy : y ∈ zpowers w) : y = 1 ∨ y = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show k % ((2 : ℕ) : ℤ) = 0 by exact_mod_cast h, zpow_zero]
  · right
    rw [show k % ((2 : ℕ) : ℤ) = 1 by exact_mod_cast h, zpow_one]

theorem isSubnormal_map_of_range_normal {A B : Type*} [Group A] [Group B] (γ : A →* B)
    (hnorm : γ.range.Normal) {J : Subgroup A} (hJ : J.IsSubnormal) : (J.map γ).IsSubnormal := by
  have hle : J.map γ ≤ γ.range := map_le_range γ J
  have h1 : (J.map γ.rangeRestrict).IsSubnormal := IsSubnormal.map γ.rangeRestrict_surjective hJ
  have h2 : (J.map γ).subgroupOf γ.range = J.map γ.rangeRestrict := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, congrArg Subtype.val h⟩
  exact IsSubnormal.trans hle (h2 ▸ h1) hnorm.isSubnormal

theorem isPComponent_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {L : Subgroup A} (hL : IsPComponent 2 L) :
    IsPComponent 2 (L.map e.toMonoidHom) := by
  obtain ⟨hsub, hq⟩ := (isTwoComponent_iff_isPComponent L).mpr hL
  exact (isTwoComponent_iff_isPComponent _).mp ⟨IsSubnormal.map e.surjective hsub,
    isTwoQuasisimple_of_mulEquiv (L.equivMapOfInjective _ e.injective) hq⟩

theorem isBlowup_of_mulEquiv {X X' Y : Type} [Group X] [Group X'] [Group Y] (e : X ≃* X')
    (h : IsBlowup X Y) : IsBlowup X' Y := by
  obtain ⟨hfin, hsimp, α, hα, L, hL, ⟨eL⟩⟩ := h
  have : Finite X := hfin
  have : Finite X' := Finite.of_equiv X e.toEquiv
  have hfix : fixedPoints (MulAut.congr e α) = (fixedPoints α).map e.toMonoidHom := by
    ext x
    rw [mem_fixedPoints, mem_map]
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [mem_fixedPoints]
      have h1 : e (α (e.symm x)) = x := hx
      simpa using congrArg e.symm h1
    · rintro ⟨y, hy, rfl⟩
      rw [mem_fixedPoints] at hy
      show e (α (e.symm (e y))) = e y
      rw [MulEquiv.symm_apply_apply, hy]
  let eF : ↥(fixedPoints α) ≃* ↥(fixedPoints (MulAut.congr e α)) :=
    ((fixedPoints α).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  refine ⟨this, e.symm.isSimpleGroup, MulAut.congr e α, by rw [MulEquiv.orderOf_eq]; exact hα,
    L.map eF.toMonoidHom, isPComponent_map_mulEquiv eF hL, ?_⟩
  obtain ⟨e'⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv
    (L.equivMapOfInjective eF.toMonoidHom eF.injective)
  exact ⟨e'.symm.trans eL⟩

theorem inClosure_of_mulEquiv {F : (Y : Type) → [Group Y] → Prop}
    (hF : ∀ (A B : Type) [Group A] [Group B], (A ≃* B) → F A → F B) {X X' : Type} [Group X]
    [Group X'] (e : X ≃* X') (h : InClosure F X) : InClosure F X' := by
  cases h with
  | base hFX => exact .base (hF _ _ e hFX)
  | blowup hY hcat hblow =>
    exact .blowup hY (SectionRank.catalog_of_mulEquiv e.symm hcat) (isBlowup_of_mulEquiv e hblow)

theorem harrisF_of_mulEquiv {p : ℕ} {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : HarrisF p X) : HarrisF p X' :=
  inClosure_of_mulEquiv
    (fun _ _ _ _ e ⟨n, hn, hm⟩ => ⟨n, hn, GSThmB.OddQuot.lieModel_of_equiv e hm⟩) e h

section QuotCenter

variable {G : Type} [Group G] (E : Subgroup G) [E.Normal]

omit [E.Normal] in
theorem map_center_mulAut (σ : MulAut ↥E) : (center ↥E).map σ.toMonoidHom = center ↥E :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance σ

@[expose] def quotCenterConj (τ : G) : MulAut (↥E ⧸ center ↥E) :=
  QuotientGroup.congr (center ↥E) (center ↥E) (MulAut.conjNormal τ) (map_center_mulAut E _)

theorem quotCenterConj_mk (τ : G) (x : ↥E) :
    quotCenterConj E τ (x : ↥E ⧸ center ↥E) = ((MulAut.conjNormal τ x : ↥E) : ↥E ⧸ center ↥E) :=
  QuotientGroup.congr_mk _ _ _ _ x

variable {E}

@[expose] def toFixedQuot {τ : G} {K : Subgroup G} (hKE : K ≤ E ⊓ centralizer ({τ} : Set G)) :
    ↥K →* ↥(fixedPoints (quotCenterConj E τ)) :=
  ((QuotientGroup.mk' (center ↥E)).comp (Subgroup.inclusion (hKE.trans inf_le_left))).codRestrict
    _ fun k => by
      rw [mem_fixedPoints, MonoidHom.comp_apply, QuotientGroup.mk'_apply, quotCenterConj_mk]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hk : (k : G) * τ = τ * k := mem_centralizer_singleton_iff.mp (hKE k.2).2
      show τ * (k : G) * τ⁻¹ = k
      rw [← hk, mul_inv_cancel_right]

theorem toFixedQuot_apply {τ : G} {K : Subgroup G} (hKE : K ≤ E ⊓ centralizer ({τ} : Set G))
    (k : ↥K) : ((toFixedQuot hKE k : ↥(fixedPoints (quotCenterConj E τ))) : ↥E ⧸ center ↥E) =
      ((⟨k, (hKE k.2).1⟩ : ↥E) : ↥E ⧸ center ↥E) :=
  rfl

theorem toFixedQuot_injective [Finite G] (hZ : IsPGroup 2 ↥(center ↥E)) {τ : G} {K : Subgroup G}
    (hKE : K ≤ E ⊓ centralizer ({τ} : Set G)) (hKZ : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥) :
    Function.Injective (toFixedQuot hKE) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have h1 : ((⟨k, (hKE k.2).1⟩ : ↥E) : ↥E ⧸ center ↥E) = 1 := congrArg Subtype.val hk
  rw [QuotientGroup.eq_one_iff] at h1
  have hkc : (QuotientGroup.mk k : ↥K ⧸ pPrimeCore 2 ↥K) ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have h' := congrArg Subtype.val (mem_center_iff.mp h1 ⟨g, (hKE g.2).1⟩)
    exact h'
  rw [hKZ, mem_bot, QuotientGroup.eq_one_iff] at hkc
  have hodd := Subgroup.orderOf_dvd_natCard _ hkc
  obtain ⟨n, hn⟩ := hZ ⟨_, h1⟩
  have h2 : k ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg (fun y : ↥(center ↥E) => ((y : ↥E) : G)) hn
    simpa using this
  have h3 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
  rcases m with _ | m
  · rw [pow_zero, orderOf_eq_one_iff] at hm
    rw [hm]
    exact one_mem _
  · rw [hm, pow_succ] at hodd
    exact absurd (Nat.Coprime.coprime_dvd_right (dvd_trans (dvd_mul_left 2 _) hodd) hcop)
      (by norm_num)

theorem range_toFixedQuot_normal {τ : G} :
    (toFixedQuot (le_refl (E ⊓ centralizer ({τ} : Set G)))).range.Normal := by
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (f : ↥E ⧸ center ↥E)
  have hf : quotCenterConj E τ (x : ↥E ⧸ center ↥E) = x := by
    rw [hx]
    exact f.2
  rw [quotCenterConj_mk, QuotientGroup.eq] at hf
  set z := (MulAut.conjNormal τ x)⁻¹ * x with hz
  have hzG : (z : G) = (τ * x * τ⁻¹)⁻¹ * x := by
    rw [hz, coe_mul, coe_inv, MulAut.conjNormal_apply]
  have hcτ : (c : G) * τ = τ * c := mem_centralizer_singleton_iff.mp c.2.2
  have hzcG : (c : G) * z = z * c := congrArg Subtype.val (mem_center_iff.mp hf ⟨c, c.2.1⟩)
  have h1 : τ * (x : G) = x * (z : G)⁻¹ * τ := by
    rw [hzG]
    group
  have h2 : τ * (x : G)⁻¹ = z * (x : G)⁻¹ * τ := by
    rw [hzG]
    group
  have hmem : (x : G) * c * (x : G)⁻¹ ∈ E ⊓ centralizer ({τ} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem x.2 (Subgroup.mem_inf.mp c.2).1)
      (inv_mem x.2), ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * c * (x : G)⁻¹ * τ = (x : G) * (z : G)⁻¹ * ((c : G) * z) * (x : G)⁻¹ * τ := by
          rw [hzcG]
          group
      _ = (x : G) * (z : G)⁻¹ * c * (τ * (x : G)⁻¹) := by
          rw [h2]
          group
      _ = (x : G) * (z : G)⁻¹ * ((c : G) * τ) * (x : G)⁻¹ := by group
      _ = (x : G) * (z : G)⁻¹ * (τ * c) * (x : G)⁻¹ := by rw [hcτ]
      _ = τ * ((x : G) * c * (x : G)⁻¹) := by
          rw [show (x : G) * (z : G)⁻¹ * (τ * c) * (x : G)⁻¹ =
            ((x : G) * (z : G)⁻¹ * τ) * c * (x : G)⁻¹ by group, ← h1]
          group
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [toFixedQuot_apply, coe_mul, coe_mul, coe_inv, ← hx, toFixedQuot_apply,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

end QuotCenter

section Blowup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} [E.Normal]

omit [Finite G] in
theorem isSubnormal_range_toFixedQuot {τ : G} {K : Subgroup G}
    (hK : IsTwoComponentIn K (E ⊓ centralizer {τ})) : (toFixedQuot hK.1).range.IsSubnormal := by
  have hcomp : toFixedQuot hK.1 =
      (toFixedQuot (le_refl (E ⊓ centralizer ({τ} : Set G)))).comp (Subgroup.inclusion hK.1) :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact isSubnormal_map_of_range_normal _ range_toFixedQuot_normal hK.2.1

theorem isPComponent_range_toFixedQuot (hZ : IsPGroup 2 ↥(center ↥E)) {τ : G} {K : Subgroup G}
    (hK : IsTwoComponentIn K (E ⊓ centralizer {τ})) (hKZ : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥) :
    IsPComponent 2 (toFixedQuot hK.1).range :=
  (isTwoComponent_iff_isPComponent _).mp ⟨isSubnormal_range_toFixedQuot hK,
    isTwoQuasisimple_of_mulEquiv (MonoidHom.ofInjective (toFixedQuot_injective hZ hK.1 hKZ))
      hK.2.2⟩

omit [Finite G] in
theorem orderOf_quotCenterConj (hE : IsQuasisimple ↥E) {τ : G} (hτ : orderOf τ = 2)
    (hτE : ⁅E, zpowers τ⁆ = E) : orderOf (quotCenterConj E τ) = 2 := by
  have hτ2 : τ ^ 2 = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ] at this
  refine orderOf_eq_prime ?_ ?_
  · ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [sq, MulAut.mul_apply, quotCenterConj_mk, quotCenterConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    calc τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = (τ * τ) * x * (τ * τ)⁻¹ := by group
      _ = x := by rw [← sq, hτ2]; group
  · intro h1
    have hle : ⁅E, zpowers τ⁆ ≤ (center ↥E).map E.subtype := by
      rw [commutator_le]
      intro x hx y hy
      rcases eq_one_or_eq_of_mem_zpowers_two hτ hy with hy1 | hyτ
      · rw [hy1, commutatorElement_one_right]
        exact one_mem _
      · rw [hyτ]
        have h2 : quotCenterConj E τ ((⟨x, hx⟩ : ↥E) : ↥E ⧸ center ↥E) =
            ((⟨x, hx⟩ : ↥E) : ↥E ⧸ center ↥E) := by
          rw [h1]
          rfl
        rw [quotCenterConj_mk, QuotientGroup.eq] at h2
        refine ⟨_, h2, ?_⟩
        have hwx := congrArg Subtype.val (mem_center_iff.mp h2 ⟨x, hx⟩)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at hwx ⊢
        rw [commutatorElement_def]
        calc (τ * x * τ⁻¹)⁻¹ * x = x * ((τ * x * τ⁻¹)⁻¹ * x) * x⁻¹ := by
              rw [hwx]
              group
          _ = x * τ * x⁻¹ * τ⁻¹ := by group
    rw [hτE] at hle
    have hEZ : ∀ x : ↥E, x ∈ center ↥E := by
      intro x
      obtain ⟨w, hw, hwx⟩ := hle x.2
      have hw' : w = x := Subtype.ext hwx
      rw [← hw']
      exact hw
    obtain ⟨a, b, hab⟩ := hE.2.2
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [(QuotientGroup.eq_one_iff a).mpr (hEZ a), (QuotientGroup.eq_one_iff b).mpr (hEZ b)]

theorem isBlowup_quotient_center (hE : IsQuasisimple ↥E) (hZ : IsPGroup 2 ↥(center ↥E)) {τ : G}
    (hτ : orderOf τ = 2) (hτE : ⁅E, zpowers τ⁆ = E) {K : Subgroup G}
    (hK : IsTwoComponentIn K (E ⊓ centralizer {τ})) (hKZ : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥)
    {Y : Type} [Group Y] (hY : Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* Y)) :
    IsBlowup (↥E ⧸ center ↥E) Y := by
  obtain ⟨eY⟩ := hY
  obtain ⟨e'⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv
    (MonoidHom.ofInjective (toFixedQuot_injective hZ hK.1 hKZ))
  exact ⟨inferInstance, hE.2.1, quotCenterConj E τ, orderOf_quotCenterConj hE hτ hτE,
    (toFixedQuot hK.1).range, isPComponent_range_toFixedQuot hZ hK hKZ, ⟨e'.symm.trans eY⟩⟩

end Blowup

end CFSG.ComponentClassification.HarrisLit
