module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallShape
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

theorem map_centralizer_mulEquiv {T P : Type} [Group T] [Group P] (e : T ≃* P) (z : T) :
    (Subgroup.centralizer ({e z} : Set P)).map e.symm.toMonoidHom =
      Subgroup.centralizer ({z} : Set T) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := congrArg e.symm hy
    simpa using this
  · intro hx
    refine ⟨e x, ?_, by simp⟩
    have := congrArg e hx
    simpa using this

theorem map_centralizer_subtype {Y : Type} [Group Y] (T : Subgroup Y) (z : ↥T) :
    (Subgroup.centralizer ({z} : Set ↥T)).map T.subtype =
      Subgroup.centralizer ({(z : Y)} : Set Y) ⊓ T := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨congrArg Subtype.val hx, x.2⟩
  · rintro ⟨hy, hyT⟩
    exact ⟨⟨y, hyT⟩, Subtype.ext hy, rfl⟩

theorem isSubnormal_inf_normal {Y : Type} [Group Y] (C T : Subgroup Y) [T.Normal] :
    CFSG.Open.IsSubnormal (C ⊓ T) C := by
  refine CFSG.Open.IsSubnormal.step inf_le_left ?_ (CFSG.Open.IsSubnormal.refl C)
  rw [Subgroup.normal_subgroupOf_iff inf_le_left]
  intro x k hx hk
  exact ⟨C.mul_mem (C.mul_mem hk hx.1) (C.inv_mem hk),
    (inferInstance : T.Normal).conj_mem x hx.2 k⟩

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))


theorem twin_exists_q8 {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (h : PerpHypR r n Y R S t) :
    ∃ φ : QuaternionGroup 2 →* Y, Function.Injective φ ∧ (∀ x, φ x ∈ tightCore R) := by
  obtain ⟨e⟩ := h.core.quat
  obtain ⟨r', hr', ⟨e'⟩⟩ := h.core.datum.quat
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨r', hr', ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans e'⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_q8Pair hQ
  have hS'K : S' ≤ tightCore R := h.core.datum.sylow_core.1
  exact ⟨q8Hom hpq, q8Hom_injective hpq, fun x => hS'K (q8Hom_mem hpq hp hq x)⟩

theorem twin_mem_of_mem_of_ne_one {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {N : Subgroup Y} {x : Y}
    (hxK : x ∈ tightCore R) (hxN : x ∈ N) {k : ℕ} (hx : x ^ 2 ^ k = 1) (hx1 : x ≠ 1) : t ∈ N := by
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hx1
    · exact h'
  have hy : orderOf (x ^ 2 ^ (m - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)), hm,
      Nat.pow_div (Nat.sub_le m 1) two_pos]
    have : m - (m - 1) = 1 := by omega
    rw [this, pow_one]
  have hy1 : x ^ 2 ^ (m - 1) ≠ 1 := fun h' => by
    rw [h', orderOf_one] at hy
    omega
  have hyK : x ^ 2 ^ (m - 1) ∈ tightCore R := (tightCore R).pow_mem hxK _
  have hy2 : (x ^ 2 ^ (m - 1)) * (x ^ 2 ^ (m - 1)) = 1 := by
    have := pow_orderOf_eq_one (x ^ 2 ^ (m - 1))
    rwa [hy, pow_two] at this
  have hyt : x ^ 2 ^ (m - 1) = t := (hz.unique _ hyK hy2).resolve_left hy1
  rw [← hyt]
  exact N.pow_mem hxN _

theorem twin_mem_of_noQ8Outer {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥)
    (hO : ∀ φ : QuaternionGroup 2 →* Outer N, ¬ Function.Injective φ) : t ∈ N := by
  by_contra htN
  obtain ⟨φ, hφ, hφK⟩ := twin_exists_q8 h
  apply hO ((outerHom N).comp φ)
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hxN : φ x ∈ N := (outerHom_eq_one_iff hC).mp hx
  have hφx : φ x ≠ 1 := fun h' => hx1 (hφ (h'.trans (map_one φ).symm))
  have h8' : x ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_q8_dvd x)
  have h8 : φ x ^ 2 ^ 3 = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ 3 = 8 by norm_num, h8', map_one]
  exact htN (twin_mem_of_mem_of_ne_one h (hφK x) hxN h8 hφx)

theorem twin_false_of_model {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) (H₁ H₂ : Subgroup P)
    (hK₁ : CFSG.Open.IsComponentOf H₁ (Subgroup.centralizer ({u} : Set P)))
    (hK₂ : CFSG.Open.IsComponentOf H₂ (Subgroup.centralizer ({u} : Set P)))
    (hA : NoQ8Fix P (H₁ ⊔ H₂)) : False := by
  have hq₁ : CFSG.IsQuasisimple ↥H₁ := isQuasisimple_of_open hK₁.2.2
  have hq₂ : CFSG.IsQuasisimple ↥H₂ := isQuasisimple_of_open hK₂.2.2
  have hs₁ := hK₁.2.1
  have hs₂ := hK₂.2.1
  haveI hsimple := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hRsolv : Group.IsSolvable ↥R := isSolvable_of_quotient_twoGroup h.core.datum.twoGroup
  have hK₀solv : Group.IsSolvable ↥(tightCore R) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (tightCore_le R))
  have hsubK : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hΩ (CoreAssembly.mem_conjClass_self _) hz
  have hcomp : ∀ H : Subgroup P, CFSG.IsQuasisimple ↥H →
      CFSG.Open.IsSubnormal H (Subgroup.centralizer ({u} : Set P)) →
      CFSG.IsQuasisimple ↥((H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype) ∧
        CFSG.Open.IsSubnormal ((H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype)
          (Subgroup.centralizer ({t} : Set Y)) := by
    intro H hq hs
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective H e.symm.toMonoidHom e.symm.injective).trans
        (Subgroup.equivMapOfInjective _ (genFittingFStar Y).subtype
          (genFittingFStar Y).subtype_injective)) hq, ?_⟩
    have h1 := (hs.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype
    rw [← hu, map_centralizer_mulEquiv e ⟨t, htT⟩,
      map_centralizer_subtype (genFittingFStar Y) ⟨t, htT⟩] at h1
    exact h1.trans (isSubnormal_inf_normal _ (genFittingFStar Y))
  obtain ⟨hq₁', hs₁'⟩ := hcomp H₁ hq₁ hs₁
  obtain ⟨hq₂', hs₂'⟩ := hcomp H₂ hq₂ hs₂
  have hc₁ := commute_of_solvable_subnormal hs₁' hq₁' hsubK hK₀solv
  have hc₂ := commute_of_solvable_subnormal hs₂' hq₂' hsubK hK₀solv
  obtain ⟨φ, hφi, hφK⟩ := twin_exists_q8 h
  let ψ : QuaternionGroup 2 →* MulAut P :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp φ)
  have hψ : ∀ q p, ψ q p = e ⟨φ q * (e.symm p : Y) * (φ q)⁻¹, by
      exact hTn.conj_mem _ (e.symm p).2 _⟩ := fun q p => rfl
  refine hA ψ ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : φ q ∈ Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg (fun α : MulAut P => α (e ⟨x, hx⟩)) hq
      simp only [hψ, MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
      have h3 := congrArg (fun y : ↥(genFittingFStar Y) => (y : Y)) (e.injective h2)
      simp only at h3
      calc x * φ q = (φ q * x * (φ q)⁻¹) * φ q := by rw [h3]
        _ = φ q * x := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact hφi (h1.trans (map_one φ).symm)
  · intro a p hp
    let Fix : Subgroup P :=
      { carrier := {p | ψ a p = p}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_mul, hx, hy]
        one_mem' := map_one _
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [map_inv, hx] }
    have hfixH : ∀ H : Subgroup P,
        (∀ x ∈ (H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype,
          ∀ y ∈ tightCore R, x * y = y * x) → H ≤ Fix := by
      intro H hcH p hp
      show ψ a p = p
      rw [hψ]
      have hmem : ((e.symm p : ↥(genFittingFStar Y)) : Y) ∈
          (H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype :=
        ⟨e.symm p, ⟨p, hp, rfl⟩, rfl⟩
      have hcomm := hcH _ hmem (φ a) (hφK a)
      have hx : φ a * ((e.symm p : ↥(genFittingFStar Y)) : Y) * (φ a)⁻¹ =
          ((e.symm p : ↥(genFittingFStar Y)) : Y) := by
        rw [← hcomm]
        group
      have : (⟨φ a * (e.symm p : Y) * (φ a)⁻¹, hTn.conj_mem _ (e.symm p).2 _⟩ :
          ↥(genFittingFStar Y)) = e.symm p := Subtype.ext hx
      rw [this, MulEquiv.apply_symm_apply]
    exact (sup_le (hfixH H₁ hc₁) (hfixH H₂ hc₂) hp : p ∈ Fix)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
