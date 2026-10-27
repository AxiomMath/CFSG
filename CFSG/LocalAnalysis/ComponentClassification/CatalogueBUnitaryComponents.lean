module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryNorm
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

noncomputable section

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Assembly.LowTwoRank CatalogueBHigherLinearField

theorem map_conjTr {K F : Type*} [Field K] [Field F]
    (e : K ≃+* F) (sigma : K ≃+* K) (tau : F ≃+* F)
    (he : ∀ x : K, e (sigma x) = tau (e x))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    e.toRingHom.mapMatrix (conjTr sigma A) =
      conjTr tau (e.toRingHom.mapMatrix A) := by
  ext i j
  exact he (A j i)

theorem mem_SUid_map_iff {K F : Type*} [Field K] [Field F]
    (e : K ≃+* F) (sigma : K ≃+* K) (tau : F ≃+* F)
    (he : ∀ x : K, e (sigma x) = tau (e x)) (n : ℕ) (A : GL (Fin n) K) :
    glFieldEquiv (Fin n) e A ∈ SUid tau n ↔ A ∈ SUid sigma n := by
  rw [mem_SUid, mem_SUid]
  have hmatrix : (glFieldEquiv (Fin n) e A).val = e.toRingHom.mapMatrix A.val := rfl
  have hmapinj : Function.Injective
      (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) F) := by
    intro B C h
    ext i j
    exact e.injective (congrFun₂ h i j)
  rw [hmatrix, ← e.toRingHom.map_det, ← map_conjTr e sigma tau he n A.val,
    ← map_mul, ← map_one e.toRingHom.mapMatrix, ← map_one e]
  exact and_congr e.injective.eq_iff hmapinj.eq_iff

@[expose] def specialUnitaryRingEquiv {K F : Type*} [Field K] [Field F]
    (e : K ≃+* F) (sigma : K ≃+* K) (tau : F ≃+* F)
    (he : ∀ x : K, e (sigma x) = tau (e x)) (n : ℕ) :
    SUid sigma n ≃* SUid tau n where
  toFun A := ⟨glFieldEquiv (Fin n) e A.val, (mem_SUid_map_iff e sigma tau he n A.val).mpr A.property⟩
  invFun A := ⟨(glFieldEquiv (Fin n) e).symm A.val,
    (mem_SUid_map_iff e sigma tau he n ((glFieldEquiv (Fin n) e).symm A.val)).mp
      (by simpa only [MulEquiv.apply_symm_apply] using A.property)⟩
  left_inv A := Subtype.ext ((glFieldEquiv (Fin n) e).symm_apply_apply A.val)
  right_inv A := Subtype.ext ((glFieldEquiv (Fin n) e).apply_symm_apply A.val)
  map_mul' A B := Subtype.ext ((glFieldEquiv (Fin n) e).map_mul A.val B.val)

theorem specialUnitaryRingEquiv_entry {K F : Type*} [Field K] [Field F]
    (e : K ≃+* F) (sigma : K ≃+* K) (tau : F ≃+* F)
    (he : ∀ x : K, e (sigma x) = tau (e x)) (n : ℕ)
    (A : SUid sigma n) (i j : Fin n) :
    (specialUnitaryRingEquiv e sigma tau he n A).val.val i j = e (A.val.val i j) := rfl

private theorem SUid_quasisimple_typeZero (K : Type) [Field K]
    (sigma : K ≃+* K) (hunitary : IsUnitaryInvolution sigma) (n : ℕ) (hn : 3 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ sigma s * s ≠ 1) :
    CFSG.IsQuasisimple (SUid sigma n) := by
  let : Group.IsPerfect (SUid sigma n) := isPerfect_SUid hunitary hn h3
  let : IsSimpleGroup (StatedProj (SUid sigma n)) :=
    isSimpleGroup_statedProj_SUid hunitary hn h3
  have hprojective : CFSG.Open.IsQuasisimple (StatedProj (SUid sigma n)) :=
    Quasisimple.simple_of_perfect (StatedProj (SUid sigma n))
  have hscalars : (StatedScalars (Fin n) K).subgroupOf (SUid sigma n) ≤
      Subgroup.center (SUid sigma n) := by
    intro A hA
    apply Subgroup.mem_center_iff.mpr
    intro B
    have hcentral : A.val ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hA
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentral) B.val)
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (CentralExtensions.quasisimple_of_surjective hprojective
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (SUid sigma n)))
      (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hscalars))

theorem SUid_quasisimple {K : Type*} [Field K] [Finite K]
    (sigma : K ≃+* K) (hunitary : IsUnitaryInvolution sigma) (n : ℕ) (hn : 3 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ sigma s * s ≠ 1) :
    CFSG.IsQuasisimple (SUid sigma n) := by
  let F := Shrink.{0} K
  let e : K ≃+* F := (Shrink.ringEquiv.{0} K).symm
  let tau : F ≃+* F := (e.symm.trans sigma).trans e
  have he : ∀ x : K, e (sigma x) = tau (e x) := by
    intro x
    dsimp only [tau, RingEquiv.trans_apply]
    rw [e.symm_apply_apply]
  have hunitaryF : IsUnitaryInvolution tau := by
    constructor
    · intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← he, ← he, hunitary.invol]
    · obtain ⟨x, hx⟩ := hunitary.exists_ne
      exact ⟨e x, by rw [← he]; exact fun h => hx (e.injective h)⟩
    · intro a ha
      obtain ⟨b, rfl⟩ := e.surjective a
      have hb : sigma b = b := e.injective (by simpa only [he] using ha)
      obtain ⟨c, hc⟩ := hunitary.trace_surj b hb
      exact ⟨e c, by rw [← he, ← map_add, hc]⟩
    · intro a ha ha0
      obtain ⟨b, rfl⟩ := e.surjective a
      have hb : sigma b = b := e.injective (by simpa only [he] using ha)
      have hb0 : b ≠ 0 := fun hb => ha0 (by rw [hb, map_zero])
      obtain ⟨c, hc⟩ := hunitary.norm_surj b hb hb0
      exact ⟨e c, by rw [← he, ← map_mul, hc]⟩
  have h3F : n = 3 → ∃ s : F, s ≠ 0 ∧ tau s * s ≠ 1 := by
    intro hn3
    obtain ⟨s, hs0, hs⟩ := h3 hn3
    refine ⟨e s, (map_ne_zero e).mpr hs0, ?_⟩
    rw [← he, ← map_mul, ← map_one e]
    exact fun h => hs (e.injective h)
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (specialUnitaryRingEquiv e sigma tau he n)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (SUid_quasisimple_typeZero F tau hunitaryF n hn h3F)))

theorem exists_norm_ne_one_of_fixed_card {K : Type*} [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) ≠ 2) :
    ∃ s : K, s ≠ 0 ∧ sigma s * s ≠ 1 := by
  let F := CatalogueBLinearTwoDescent.fixedSubfield K sigma
  have hex : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! h
    have hall : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr (h a ha)
    apply hq2
    apply Nat.card_eq_two_iff.mpr
    refine ⟨(0 : F), 1, zero_ne_one, ?_⟩
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact hall a
  obtain ⟨a, ha0, ha1⟩ := hex
  have ha : sigma (a : K) = a :=
    (CatalogueBLinearTwoDescent.mem_fixedSubfield K sigma a).mp a.property
  have ha0K : (a : K) ≠ 0 := by
    intro h
    exact ha0 (Subtype.ext h)
  obtain ⟨s, hs⟩ := CatalogueBUnitaryNorm.exists_norm sigma hsigma hne (a : K) ha ha0K
  refine ⟨s, ?_, ?_⟩
  · intro hs0
    rw [hs0, map_zero, mul_zero] at hs
    exact ha0K hs.symm
  · intro hs1
    apply ha1
    exact Subtype.ext (hs.symm.trans hs1)

theorem SUid_quasisimple_finite {K : Type*} [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (n : ℕ) (hn : 3 ≤ n)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2)) :
    CFSG.IsQuasisimple (SUid sigma n) := by
  apply SUid_quasisimple sigma (CatalogueBUnitaryNorm.isUnitaryInvolution sigma hsigma hne) n hn
  intro hn3
  apply exists_norm_ne_one_of_fixed_card sigma hsigma hne
  intro hq2
  exact hnq (by rw [hn3, hq2])

theorem unitary_isometry_p_components {K : Type*} [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (n : ℕ) (hn : 3 ≤ n)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2)) :
    CFSG.IsQuasisimple (SUid sigma n) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (Uid sigma n),
        CFSG.IsPComponent p L → L = specialUnitary sigma n ∧ CFSG.IsQuasisimple L := by
  have hquasi := SUid_quasisimple_finite sigma hsigma hne n hn hnq
  exact ⟨hquasi, fun p hp L hL => pComponent_eq_specialUnitary sigma n hquasi p hp L hL⟩

theorem quadraticFrobenius_data {K : Type*} [Field K] [Finite K]
    (r e : ℕ) [Fact r.Prime] [CharP K r]
    (hK : Nat.card K = (r ^ e) ^ 2) :
    (iterateFrobeniusEquiv K r e) ^ 2 = 1 ∧
      iterateFrobeniusEquiv K r e ≠ 1 ∧
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K
        (iterateFrobeniusEquiv K r e)) = r ^ e := by
  let F := Shrink.{0} K
  let s : K ≃+* F := (Shrink.ringEquiv.{0} K).symm
  have hF : Nat.card F = (r ^ e) ^ 2 := (Nat.card_congr s.toEquiv).symm.trans hK
  let : CharP F r := charP_of_card_sq (p := r) (f := e) hF
  let sigma := iterateFrobeniusEquiv K r e
  have hs (x : K) : s (sigma x) = CFSG.LieType.BorelTits.unitaryInvolution F r e (s x) := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    change s ((iterateFrobeniusEquiv K r e) x) = _
    rw [iterateFrobeniusEquiv_def, map_pow]
  have hsq : sigma ^ 2 = 1 := by
    ext x
    change sigma (sigma x) = x
    apply s.injective
    rw [hs, hs, CFSG.LieType.BorelTits.unitaryInvolution_involutive hF]
  have hne : sigma ≠ 1 := by
    obtain ⟨x, hx⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hF
    obtain ⟨y, rfl⟩ := s.surjective x
    intro h
    apply hx
    rw [← hs]
    exact congrArg s (DFunLike.congr_fun h y)
  have hparams := CatalogueBLinearTwoDescent.quadraticField_parameters K r (e * 2)
    (Fact.out : r.Prime) (by rw [pow_mul]; exact hK) sigma hsq hne
  exact ⟨hsq, hne, by simpa using hparams.2.2⟩

theorem unitary_field_isometry_p_components {K : Type*} [Field K] [Finite K]
    (r e : ℕ) [Fact r.Prime] [CharP K r]
    (hK : Nat.card K = (r ^ e) ^ 2) (n : ℕ) (hn : 3 ≤ n)
    (hnq : (n, r ^ e) ≠ (3, 2)) :
    CFSG.IsQuasisimple (SUid (iterateFrobeniusEquiv K r e) n) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (Uid (iterateFrobeniusEquiv K r e) n),
        CFSG.IsPComponent p L →
          L = specialUnitary (iterateFrobeniusEquiv K r e) n ∧ CFSG.IsQuasisimple L := by
  obtain ⟨hsq, hne, hfixed⟩ := quadraticFrobenius_data r e hK
  apply unitary_isometry_p_components (iterateFrobeniusEquiv K r e) hsq hne n hn
  simpa only [hfixed] using hnq

theorem stated_unitary_isometry_p_components (K : Type) [Field K] [Finite K]
    (r e : ℕ) [Fact r.Prime] (hK : Nat.card K = (r ^ e) ^ 2)
    (n : ℕ) (hn : 3 ≤ n) (hnq : (n, r ^ e) ≠ (3, 2)) :
    letI : CharP K r := charP_of_card_sq (p := r) (f := e) hK
    let sigma := CFSG.LieType.BorelTits.unitaryInvolution K r e
    CFSG.IsQuasisimple (StatedSU n (r ^ e) K) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (Uid sigma n), CFSG.IsPComponent p L →
        L = (StatedSU n (r ^ e) K).subgroupOf (Uid sigma n) ∧ CFSG.IsQuasisimple L := by
  let : CharP K r := charP_of_card_sq (p := r) (f := e) hK
  change CFSG.IsQuasisimple (StatedSU n (r ^ e) K) ∧ _
  have hfull := unitary_field_isometry_p_components r e hK n hn hnq
  rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n] at hfull
  refine ⟨hfull.1, fun p hp L hL => ?_⟩
  obtain ⟨heq, hquasi⟩ := hfull.2 p hp L hL
  refine ⟨heq.trans ?_, hquasi⟩
  rw [specialUnitary_eq_subgroupOf, SUid_eq_statedSU hK n]

end

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry
