module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1POddOut
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)

theorem isCyclic_quotient_of_relIndex_le_two {A : Type*} [Group A] [Finite A]
    {M N : Subgroup A} [M.Normal] (h : M.relIndex N ≤ 2) : IsCyclic (↥N ⧸ M.subgroupOf N) := by
  have h0 : M.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine isCyclic_of_card_dvd_prime Nat.prime_two ?_
  change M.relIndex N ∣ 2
  rcases (show M.relIndex N = 1 ∨ M.relIndex N = 2 by omega) with h1 | h1 <;> rw [h1]
  exact one_dvd 2

theorem outNoA4_of_relIndex_chain {T : Type*} [Group T] [Finite (MulAut T)]
    {L₁ L₂ L₃ : Subgroup (MulAut T)} [L₁.Normal] [L₂.Normal] [L₃.Normal]
    (h₁ : (inner T).relIndex L₁ ≤ 2) (h₂ : L₁.relIndex L₂ ≤ 2) (h₃ : L₂.relIndex L₃ ≤ 2)
    (h₄ : IsCyclic (MulAut T ⧸ L₃)) : OutNoA4 T := by
  have := isCyclic_quotient_of_relIndex_le_two h₁
  have := isCyclic_quotient_of_relIndex_le_two h₂
  have := isCyclic_quotient_of_relIndex_le_two h₃
  refine outNoA4_of_false fun R φ hφ hinn => ?_
  have k₁ : ∀ x : ↥L₁, QuotientGroup.mk' ((inner T).subgroupOf L₁) x = 1 →
      (x : MulAut T) ∈ inner T := fun x hx => by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
  have k₂ : ∀ x : ↥L₂, QuotientGroup.mk' (L₁.subgroupOf L₂) x = 1 → (x : MulAut T) ∈ L₁ :=
    fun x hx => by rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
  have k₃ : ∀ x : ↥L₃, QuotientGroup.mk' (L₂.subgroupOf L₃) x = 1 → (x : MulAut T) ∈ L₂ :=
    fun x hx => by rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
  have e₁ := forall_eq_one_of_cyclic (R := R) (φ := φ) _ k₁ hφ hinn
  have e₂ := forall_eq_one_of_cyclic (R := R) (φ := φ) _ k₂ hφ e₁
  have e₃ := forall_eq_one_of_cyclic (R := R) (φ := φ) _ k₃ hφ e₂
  exact false_of_forall_eq_one_ker (QuotientGroup.mk' L₃) (fun _ _ => mul_comm_of_isCyclic _ _)
    hφ fun r hr => e₃ r (by rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hr)

section Orth

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] def isometryDet : matrixIsometries Q →* Kˣ :=
  GeneralLinearGroup.det.comp (matrixIsometries Q).subtype

@[expose] def specialIsometries : Subgroup (matrixIsometries Q) := (isometryDet Q).ker

theorem det_matrixConjugation_eq_one (g : coordinateSemilinearGroup d K) {A : GL (Fin d) K}
    (hA : GeneralLinearGroup.det A = 1) : GeneralLinearGroup.det (matrixConjugation g A) = 1 := by
  have h1 : GeneralLinearGroup.det
      (CatalogueBHigherLinearField.glFieldAut (Fin d) K g.right A) = 1 := by
    have hval : (CatalogueBHigherLinearField.glFieldAut (Fin d) K g.right A).val =
        g.right.toRingHom.mapMatrix A.val := by
      ext i j
      rfl
    have hA' : A.val.det = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, hA, Units.val_one]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, hval, ← RingHom.map_det, hA', map_one, Units.val_one]
  rw [matrixConjugation_apply, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]

theorem conj_matrixIsometryInclusion (g : similarityPairs Q) (A : matrixIsometries Q) :
    g * matrixIsometryInclusion Q A * g⁻¹ = matrixIsometryInclusion Q
      ⟨matrixConjugation g.val A.val, matrixConjugation_mem_isometries Q g A.val A.2⟩ := by
  apply Subtype.ext
  exact (matrixConjugation_inl g.val A.val).symm

theorem specialPairs_normal :
    ((specialIsometries Q).map (matrixIsometryInclusion Q)).Normal := by
  constructor
  rintro _ ⟨A, hA, rfl⟩ g
  exact ⟨_, MonoidHom.mem_ker.mpr (det_matrixConjugation_eq_one g.val (MonoidHom.mem_ker.mp hA)),
    (conj_matrixIsometryInclusion Q g A).symm⟩

theorem isometryDet_sq (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (A : matrixIsometries Q) : isometryDet Q A ^ 2 = 1 := by
  have h := det_sq_eq_pow_of_similitude Q hnd A.val.val 1 fun v => by
    rw [one_mul, ← matrixLinearEquiv_apply]
    exact (mem_matrixIsometries_iff Q A.val).mp A.2 v
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (GeneralLinearGroup.det A.val : K) ^ 2 = 1
  rw [GeneralLinearGroup.val_det_apply, h, one_pow]

theorem index_specialIsometries_le_two (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (specialIsometries Q).index ≤ 2 := by
  rw [specialIsometries, Subgroup.index_ker]
  have hsub : Set.range (isometryDet Q) ⊆ {1, -1} := by
    rintro _ ⟨A, rfl⟩
    have h : isometryDet Q A ^ 2 = 1 ^ 2 := by rw [one_pow]; exact isometryDet_sq Q hnd A
    exact Units.eq_or_eq_neg_of_sq_eq_sq _ _ h
  calc Nat.card (Set.range (isometryDet Q)) = (Set.range (isometryDet Q)).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, -1} : Set Kˣ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem specialRange_normal (hsurj : Function.Surjective (matrixProjectiveConjugationHom Q)) :
    ((specialIsometries Q).map (isometryConjugationHom Q)).Normal := by
  have h : (specialIsometries Q).map (isometryConjugationHom Q) =
      ((specialIsometries Q).map (matrixIsometryInclusion Q)).map
        (matrixProjectiveConjugationHom Q) := by
    rw [Subgroup.map_map]
    rfl
  rw [h]
  exact (specialPairs_normal Q).map _ hsurj

theorem isometryRange_normal (hsurj : Function.Surjective (matrixProjectiveConjugationHom Q)) :
    (isometryConjugationHom Q).range.Normal := by
  have h : (isometryConjugationHom Q).range =
      (matrixIsometryPairs Q).map (matrixProjectiveConjugationHom Q) := by
    rw [isometryConjugationHom, MonoidHom.range_comp]
    rfl
  rw [h]
  exact (matrixIsometryPairs_normal Q).map _ hsurj

theorem linearConjugationRange_normal
    (hsurj : Function.Surjective (matrixProjectiveConjugationHom Q)) :
    (linearConjugationHom Q).range.Normal := by
  have h : (linearConjugationHom Q).range =
      (linearSimilarityPairs Q).map (matrixProjectiveConjugationHom Q) := by
    rw [linearConjugationHom, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h]
  exact Subgroup.Normal.map inferInstance _ hsurj

variable [Finite K]

theorem two_le_index_specialIsometries
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1) :
    2 ≤ (specialIsometries Q).index := by
  obtain ⟨A, hA⟩ := hneg
  have h0 : (specialIsometries Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (specialIsometries Q).index ≠ 1 := fun h => by
    have hAS : A ∈ specialIsometries Q := by
      rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.mem_top A
    exact hA (MonoidHom.mem_ker.mp hAS)
  omega

theorem relIndex_commutator_special_le_two
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1) :
    (commutator (matrixIsometries Q)).relIndex (specialIsometries Q) ≤ 2 := by
  have hle : commutator (matrixIsometries Q) ≤ specialIsometries Q :=
    Abelianization.commutator_subset_ker (isometryDet Q)
  have h := Subgroup.relIndex_mul_index hle
  have hc : (commutator (matrixIsometries Q)).index =
      Nat.card (Abelianization (matrixIsometries Q)) := rfl
  have h2 := two_le_index_specialIsometries Q hneg
  rw [hc] at h
  by_contra hlt
  have : 3 * 2 ≤ (commutator (matrixIsometries Q)).relIndex (specialIsometries Q) *
      (specialIsometries Q).index := Nat.mul_le_mul (by omega) h2
  omega

theorem relIndex_inner_specialRange_le_two
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1) :
    (inner (matrixProjectiveDerived Q)).relIndex
      ((specialIsometries Q).map (isometryConjugationHom Q)) ≤ 2 := by
  rw [inner_eq_map_commutator Q]
  have h0 : (commutator (matrixIsometries Q)).relIndex (specialIsometries Q) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (relIndex_map_dvd_relIndex _ _ _)).trans
    (relIndex_commutator_special_le_two Q hab hneg)

theorem relIndex_specialRange_isometryRange_le_two
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ((specialIsometries Q).map (isometryConjugationHom Q)).relIndex
      (isometryConjugationHom Q).range ≤ 2 := by
  rw [MonoidHom.range_eq_map]
  have h0 : (specialIsometries Q).relIndex ⊤ ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (relIndex_map_dvd_relIndex _ _ _)).trans ?_
  rw [Subgroup.relIndex_top_right]
  exact index_specialIsometries_le_two Q hnd

theorem relIndex_isometryRange_linearRange_le_two (hQ : ∃ v, Q v ≠ 0) :
    (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range ≤ 2 := by
  have h3 := relIndex_isometryRange_dvd Q hQ
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
  rw [hsq] at h3
  exact Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_right _ _))

theorem isCyclic_quotient_linearRange [(linearConjugationHom Q).range.Normal]
    (hsurj : Function.Surjective (matrixProjectiveConjugationHom Q)) :
    IsCyclic (MulAut (matrixProjectiveDerived Q) ⧸ (linearConjugationHom Q).range) := by
  have := fieldQuotient_cyclic Q
  have hLD : linearSimilarityPairs Q ≤
      (linearConjugationHom Q).range.comap (matrixProjectiveConjugationHom Q) :=
    fun g hg => ⟨⟨g, hg⟩, rfl⟩
  refine isCyclic_of_surjective (QuotientGroup.map _ _ _ hLD)
    (QuotientGroup.map_surjective_of_surjective _ _ _ (fun y => ?_) hLD)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g, rfl⟩ := hsurj x
  exact ⟨g, rfl⟩

theorem outNoA4_of_orthLayers (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ : ∃ v, Q v ≠ 0) (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1) (htop : matrixProjectiveImage Q = ⊤) :
    OutNoA4 (matrixProjectiveDerived Q) := by
  have hsurj : Function.Surjective (matrixProjectiveConjugationHom Q) :=
    MonoidHom.range_eq_top.mp htop
  have := specialRange_normal Q hsurj
  have := isometryRange_normal Q hsurj
  have := linearConjugationRange_normal Q hsurj
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  exact outNoA4_of_relIndex_chain (relIndex_inner_specialRange_le_two Q hab hneg)
    (relIndex_specialRange_isometryRange_le_two Q hnd)
    (relIndex_isometryRange_linearRange_le_two Q hQ) (isCyclic_quotient_linearRange Q hsurj)

end Orth

theorem exists_isometryDet_ne_one_of_swap {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (h2 : ringChar K ≠ 2) {a b : Fin d} (hab : a ≠ b)
    (hQ : ∀ v, Q (v ∘ Equiv.swap a b) = Q v) : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1 := by
  set M : Matrix (Fin d) (Fin d) K := (Equiv.swap a b).permMatrix K with hM
  have hdet : M.det = -1 := by
    rw [hM, Matrix.det_permutation, Equiv.Perm.sign_swap hab]
    simp
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact neg_ne_zero.mpr one_ne_zero
  set A := GeneralLinearGroup.mkOfDetNeZero M hdet0 with hA
  have hAiso : A ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    rw [matrixLinearEquiv_apply, hA, GeneralLinearGroup.val_mkOfDetNeZero, hM,
      Matrix.permMatrix_mulVec]
    exact hQ v
  refine ⟨⟨A, hAiso⟩, fun h => ?_⟩
  have h1 : (GeneralLinearGroup.det A : K) = 1 := congrArg Units.val h
  rw [GeneralLinearGroup.val_det_apply, hA, GeneralLinearGroup.val_mkOfDetNeZero, hdet] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two h2 h1

theorem coordinateQuadPlus_comp_swap (n : ℕ) (K : Type*) [Field K] (i₀ : Fin n)
    (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K
        (v ∘ Equiv.swap (plusIndexEquiv n (.inl i₀)) (plusIndexEquiv n (.inr i₀))) =
      coordinateQuadPlus n K v := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  by_cases hi : i = i₀
  · subst hi
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
  · rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne] <;> simp [hi]

theorem coordinateQuadMinus_comp_swap (n : ℕ) (K : Type*) [Field K] (hn : 1 ≤ n) (b c : K)
    (i₀ : Fin (n - 1)) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c
        (v ∘ Equiv.swap (minusIndexEquiv n hn (.inl i₀)) (minusIndexEquiv n hn (.inr (.inl i₀)))) =
      coordinateQuadMinus n K hn b c v := by
  have ht : ∀ j : Fin 2, Equiv.swap (minusIndexEquiv n hn (.inl i₀))
      (minusIndexEquiv n hn (.inr (.inl i₀))) (minusIndexEquiv n hn (.inr (.inr j))) =
        minusIndexEquiv n hn (.inr (.inr j)) := fun j =>
    Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
  have hs : ∀ i : Fin (n - 1),
      v (Equiv.swap (minusIndexEquiv n hn (.inl i₀)) (minusIndexEquiv n hn (.inr (.inl i₀)))
          (minusIndexEquiv n hn (.inl i))) *
        v (Equiv.swap (minusIndexEquiv n hn (.inl i₀)) (minusIndexEquiv n hn (.inr (.inl i₀)))
          (minusIndexEquiv n hn (.inr (.inl i)))) =
      v (minusIndexEquiv n hn (.inl i)) * v (minusIndexEquiv n hn (.inr (.inl i))) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne] <;> simp [hi]
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [Function.comp_apply, ht, hs]

theorem outNoA4_of_statedClassicalModel_odd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) : OutNoA4 S := by
  obtain ⟨⟨hp, hf, hn3, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K p :=
    finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  refine OutNoA4.of_mulEquiv (coordinateOddWitnessEquiv K e).symm
    (outNoA4_of_ker_le_inner (QuotientGroup.mk' (inner _)) (fun a b => ?_)
      (QuotientGroup.ker_mk' _).le)
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective _ b
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hc := commutator_mem_inner_coordinateQuadOdd K n hchar hn3 β⁻¹ α⁻¹
  rwa [inv_inv, inv_inv, ← _root_.mul_inv_rev, mul_assoc] at hc

theorem outNoA4_of_statedClassicalModel_plus {S : Type} [Group S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 5 ≤ n) (h : StatedClassicalModel S .POmegaPlus n p f) : OutNoA4 S := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hp2
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound S .POmegaPlus
    (.inr (.inl rfl)) n p f h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound
    (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hneg := exists_isometryDet_ne_one_of_swap (coordinateQuadPlus n K) h2
    (a := plusIndexEquiv n (.inl ⟨0, by omega⟩)) (b := plusIndexEquiv n (.inr ⟨0, by omega⟩))
    (by simp) (coordinateQuadPlus_comp_swap n K _)
  exact OutNoA4.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (outNoA4_of_orthLayers _ hnd hQ hab' hneg htop)

theorem outNoA4_of_statedClassicalModel_minus {S : Type} [Group S] {n p f : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .POmegaMinus n p f) : OutNoA4 S := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hp2
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound S .POmegaMinus
    (.inr (.inr rfl)) n p f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' := CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound
    (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  have hneg := exists_isometryDet_ne_one_of_swap (coordinateQuadMinus n K hn1 b c) h2
    (a := minusIndexEquiv n hn1 (.inl ⟨0, by omega⟩))
    (b := minusIndexEquiv n hn1 (.inr (.inl ⟨0, by omega⟩))) (by simp)
    (coordinateQuadMinus_comp_swap n K hn1 b c _)
  exact OutNoA4.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
    (outNoA4_of_orthLayers _ hnd hQ hab' hneg htop)

theorem outNoA4_of_statedClassicalModel_orth_any {S : Type} [Group S] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hp2 : p ≠ 2)
    (hn : ¬(t = .POmegaPlus ∧ n = 4)) (h : StatedClassicalModel S t n p f) : OutNoA4 S := by
  rcases ht with rfl | rfl | rfl
  · exact outNoA4_of_statedClassicalModel_odd h
  · have hn4 : 4 ≤ n := h.1.2.2
    have hn5 : 5 ≤ n := by
      by_contra hlt
      exact hn ⟨rfl, by omega⟩
    exact outNoA4_of_statedClassicalModel_plus hp2 hn5 h
  · exact outNoA4_of_statedClassicalModel_minus hp2 h

theorem harris82OutQuatThreeOrth_holds : Harris82OutQuatThreeOrth := by
  intro S _ t n f ht _ hm _ hD4 X _ _ hX hXS R φ hφ
  obtain ⟨e⟩ := hXS
  have hcl : StatedClassicalModel S t n 3 f := by
    rcases hm with ⟨-, h⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, rfl, -⟩
    · exact h
    · exact absurd ht' (by rcases ht with rfl | rfl | rfl <;> decide)
    · exact absurd ht' (by rcases ht with rfl | rfl | rfl <;> decide)
    · exact absurd ht (by decide)
  have hS := outNoA4_of_statedClassicalModel_orth_any ht (by norm_num)
    (fun h => hD4 f (by obtain ⟨rfl, rfl⟩ := h; exact hm)) hcl
  have : Group.IsPerfect X := hX.1
  exact OutNoA4.of_centerQuotient (OutNoA4.of_mulEquiv e.symm hS) R φ hφ

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
