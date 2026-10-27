module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixed

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalLinearFixed
  CatalogueBOrthogonalFieldFixed

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem matrixIsometries_map (Q : QuadraticForm K (Fin d → K)) :
    (matrixIsometries Q).map matrixLinearIso.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.map_comap_eq_self_of_surjective matrixLinearIso.surjective _

theorem matrixDerived_map (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerived Q).map matrixLinearIso.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries_map]

theorem mem_matrixDerived_iff (Q : QuadraticForm K (Fin d → K)) (A : GL (Fin d) K) :
    A ∈ matrixDerived Q ↔ matrixLinearIso A ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [← matrixDerived_map, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mem_orthogonalDerived_iff (Q : QuadraticForm K (Fin d → K))
    (B : TauCeti.QuadraticMap.orthogonalGroup Q) :
    B ∈ orthogonalDerived Q ↔ B.val ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [← Subgroup.map_subtype_commutator]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm

@[expose] def derivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃* orthogonalDerived Q where
  toFun A := ⟨⟨matrixLinearIso A.val, matrixDerived_le_isometries Q A.property⟩,
    (mem_orthogonalDerived_iff Q _).mpr ((mem_matrixDerived_iff Q A.val).mp A.property)⟩
  invFun B := ⟨matrixLinearIso.symm B.val.val, (mem_matrixDerived_iff Q _).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact (mem_orthogonalDerived_iff Q B.val).mp B.property)⟩
  left_inv A := Subtype.ext (matrixLinearIso.symm_apply_apply A.val)
  right_inv B := Subtype.ext (Subtype.ext (matrixLinearIso.apply_symm_apply B.val.val))
  map_mul' A B := Subtype.ext (Subtype.ext (map_mul matrixLinearIso A.val B.val))

theorem derivedEquiv_val (Q : QuadraticForm K (Fin d → K)) (A : matrixDerived Q) :
    (derivedEquiv Q A).val.val = matrixLinearIso A.val := rfl

theorem derivedEquiv_symm_val (Q : QuadraticForm K (Fin d → K)) (B : orthogonalDerived Q) :
    ((derivedEquiv Q).symm B).val = matrixLinearIso.symm B.val.val := rfl

theorem matrixLinearEquiv_scalar (c : Kˣ) (v : Fin d → K) :
    matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = (c : K) • v := by
  rw [matrixLinearEquiv_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

theorem matrixLinearIso_scalar_neg_one :
    matrixLinearIso (GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ)) = LinearEquiv.neg K := by
  apply LinearEquiv.ext
  intro v
  change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ)) v = -v
  rw [matrixLinearEquiv_scalar]
  simp

theorem scalar_mem_matrixIsometries_iff (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin d) c ∈ matrixIsometries Q ↔ c = 1 ∨ c = -1 := by
  rw [mem_matrixIsometries_iff]
  simp only [matrixLinearEquiv_scalar, QuadraticMap.map_smul, smul_eq_mul]
  constructor
  · intro hc
    obtain ⟨v, hv⟩ := hQ
    have hcc : (c : K) * c = 1 := mul_right_cancel₀ hv ((hc v).trans (one_mul (Q v)).symm)
    rcases mul_self_eq_one_iff.mp hcc with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by simpa using h1))
  · rintro (rfl | rfl) v <;> simp

theorem matrixDerivedScalars_map (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    (matrixDerivedScalars Q).map (derivedEquiv Q).toMonoidHom =
      (scalarSigns Q).subgroupOf (orthogonalDerived Q) := by
  ext B
  rw [Subgroup.mem_map_equiv, mem_matrixDerivedScalars_iff, Subgroup.mem_subgroupOf,
    mem_scalarSigns_iff, derivedEquiv_symm_val]
  constructor
  · rintro ⟨c, hc⟩
    have hiso : GeneralLinearGroup.scalar (Fin d) c ∈ matrixIsometries Q := by
      rw [hc, ← derivedEquiv_symm_val]
      exact matrixDerived_le_isometries Q ((derivedEquiv Q).symm B).property
    have hB : B.val.val = matrixLinearIso (GeneralLinearGroup.scalar (Fin d) c) := by
      rw [hc, MulEquiv.apply_symm_apply]
    rcases (scalar_mem_matrixIsometries_iff Q hQ c).mp hiso with rfl | rfl
    · left
      apply Subtype.ext
      rw [hB, map_one, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [hB, matrixLinearIso_scalar_neg_one, QuadraticMap.coe_negOrthogonal]
  · rintro (hB | hB)
    · refine ⟨1, ?_⟩
      rw [hB, map_one]
      exact (map_one matrixLinearIso.symm).symm
    · refine ⟨-1, ?_⟩
      rw [hB, QuadraticMap.coe_negOrthogonal, ← matrixLinearIso_scalar_neg_one,
        MulEquiv.symm_apply_apply]

@[expose] def projectiveEquiv (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    matrixProjectiveDerived Q ≃* projectiveDerived Q :=
  QuotientGroup.congr (matrixDerivedScalars Q) ((scalarSigns Q).subgroupOf (orthogonalDerived Q))
    (derivedEquiv Q) (matrixDerivedScalars_map Q hQ)

theorem projectiveEquiv_mk (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (A : matrixDerived Q) :
    projectiveEquiv Q hQ (matrixProjectiveProjection Q A) =
      QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) (derivedEquiv Q A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem projectiveEquiv_mk_of_val (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (A : matrixDerived Q) (B : orthogonalDerived Q) (hB : B.val.val = matrixLinearIso A.val) :
    projectiveEquiv Q hQ (matrixProjectiveProjection Q A) =
      QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) B := by
  rw [projectiveEquiv_mk]
  exact congrArg _ (Subtype.ext (Subtype.ext hB.symm))

theorem projectiveEquiv_symm_mk (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (B : orthogonalDerived Q) :
    (projectiveEquiv Q hQ).symm
        (QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) B) =
      matrixProjectiveProjection Q ((derivedEquiv Q).symm B) := by
  rw [MulEquiv.symm_apply_eq, projectiveEquiv_mk, MulEquiv.apply_symm_apply]

theorem coordinateSemilinearMap_eq_matrix (g : coordinateSemilinearGroup d K)
    (hg : g.right = 1) :
    coordinateSemilinearMap g = (matrixLinearEquiv g.left).toAddEquiv := by
  apply AddEquiv.ext
  intro v
  change matrixLinearEquiv g.left (coordinateFieldMap d g.right v) = matrixLinearEquiv g.left v
  rw [hg]
  rfl

theorem matrix_similarity (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (hg : g.val.right = 1) (x : Fin d → K) :
    Q (matrixLinearEquiv g.val.left x) = (multiplier Q g : K) * Q x := by
  have h := multiplier_spec Q g x
  rw [coordinateSemilinearMap_eq_matrix g.val hg, hg] at h
  exact h

theorem projectiveEquiv_conjugation_linear (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) (hg : g.val.right = 1)
    (x : matrixProjectiveDerived Q) :
    projectiveEquiv Q hQ (matrixProjectiveConjugation Q g x) =
      projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
        (matrix_similarity Q g hg) (projectiveEquiv Q hQ x) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [matrixProjectiveConjugation_mk, projectiveEquiv_mk, projectiveEquiv_mk,
    projectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change matrixLinearEquiv (matrixConjugation g.val A.val) v =
    matrixLinearEquiv g.val.left (matrixLinearEquiv A.val ((matrixLinearEquiv g.val.left).symm v))
  rw [matrixConjugation_vector, coordinateSemilinearMap_eq_matrix g.val hg]
  rfl

theorem projectiveEquiv_conjugation (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) (x : matrixProjectiveDerived Q) :
    projectiveEquiv Q hQ (matrixProjectiveConjugation Q g x) =
      projectiveSemilinearConjugation Q g.val.right (coordinateSemilinearMap g.val)
        (multiplier Q g) (coordinateSemilinearMap_smul g.val) (multiplier_spec Q g)
        (projectiveEquiv Q hQ x) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [matrixProjectiveConjugation_mk, projectiveEquiv_mk, projectiveEquiv_mk,
    projectiveSemilinearConjugation_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact matrixConjugation_vector g.val A.val v

theorem mulAutCongr_conjugation_linear (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) (hg : g.val.right = 1) :
    MulAut.congr (projectiveEquiv Q hQ) (matrixProjectiveConjugation Q g) =
      projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
        (matrix_similarity Q g hg) := by
  apply MulEquiv.ext
  intro y
  change projectiveEquiv Q hQ (matrixProjectiveConjugation Q g ((projectiveEquiv Q hQ).symm y)) = _
  rw [projectiveEquiv_conjugation_linear Q hQ g hg, MulEquiv.apply_symm_apply]

theorem mulAutCongr_conjugation (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) :
    MulAut.congr (projectiveEquiv Q hQ) (matrixProjectiveConjugation Q g) =
      projectiveSemilinearConjugation Q g.val.right (coordinateSemilinearMap g.val)
        (multiplier Q g) (coordinateSemilinearMap_smul g.val) (multiplier_spec Q g) := by
  apply MulEquiv.ext
  intro y
  change projectiveEquiv Q hQ (matrixProjectiveConjugation Q g ((projectiveEquiv Q hQ).symm y)) = _
  rw [projectiveEquiv_conjugation, MulEquiv.apply_symm_apply]

theorem fixedSubgroup_map_of_intertwining {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : ∀ x, e (α x) = β (e x)) :
    (FixedCommutingProduct.fixedSubgroup α).map e.toMonoidHom =
      FixedCommutingProduct.fixedSubgroup β := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change α (e.symm y) = e.symm y ↔ β y = y
  rw [← e.apply_eq_iff_eq, h, e.apply_symm_apply]

@[expose] def fixedEquivOfIntertwining {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : ∀ x, e (α x) = β (e x)) :
    FixedCommutingProduct.fixedSubgroup α ≃* FixedCommutingProduct.fixedSubgroup β :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (fixedSubgroup_map_of_intertwining e α β h))

theorem fixedEquivOfIntertwining_val {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : ∀ x, e (α x) = β (e x))
    (x : FixedCommutingProduct.fixedSubgroup α) :
    (fixedEquivOfIntertwining e α β h x).val = e x.val := rfl

@[expose] def linearFixedEquiv (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) (hg : g.val.right = 1) :
    FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g) ≃*
      FixedCommutingProduct.fixedSubgroup (projectiveConjugation Q (matrixLinearEquiv g.val.left)
        (multiplier Q g) (matrix_similarity Q g hg)) :=
  fixedEquivOfIntertwining (projectiveEquiv Q hQ) _ _
    (projectiveEquiv_conjugation_linear Q hQ g hg)

theorem linearFixedEquiv_val (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) (hg : g.val.right = 1)
    (x : FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)) :
    (linearFixedEquiv Q hQ g hg x).val = projectiveEquiv Q hQ x.val := rfl

@[expose] def semilinearFixedEquiv (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) :
    FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g) ≃*
      FixedCommutingProduct.fixedSubgroup (projectiveSemilinearConjugation Q g.val.right
        (coordinateSemilinearMap g.val) (multiplier Q g) (coordinateSemilinearMap_smul g.val)
        (multiplier_spec Q g)) :=
  fixedEquivOfIntertwining (projectiveEquiv Q hQ) _ _ (projectiveEquiv_conjugation Q hQ g)

theorem semilinearFixedEquiv_val (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q)
    (x : FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)) :
    (semilinearFixedEquiv Q hQ g x).val = projectiveEquiv Q hQ x.val := rfl

theorem exists_ne_zero_of_polarBilin_nondegenerate (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (hd : 0 < d) : ∃ v, Q v ≠ 0 := by
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; exact hd)
  by_contra h
  have hzero : ∀ v, Q v = 0 := not_exists_not.mp h
  apply hQ.1.ne_zero
  ext x y
  simp [QuadraticMap.polar, hzero]

theorem eq_scalar_of_matrixLinearEquiv_apply (A : GL (Fin d) K) (b : Kˣ)
    (h : ∀ x, matrixLinearEquiv A x = (b : K) • x) :
    A = GeneralLinearGroup.scalar (Fin d) b := by
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro x
  exact (h x).trans (matrixLinearEquiv_scalar b x).symm

theorem matrixLinearEquiv_ne_smul_one (A : GL (Fin d) K)
    (hA : ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ A) (a : K) :
    (matrixLinearEquiv A).toLinearMap ≠ a • (1 : Module.End K (Fin d → K)) := by
  intro h
  have happly : ∀ x, matrixLinearEquiv A x = a • x := fun x => LinearMap.congr_fun h x
  by_cases ha : a = 0
  · refine hA 1 (eq_scalar_of_matrixLinearEquiv_apply A 1 fun x => ?_).symm
    have hx : x = 0 := (matrixLinearEquiv A).injective (by rw [happly, ha, zero_smul, map_zero])
    rw [hx, map_zero, smul_zero]
  · exact hA (Units.mk0 a ha) (eq_scalar_of_matrixLinearEquiv_apply A _ happly).symm

theorem coordinateSemilinearMap_sq_apply (g : coordinateSemilinearGroup d K) (c : Kˣ)
    (hsigma : g.right ^ 2 = 1)
    (hsquare : g.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.right g.left =
      GeneralLinearGroup.scalar (Fin d) c) (x : Fin d → K) :
    coordinateSemilinearMap g (coordinateSemilinearMap g x) = (c : K) • x := by
  have hright : (g * g).right = 1 := by
    rw [coordinateSemilinearGroup_mul_field, ← sq, hsigma]
  rw [← coordinateSemilinearMap_mul, coordinateSemilinearMap_eq_matrix (g * g) hright,
    coordinateSemilinearGroup_mul_matrix, hsquare]
  exact matrixLinearEquiv_scalar c x

variable [Finite K]

theorem linear_fixed_pComponent_quasisimple
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (hd : 2 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hg : g.val.right = 1) (c : Kˣ)
    (hsquare : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x)
    (hnonscalar : ∀ a : K,
      (matrixLinearEquiv g.val.left).toLinearMap ≠ a • (1 : Module.End K (Fin d → K))) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have hn : 2 ≤ Module.finrank K (Fin d → K) := by rw [Module.finrank_fin_fun]; exact hd
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (linearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)) g hg)
    ((odd_orthogonal_linear_involution_fixed_p_components ℓ f hℓ hodd hf hcard hn Q hQ
      (matrixLinearEquiv g.val.left) c (multiplier Q g) hsquare (matrix_similarity Q g hg)
      hnonscalar).2 p hp) L hL

theorem semilinear_fixed_pComponent_quasisimple
    (hodd : Odd (Nat.card K)) (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q)
    (hsigma : g.val.right ^ 2 = 1) (hne : g.val.right ≠ 1) (lambda : Kˣ)
    (hsquare : ∀ x, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val x) =
      (lambda : K) • x) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have hdim : 0 < Module.finrank K (Fin d → K) := by rw [Module.finrank_fin_fun]; exact hd
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (semilinearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd) g)
    ((odd_orthogonal_field_involution_fixed_p_components hodd g.val.right hsigma hne hdim Q hQ
      (coordinateSemilinearMap g.val) (multiplier Q g) lambda
      (coordinateSemilinearMap_smul g.val) (multiplier_spec Q g) hsquare).2 p hp) L hL

theorem linear_fixed_pComponent_quasisimple_of_matrix
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (hd : 2 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hg : g.val.right = 1) (c : Kˣ)
    (hsquare : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin d) c)
    (hnonscalar : ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg, one_pow]) hsquare x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg] at h
  exact linear_fixed_pComponent_quasisimple ℓ f hℓ hodd hf hcard hd Q hQ g hg c hsq
    (matrixLinearEquiv_ne_smul_one g.val.left hnonscalar)

theorem semilinear_fixed_pComponent_quasisimple_of_matrix
    (hodd : Odd (Nat.card K)) (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q)
    (hsigma : g.val.right ^ 2 = 1) (hne : g.val.right ≠ 1) (c : Kˣ)
    (hsquare : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin d) c) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L :=
  semilinear_fixed_pComponent_quasisimple hodd hd Q hQ g hsigma hne c
    (coordinateSemilinearMap_sq_apply g.val c hsigma hsquare)

theorem fixed_pComponent_quasisimple_of_matrix
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (hd : 2 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hsigma : g.val.right ^ 2 = 1) (c : Kˣ)
    (hsquare : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin d) c)
    (hnonscalar : g.val.right = 1 → ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  by_cases hg : g.val.right = 1
  · exact linear_fixed_pComponent_quasisimple_of_matrix ℓ f hℓ hodd hf hcard hd Q hQ g hg c
      hsquare (hnonscalar hg)
  · have hKodd : Odd (Nat.card K) := by
      rw [hcard]
      exact (hℓ.odd_of_ne_two hodd).pow
    exact semilinear_fixed_pComponent_quasisimple_of_matrix hKodd (by omega) Q hQ g hsigma hg c
      hsquare

end CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
