module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace GenLocL3NFLin

open Module Module.End Matrix

theorem isPrimitiveRoot_neg_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    IsPrimitiveRoot (-1 : F) 2 := by
  have hne : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  refine ⟨by norm_num, fun l hl => ?_⟩
  have := (neg_one_pow_eq_one_iff_even hne).1 hl
  exact even_iff_two_dvd.1 this

theorem exists_orthogonal_common_eigenbasis {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) {B : LinearMap.BilinForm F V} (hB : LinearMap.IsSymm B)
    {ι : Type*} [Finite ι] (g : ι → End F V) (hcomm : ∀ i j, Commute (g i) (g j))
    (hsq : ∀ i, g i ^ 2 = 1) (hiso : ∀ i v w, B (g i v) (g i w) = B v w) :
    ∃ (b : Basis (Fin (finrank F V)) F V) (μ : ι → Fin (finrank F V) → F),
      (∀ i j, g i (b j) = μ i j • b j) ∧ ∀ i j, i ≠ j → B (b i) (b j) = 0 := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hζ := isPrimitiveRoot_neg_one h2
  have : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hss := fun i => CFSG.RankThree.PartOne.isSemisimple_of_pow_eq_one hζ (hsq i)
  have hspan : ∀ i, ⨆ μ, (g i).maxGenEigenspace μ = ⊤ := fun i =>
    ((hss i).iSup_maxGenEigenspace_eq_top_iff).2
      (CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ (hsq i))
  set W : (ι → F) → Submodule F V := fun χ => ⨅ i, (g i).maxGenEigenspace (χ i) with hWdef
  have hW : ∀ (χ : ι → F) (i : ι), (g i).maxGenEigenspace (χ i) = (g i).eigenspace (χ i) :=
    fun χ i => (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have htop : ⨆ χ, W χ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute g
      (fun i j _ => hcomm i j) hspan
  have hind : iSupIndep W :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo g
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmem : ∀ (χ : ι → F) (i : ι) {v : V}, v ∈ W χ → g i v = χ i • v := fun χ i v hv => by
    have hi := (Submodule.mem_iInf _).mp hv i
    rw [hW] at hi
    exact mem_eigenspace_iff.mp hi
  have hev2 : ∀ (χ : ι → F) (i : ι) {v : V}, v ∈ W χ → v ≠ 0 → χ i * χ i = 1 := by
    intro χ i v hv hv0
    have hev : (g i).HasEigenvector (χ i) v := ⟨mem_eigenspace_iff.mpr (hmem χ i hv), hv0⟩
    have h1 := hev.pow_apply 2
    rw [hsq i, Module.End.one_apply] at h1
    have h2' : (χ i ^ 2 - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    have := sub_eq_zero.mp ((smul_eq_zero.mp h2').resolve_right hv0)
    rw [← sq]
    exact this
  have horth : ∀ {χ ψ : ι → F}, χ ≠ ψ → ∀ {v w : V}, v ∈ W χ → w ∈ W ψ → B v w = 0 := by
    intro χ ψ hne v w hv hw
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have e1 : B v w = (χ i * ψ i) * B v w := by
      have h3 := hiso i v w
      rw [hmem χ i hv, hmem ψ i hw] at h3
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
      linear_combination -h3
    have hχ := hev2 χ i hv hv0
    have hψ := hev2 ψ i hw hw0
    have hprod : χ i * ψ i = -1 := by
      rcases mul_self_eq_one_iff.mp hχ with h | h <;> rcases mul_self_eq_one_iff.mp hψ with h' | h'
      · exact absurd (h.trans h'.symm) hi
      · rw [h, h']; ring
      · rw [h, h']; ring
      · exact absurd (h.trans h'.symm) hi
    rw [hprod] at e1
    have h4 : (2 : F) * B v w = 0 := by linear_combination e1
    exact (mul_eq_zero.mp h4).resolve_left h2
  choose e he using fun χ => LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.IsSymm.domRestrict hB (W χ))
  let b₀ := hint.collectedBasis e
  have : Finite (Σ χ, Fin (finrank F (W χ))) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Fin (finrank F (W χ))) ≃ Fin (finrank F V) :=
    (Finite.equivFin _).trans (finCongr (finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_, fun i j hij => ?_⟩
  · have hm : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem e (e₀.symm j)
    rw [Basis.reindex_apply]
    exact hmem _ i hm
  · rw [Basis.reindex_apply, Basis.reindex_apply]
    obtain ⟨⟨χ, a⟩, hχa⟩ : ∃ z, z = e₀.symm i := ⟨_, rfl⟩
    obtain ⟨⟨ψ, c⟩, hψc⟩ : ∃ z, z = e₀.symm j := ⟨_, rfl⟩
    rw [← hχa, ← hψc]
    have hb1 : b₀ ⟨χ, a⟩ = (e χ a : V) := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
    have hb2 : b₀ ⟨ψ, c⟩ = (e ψ c : V) := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
    rw [hb1, hb2]
    by_cases hχψ : χ = ψ
    · subst hχψ
      have hac : a ≠ c := by
        rintro rfl
        apply hij
        apply e₀.symm.injective
        rw [← hχa, ← hψc]
      have := he χ hac
      simpa [Function.onFun, LinearMap.domRestrict₁₂_apply] using this
    · exact horth hχψ (e χ a).2 (e ψ c).2

theorem exists_orth_conj_diag {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) F) (hS : Sᵀ = S) {ι : Type*} [Finite ι] (R : ι → GL (Fin n) F)
    (hcomm : ∀ i j, R i * R j = R j * R i) (hsq : ∀ i, R i * R i = 1)
    (hiso : ∀ i, ((R i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * S *
      ((R i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = S) :
    ∃ C : GL (Fin n) F, (∀ i, ((C⁻¹ * R i * C : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) ∧
      ((C : Matrix (Fin n) (Fin n) F)ᵀ * S * (C : Matrix (Fin n) (Fin n) F)).IsDiag := by
  classical
  let g : ι → End F (Fin n → F) := fun i => Matrix.toLinAlgEquiv' ((R i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hg_comm : ∀ i j, Commute (g i) (g j) := fun i j => by
    have h := congrArg Units.val (hcomm i j)
    simp only [Units.val_mul] at h
    show g i * g j = g j * g i
    simp only [g, ← map_mul, h]
  have hg_sq : ∀ i, g i ^ 2 = 1 := fun i => by
    have h := congrArg Units.val (hsq i)
    simp only [Units.val_mul, Units.val_one] at h
    simp only [g, sq, ← map_mul, h, map_one]
  have hB : LinearMap.IsSymm (Matrix.toBilin' S) := ⟨fun x y => by
    simp only [RingHom.id_apply, Matrix.toBilin'_apply']
    rw [dotProduct_comm, ← vecMul_transpose, hS, dotProduct_mulVec]⟩
  have hg_iso : ∀ i v w, Matrix.toBilin' S (g i v) (g i w) = Matrix.toBilin' S v w := fun i v w => by
    simp only [g, Matrix.toBilin'_apply', Matrix.toLinAlgEquiv'_apply]
    rw [← Matrix.vecMul_transpose (R i : Matrix (Fin n) (Fin n) F) v, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hiso i]
  obtain ⟨b, μ, hb, hbo⟩ := exists_orthogonal_common_eigenbasis h2 hB g hg_comm hg_sq hg_iso
  let e := finCongr (Module.finrank_fin_fun (n := n) F)
  let b' : Module.Basis (Fin n) F (Fin n → F) := b.reindex e
  have hb' : ∀ i j, g i (b' j) = μ i (e.symm j) • b' j := fun i j => by
    simp only [b', Basis.reindex_apply]
    exact hb i _
  let P : Matrix (Fin n) (Fin n) F := (Pi.basisFun F (Fin n)).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun F (Fin n)) b'
  let Pu : GL (Fin n) F := unitOfInvertible P
  refine ⟨Pu, fun i => ?_, ?_⟩
  · have hxP : ((R i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * P =
        P * diagonal (fun j => μ i (e.symm j)) := by
      ext a j
      have h := congrFun (hb' i j) a
      simp only [g, Matrix.toLinAlgEquiv'_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [Matrix.mul_diagonal]
      simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
      rw [mul_comm]
      simpa [Matrix.mulVec, dotProduct] using h
    have h1 : ((Pu⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = ⅟P := rfl
    have h2' : ((Pu : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = P := rfl
    intro a j hij
    rw [Units.val_mul, Units.val_mul, h1, h2', Matrix.mul_assoc, hxP, ← Matrix.mul_assoc,
      invOf_mul_self, Matrix.one_mul, diagonal_apply_ne _ hij]
  · intro i j hij
    have h1 := hbo (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
    simp only [Matrix.toBilin'_apply'] at h1
    have h3 : (Pu : Matrix (Fin n) (Fin n) F) = P := rfl
    rw [h3]
    have h4 : (Pᵀ * S * P) i j = b' i ⬝ᵥ (S *ᵥ b' j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Basis.toMatrix_apply, Pi.basisFun_repr,
        Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [h4]
    simpa [b', Basis.reindex_apply, Matrix.mulVec, dotProduct] using h1

theorem exists_orth_conj_diag_sub {K : Type*} [Field K] (L : Subfield K) (h2 : (2 : K) ≠ 0) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) K) (hS : Sᵀ = S) (hSL : ∀ i j, S i j ∈ L)
    {α : Type*} [Finite α] (R : α → GL (Fin n) K)
    (hRL : ∀ a i j, ((R a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ L)
    (hcomm : ∀ a b, R a * R b = R b * R a) (hsq : ∀ a, R a * R a = 1)
    (hiso : ∀ a, ((R a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * S *
      ((R a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = S) :
    ∃ C : GL (Fin n) K, (∀ i j, ((C : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ L) ∧
      (∀ a, ((C⁻¹ * R a * C : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) ∧
      ((C : Matrix (Fin n) (Fin n) K)ᵀ * S * (C : Matrix (Fin n) (Fin n) K)).IsDiag := by
  classical
  let ι : ↥L →+* K := L.subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) ↥L => M.map ι) :=
    Matrix.map_injective hι
  let S0 : Matrix (Fin n) (Fin n) ↥L := Matrix.of fun i j => ⟨S i j, hSL i j⟩
  let R0 : α → Matrix (Fin n) (Fin n) ↥L := fun a => Matrix.of fun i j => ⟨(R a : Matrix (Fin n) (Fin n) K) i j, hRL a i j⟩
  have hS0 : S0.map ι = S := by ext i j; rfl
  have hR0 : ∀ a, (R0 a).map ι = (R a : Matrix (Fin n) (Fin n) K) := fun a => by ext i j; rfl
  have h2L : (2 : ↥L) ≠ 0 := by
    intro h
    apply h2
    have h3 := map_ofNat ι 2
    rw [h, map_zero] at h3
    exact h3.symm
  have hcomm0 : ∀ a b, R0 a * R0 b = R0 b * R0 a := fun a b => by
    apply hinj
    simp only [Matrix.map_mul, hR0]
    have h := congrArg Units.val (hcomm a b)
    simpa only [Units.val_mul] using h
  have hsq0 : ∀ a, R0 a * R0 a = 1 := fun a => by
    apply hinj
    simp only [Matrix.map_mul, hR0, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have h := congrArg Units.val (hsq a)
    simpa only [Units.val_mul, Units.val_one] using h
  let R1 : α → GL (Fin n) ↥L := fun a => ⟨R0 a, R0 a, hsq0 a, hsq0 a⟩
  have hS1 : S0ᵀ = S0 := by
    apply hinj
    show S0ᵀ.map ι = S0.map ι
    rw [Matrix.transpose_map, hS0, hS]
  have hiso0 : ∀ a, ((R1 a : GL (Fin n) ↥L) : Matrix (Fin n) (Fin n) ↥L)ᵀ * S0 *
      ((R1 a : GL (Fin n) ↥L) : Matrix (Fin n) (Fin n) ↥L) = S0 := fun a => by
    apply hinj
    show ((R0 a)ᵀ * S0 * R0 a).map ι = S0.map ι
    simp only [Matrix.map_mul, hS0, hR0]
    exact hiso a
  obtain ⟨C0, hC0, hC0S⟩ := exists_orth_conj_diag h2L S0 hS1 R1 (fun a b => Units.ext (hcomm0 a b))
    (fun a => Units.ext (hsq0 a)) hiso0
  let f : GL (Fin n) ↥L →* GL (Fin n) K := Units.map (RingHom.mapMatrix ι : Matrix (Fin n) (Fin n) ↥L →+* Matrix (Fin n) (Fin n) K).toMonoidHom
  have hfv : ∀ X : GL (Fin n) ↥L, ((f X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((X : GL (Fin n) ↥L) : Matrix (Fin n) (Fin n) ↥L).map ι := fun X => rfl
  refine ⟨f C0, fun i j => ?_, fun a => ?_, ?_⟩
  · rw [hfv]; exact (C0 : Matrix (Fin n) (Fin n) ↥L) i j |>.2
  · have : (f C0)⁻¹ * R a * f C0 = f (C0⁻¹ * R1 a * C0) := by
      rw [map_mul, map_mul, map_inv]
      congr 2
      exact Units.ext (hR0 a).symm
    rw [this, hfv]
    exact (hC0 a).map (map_zero ι)
  · have : ((f C0 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * S * (f C0 : Matrix (Fin n) (Fin n) K) =
        ((C0 : Matrix (Fin n) (Fin n) ↥L)ᵀ * S0 * (C0 : Matrix (Fin n) (Fin n) ↥L)).map ι := by
      rw [hfv, Matrix.map_mul, Matrix.map_mul, ← Matrix.transpose_map, hS0]
    rw [this]
    exact hC0S.map (map_zero ι)

end GenLocL3NFLin

end CFSG.GH74.Generic.BProg.B2
