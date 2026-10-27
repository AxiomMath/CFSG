module

public import CFSG.CharacterTheory.BrauerLinearThree.NineLocal

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem eq_top_of_mem_GL2 (H : Subgroup (GL (Fin 2) F)) (hup : ∀ c, upperGL c ∈ H)
    (hlow : ∀ c, lowerGL c ∈ H) (hdiag : ∀ a b, diagGL a b ∈ H) (hsw : swapGL ∈ H) :
    H = ⊤ := by
  have hLDU : ∀ A : GL (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 → A ∈ H := by
    intro A h00
    have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    have hd : (A : Matrix (Fin 2) (Fin 2) F).det / (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
      div_ne_zero hdet h00
    have hA : A = lowerGL ((A : Matrix (Fin 2) (Fin 2) F) 1 0 /
        (A : Matrix (Fin 2) (Fin 2) F) 0 0) * diagGL (Units.mk0 _ h00) (Units.mk0 _ hd) *
          upperGL ((A : Matrix (Fin 2) (Fin 2) F) 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerGL, upperGL, diagGL, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.det_fin_two] <;>
        (field_simp; try ring)
    rw [hA]
    exact H.mul_mem (H.mul_mem (hlow _) (hdiag _ _)) (hup _)
  rw [eq_top_iff]
  intro A _
  by_cases h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  ·
    have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    rw [Matrix.det_fin_two, h00, zero_mul, zero_sub, neg_ne_zero] at hdet
    have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := right_ne_zero_of_mul hdet
    have hWA : ((swapGL * A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      simpa [swapGL, Matrix.mul_apply, Fin.sum_univ_two] using h10
    have h := H.mul_mem hsw (hLDU _ hWA)
    rwa [← mul_assoc, swapGL_mul_self, one_mul] at h
  · exact hLDU A h00

omit [Finite F] in
theorem swapGL_eq :
    (swapGL : GL (Fin 2) F) = upperGL 1 * lowerGL (-1) * upperGL 1 * diagGL (-1) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapGL, upperGL, lowerGL, diagGL, Matrix.mul_apply, Fin.sum_univ_two]

omit [Finite F] in
include φ hZ hZodd h2 hJ in
theorem J_eq_sq : ∃ x : G, J * x = x * J ∧ x * x = J := by
  let K : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by simp [det_fin_two])
  refine ⟨linearCentralizerHom φ K, linearCentralizerHom_commute φ K, ?_⟩
  have hK : K * K = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.mul_apply, Fin.sum_univ_two]
  calc linearCentralizerHom φ K * linearCentralizerHom φ K = linearCentralizerHom φ (K * K) :=
        (map_mul _ _ _).symm
    _ = linearCentralizerHom φ (-1) := by rw [hK]
    _ = J := linearCentralizerHom_neg_one φ hZ hZodd h2 hJ

include hZ hZodd h2 hJ in
theorem index_ne_two_of_conj [Finite G] (hq : Nat.card F % 4 = 3)
    (hconj : ∃ g : G, g * J * g⁻¹ = invJ₁ φ) (U : Subgroup G) : U.index ≠ 2 := by
  intro hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero (2 : F) := ⟨h2⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hsq : ∀ a : G, a * a ∈ U := Subgroup.mul_self_mem_of_index_two hU
  have hn : U.Normal := Subgroup.normal_of_index_eq_two hU
  obtain ⟨x, -, hx⟩ := J_eq_sq φ hZ hZodd h2 hJ
  have hJU : J ∈ U := by rw [← hx]; exact hsq x
  obtain ⟨g, hg⟩ := hconj
  have hJ₁U : invJ₁ φ ∈ U := by rw [← hg]; exact hn.conj_mem J hJU g
  have hJ₂U : invJ₂ φ ∈ U := by
    rw [invJ₂_eq φ hZ hZodd h2 hJ]
    exact U.mul_mem hJU hJ₁U
  set H := U.comap (linearCentralizerHom φ) with hH
  have hup : ∀ c, upperGL c ∈ H := by
    intro c
    show linearCentralizerHom φ (upperGL c) ∈ U
    have h := hsq (linearCentralizerHom φ (upperGL (c / 2)))
    rwa [← map_mul, upperGL_add, add_halves] at h
  have hlow : ∀ c, lowerGL c ∈ H := by
    intro c
    show linearCentralizerHom φ (lowerGL c) ∈ U
    have h := hsq (linearCentralizerHom φ (lowerGL (c / 2)))
    rwa [← map_mul, lowerGL_add, add_halves] at h
  have hdiag : ∀ a b, diagGL a b ∈ H := by
    intro a b
    show linearCentralizerHom φ (diagGL a b) ∈ U
    obtain ⟨ε₁, c₁, hε₁, rfl⟩ := exists_sign_mul_sq h2 hq a
    obtain ⟨ε₂, c₂, hε₂, rfl⟩ := exists_sign_mul_sq h2 hq b
    have hsplit : linearCentralizerHom φ (diagGL (ε₁ * c₁ ^ 2) (ε₂ * c₂ ^ 2)) =
        linearCentralizerHom φ (diagGL ε₁ ε₂) *
          (linearCentralizerHom φ (diagGL c₁ c₂) * linearCentralizerHom φ (diagGL c₁ c₂)) := by
      rw [← map_mul, ← map_mul, diagGL_mul, diagGL_mul, sq, sq]
    rw [hsplit]
    refine U.mul_mem ?_ (hsq _)
    rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
    · rw [diagGL_one_one, map_one]; exact U.one_mem
    · exact hJ₁U
    · exact hJ₂U
    · rw [← neg_one_eq_diagGL, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ]; exact hJU
  have hsw : swapGL ∈ H := by
    rw [swapGL_eq]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hup 1) (hlow (-1))) (hup 1)) (hdiag _ _)
  have htop := eq_top_of_mem_GL2 H hup hlow hdiag hsw
  have hCU : Subgroup.centralizer ({J} : Set G) ≤ U := by
    intro y hy
    obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ
      (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    have : A ∈ H := by rw [htop]; exact Subgroup.mem_top A
    exact this
  obtain ⟨SC⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({J} : Set G))) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC rfl
  have hSU : (S : Subgroup G) ≤ U := by
    rw [hS]
    exact (Subgroup.map_subtype_le _).trans hCU
  have hdvd := Subgroup.index_dvd_of_le hSU
  rw [hU] at hdvd
  exact S.not_dvd_index hdvd

end CFSG.BrauerLinearThree
