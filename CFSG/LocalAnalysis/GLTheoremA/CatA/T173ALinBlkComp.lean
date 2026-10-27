module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinSL
import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open Matrix CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped MatrixGroups

private theorem linSL_eq_range_toGL (d : ℕ) (F : Type) [Field F] :
    LinSL d F = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin d) F →* GL (Fin d) F).range := by
  change LargeEvenSLGroup (Fin d) F = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin d) F →* GL (Fin d) F).range
  rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.statedSL_eq_range_toGL]

private noncomputable def linSLIso (d : ℕ) (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin d) F ≃* ↥(LinSL d F) :=
  (MonoidHom.ofInjective (f := (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin d) F →* GL (Fin d) F))
    Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (linSL_eq_range_toGL d F).symm)

private theorem linSLIso_coe_apply {d : ℕ} {F : Type} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin d) F) :
    ((linSLIso d F g : ↥(LinSL d F)) : GL (Fin d) F) =
      Matrix.SpecialLinearGroup.toGL g := rfl

private theorem linSLIso_matrix_apply {d : ℕ} {F : Type} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin d) F) :
    (((linSLIso d F g : ↥(LinSL d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (g : Matrix (Fin d) (Fin d) F) := by
  rw [linSLIso_coe_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

private theorem linSLIso_symm_coe_apply {d : ℕ} {F : Type} [Field F]
    (z : ↥(LinSL d F)) :
    Matrix.SpecialLinearGroup.toGL ((linSLIso d F).symm z) = (z : GL (Fin d) F) := by
  have h := linSLIso_coe_apply ((linSLIso d F).symm z)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private theorem linSLIso_symm_matrix_apply {d : ℕ} {F : Type} [Field F]
    (z : ↥(LinSL d F)) :
    (((linSLIso d F).symm z : Matrix.SpecialLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = ((z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
  show ((Matrix.SpecialLinearGroup.toGL ((linSLIso d F).symm z) : GL (Fin d) F) :
    Matrix (Fin d) (Fin d) F) = ((z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  exact congrArg (fun w : GL (Fin d) F => (w : Matrix (Fin d) (Fin d) F))
    (linSLIso_symm_coe_apply z)

private theorem linMk_ker_le_center (d : ℕ) (F : Type) [Field F] :
    (LinMk d F).ker ≤ Subgroup.center ↥(LinSL d F) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hz' : (z : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
    have h : z ∈ (QuotientGroup.mk'
        ((LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F))).ker := hz
    rw [QuotientGroup.ker_mk'] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hc : (z : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) := by
    rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact hz'
  exact Subgroup.mem_center_iff.mp hc (w : GL (Fin d) F)

private theorem linMk_comp_ker_le_center (d : ℕ) (F : Type) [Field F] :
    ((LinMk d F).comp (linSLIso d F).toMonoidHom).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' : (linSLIso d F) x ∈ (LinMk d F).ker := hx
  have hc := linMk_ker_le_center d F hx'
  apply (linSLIso d F).injective
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hc ((linSLIso d F) y)

private theorem coe_eq_diagonal_of_offDiag {d : ℕ} {F : Type} [Field F]
    {a : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) :
    (a : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (a : Matrix (Fin d) (Fin d) F) i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.diagonal_apply_ne _ hij, hadiag i j hij]

private theorem coordBlockSL_le_centralizer_diag {d : ℕ} {F : Type} [Field F]
    {a : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    {I : Finset (Fin d)}
    (hI : ∃ c : F, ∀ i : Fin d, i ∈ I ↔ (a : Matrix (Fin d) (Fin d) F) i i = c) :
    coordBlockSL F I ≤
      Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin d) F)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ha := coe_eq_diagonal_of_offDiag hadiag
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ha,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij; exact mul_comm _ _
  · by_cases hiI : i ∈ I
    · by_cases hjI : j ∈ I
      · rw [(hI.choose_spec i).mp hiI, (hI.choose_spec j).mp hjI]
        exact mul_comm _ _
      · rw [mem_coordBlockSL_iff.mp hg i j (Or.inr hjI), if_neg hij, zero_mul, mul_zero]
    · rw [mem_coordBlockSL_iff.mp hg i j (Or.inl hiI), if_neg hij, zero_mul, mul_zero]

private theorem entry_eq_zero_of_commute_diag {d : ℕ} {F : Type} [Field F]
    {a g : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (hg : g * a = a * g) {i j : Fin d}
    (hij : (a : Matrix (Fin d) (Fin d) F) i i ≠ (a : Matrix (Fin d) (Fin d) F) j j) :
    (g : Matrix (Fin d) (Fin d) F) i j = 0 := by
  have ha := coe_eq_diagonal_of_offDiag hadiag
  have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin d) F =>
    (x : Matrix (Fin d) (Fin d) F) i j) hg
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ha,
    Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : ((a : Matrix (Fin d) (Fin d) F) i i - (a : Matrix (Fin d) (Fin d) F) j j) *
      (g : Matrix (Fin d) (Fin d) F) i j = 0 := by
    rw [sub_mul, ← h, mul_comm]
    ring
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hij
  · exact h0

private theorem compIndicator_comm_of_commute_diag {d : ℕ} {F : Type} [Field F]
    {a y : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    {I : Finset (Fin d)}
    (hI : ∃ c : F, ∀ i : Fin d, i ∈ I ↔ (a : Matrix (Fin d) (Fin d) F) i i = c)
    (hy : y * a = a * y) :
    compIndicator F I * (y : Matrix (Fin d) (Fin d) F) =
      (y : Matrix (Fin d) (Fin d) F) * compIndicator F I := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i ∈ I
  · by_cases hj : j ∈ I
    · simp [hi, hj]
    · have hne : (a : Matrix (Fin d) (Fin d) F) i i ≠
          (a : Matrix (Fin d) (Fin d) F) j j := by
        rw [(hI.choose_spec i).mp hi]
        exact fun h => hj ((hI.choose_spec j).mpr h.symm)
      rw [entry_eq_zero_of_commute_diag hadiag hy hne]
      simp [hi, hj]
  · by_cases hj : j ∈ I
    · have hne : (a : Matrix (Fin d) (Fin d) F) i i ≠
          (a : Matrix (Fin d) (Fin d) F) j j := by
        rw [(hI.choose_spec j).mp hj]
        exact fun h => hi ((hI.choose_spec i).mpr h)
      rw [entry_eq_zero_of_commute_diag hadiag hy hne]
      simp [hi, hj]
    · simp [hi, hj]

private theorem coordBlockSL_normal_subgroupOf_centralizer_diag {d : ℕ} {F : Type} [Field F]
    {a : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    {I : Finset (Fin d)}
    (hI : I.Nonempty ∧ ∃ c : F, ∀ i : Fin d, i ∈ I ↔
      (a : Matrix (Fin d) (Fin d) F) i i = c) :
    ((coordBlockSL F I).subgroupOf
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin d) F)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (coordBlockSL_le_centralizer_diag hadiag hI.2)]
  intro s y hs hy
  have hyc : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  exact conj_mem_coordBlockSL (compIndicator_comm_of_commute_diag hadiag hI.2 hyc) hs

private theorem isComponentOf_coordBlockSL_centralizer_diag {d : ℕ} {F : Type} [Field F]
    [Finite F] {a : Matrix.SpecialLinearGroup (Fin d) F}
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    {I : Finset (Fin d)}
    (hI : I.Nonempty ∧ ∃ c : F, ∀ i : Fin d, i ∈ I ↔
      (a : Matrix (Fin d) (Fin d) F) i i = c)
    (hcard : 2 ≤ I.card) (h4 : 4 ≤ Nat.card F) :
    CFSG.Open.IsComponentOf (coordBlockSL F I)
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin d) F))) := by
  have hle := coordBlockSL_le_centralizer_diag hadiag hI.2
  exact ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle
    (coordBlockSL_normal_subgroupOf_centralizer_diag hadiag hI),
    isQuasisimple_coordBlockSL hcard h4⟩

theorem lin_block_component {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {a : ↥(LinSL d F)}
    (hdiag : ∀ i j : Fin d, i ≠ j → ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0)
    (ha1 : LinMk d F a ≠ 1)
    (hC : ∀ g : ↥(LinSL d F),
      LinMk d F g ∈ Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F)) →
        (g : GL (Fin d) F) * a = a * g)
    {I : Finset (Fin d)} (hI : LinLevelSet (a : GL (Fin d) F) I) (hcard : 2 ≤ I.card) :
    CFSG.Open.IsComponentOf (LinBlockSub d F I)
      (Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F))) := by
  classical
  let a₀ : Matrix.SpecialLinearGroup (Fin d) F := (linSLIso d F).symm a
  have ha₀ : (linSLIso d F) a₀ = a := MulEquiv.apply_symm_apply (linSLIso d F) a
  have ha₀mat : (a₀ : Matrix (Fin d) (Fin d) F) =
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := linSLIso_symm_matrix_apply a
  have hdiag₀ : ∀ i j : Fin d, i ≠ j → (a₀ : Matrix (Fin d) (Fin d) F) i j = 0 := by
    intro i j hij
    rw [ha₀mat]
    exact hdiag i j hij
  have hI₀ : I.Nonempty ∧ ∃ c : F, ∀ i : Fin d, i ∈ I ↔
      (a₀ : Matrix (Fin d) (Fin d) F) i i = c := by
    obtain ⟨hne, c, hc⟩ := hI
    exact ⟨hne, c, fun i => by rw [ha₀mat]; exact hc i⟩
  have h4 : 4 ≤ Nat.card F := by
    have hn : 2 ≤ n := h.2.2.2.2.2.1
    have h2n : (4 : ℕ) ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [h.2.2.2.2.1]
    exact h2n
  have hfix : CFSG.ClassicalInvolution.Balance.fixedGroup (MulAut.conj a₀) =
      Subgroup.centralizer ({a₀} : Set (Matrix.SpecialLinearGroup (Fin d) F)) := by
    ext y
    rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy; rw [mul_inv_eq_iff_eq_mul] at hy; exact hy.symm
    · intro hy; rw [mul_inv_eq_iff_eq_mul]; exact hy.symm
  have hQ : CFSG.Open.IsComponentOf (coordBlockSL F I)
      (CFSG.ClassicalInvolution.Balance.fixedGroup (MulAut.conj a₀)) := by
    rw [hfix]
    exact isComponentOf_coordBlockSL_centralizer_diag hdiag₀ hI₀ hcard h4
  let Ψ : Matrix.SpecialLinearGroup (Fin d) F →* LinPSL d F :=
    (LinMk d F).comp (linSLIso d F).toMonoidHom
  have hδ' : ∀ y : Matrix.SpecialLinearGroup (Fin d) F,
      Ψ a₀ * Ψ y * (Ψ a₀)⁻¹ = Ψ (a₀ * y * a₀⁻¹) := by
    intro y
    rw [map_mul, map_mul, map_inv]
  have hδ : ∀ y : Matrix.SpecialLinearGroup (Fin d) F,
      Ψ a₀ * Ψ (1 * y * 1⁻¹) * (Ψ a₀)⁻¹ = Ψ (1 * (MulAut.conj a₀) y * 1⁻¹) := by
    intro y
    simpa [MulAut.conj_apply] using hδ' y
  have hker : Ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) :=
    linMk_comp_ker_le_center d F
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer
    (K := Matrix.SpecialLinearGroup (Fin d) F) (X := LinPSL d F) (ψ := Ψ)
    hker 1 (Ψ a₀) (MulAut.conj a₀) hδ hQ
  have e1 : (MulAut.conj (1 : Matrix.SpecialLinearGroup (Fin d) F)).toMonoidHom =
      MonoidHom.id _ := by ext x; simp
  rw [e1, MonoidHom.comp_id] at hmain
  have hrange : Ψ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro z
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F)) z
    refine ⟨(linSLIso d F).symm t, ?_⟩
    show LinMk d F ((linSLIso d F) ((linSLIso d F).symm t)) = z
    rw [MulEquiv.apply_symm_apply]
    exact ht
  have hblock : (coordBlockSL F I).map (linSLIso d F).toMonoidHom =
      (LinBlockGrp d F I).subgroupOf (LinSL d F) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, rfl⟩
      change ((linSLIso d F g : ↥(LinSL d F)) : GL (Fin d) F) ∈ LinBlockSet d F I
      refine ⟨(linSLIso d F g).2, ?_⟩
      intro i j hij
      rw [linSLIso_matrix_apply]
      exact mem_coordBlockSL_iff.mp hg i j hij
    · intro hx
      refine ⟨(linSLIso d F).symm x, ?_, (linSLIso d F).apply_symm_apply x⟩
      change (linSLIso d F).symm x ∈ coordBlockSL F I
      rw [mem_coordBlockSL_iff]
      intro i j hij
      rw [linSLIso_symm_matrix_apply]
      exact hx.2 i j hij
  have hmap : (coordBlockSL F I).map Ψ = LinBlockSub d F I := by
    rw [LinBlockSub]
    show (coordBlockSL F I).map ((LinMk d F).comp (linSLIso d F).toMonoidHom) =
      ((LinBlockGrp d F I).subgroupOf (LinSL d F)).map (LinMk d F)
    rw [← Subgroup.map_map, hblock]
  have hΨa : Ψ a₀ = LinMk d F a := by
    show LinMk d F ((linSLIso d F) a₀) = LinMk d F a
    rw [ha₀]
  rw [hrange, top_inf_eq, hmap, hΨa] at hmain
  exact hmain

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
