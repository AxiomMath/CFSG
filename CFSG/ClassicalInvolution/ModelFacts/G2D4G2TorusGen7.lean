module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus7
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusGen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups

section Gen

variable {F : Type} [Field F] [Finite F]

theorem adjointGroup_le_toralCentralizer_sup_seven (hodd : Odd (Nat.card F)) (h7 : 7 ≤ Nat.card F)
    {y : ModGL Tag.G2 F} (hy : y ∈ adjointGroup Tag.G2 F)
    (hinv : ∀ t ∈ torusGroup Tag.G2 F, y * t * y⁻¹ = t⁻¹) :
    adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
  set M := toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) with hM
  have hXM : toralCentralizer Tag.G2 F ![-1, 1] ≤ M := le_sup_left
  have hPM : (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) ≤ M :=
    le_sup_right
  have hTM : torusGroup Tag.G2 F ≤ M := (torusGroup_le_toralCentralizer _).trans hXM
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : Fin Tag.G2.rank → Fˣ, a₂ = ![1, -1] := ⟨_, rfl⟩
  have ha₂0 : a₂ g2i0 = 1 := by rw [ha₂]; rfl
  have ha₂1 : a₂ g2i1 = -1 := by rw [ha₂]; rfl
  have ha₂sq : ∀ i, a₂ i = 1 ∨ a₂ i = -1 := by
    intro i; fin_cases i
    · exact Or.inl ha₂0
    · exact Or.inr ha₂1
  have ha₂ne : a₂ ≠ 1 := by
    intro h
    have := congrFun h g2i1
    rw [ha₂1] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val this)
  have hy₂ : y ∈ toralCentralizer Tag.G2 F a₂ := by
    rw [mem_toralCentralizer]
    refine ⟨hy, ?_⟩
    have hd := hinv _ (g2_rootDiagUnit_mem_torusGroup (K := F) a₂)
    have hdinv : (rootDiagUnit Tag.G2 a₂)⁻¹ = rootDiagUnit Tag.G2 a₂ := by
      rw [rootDiagUnit_inv]
      congr 1
      funext i
      rcases ha₂sq i with h | h <;> simp [h]
    rw [hdinv, mul_inv_eq_iff_eq_mul] at hd
    rw [mul_inv_eq_iff_eq_mul]
    exact hd.symm
  have hΦinj := rootChart_injective hK2 (τ := Tag.G2) (K := F) 1 g2i0
  have hΦlin : LinAct (rootChart Tag.G2 F 1 g2i0) y := by
    refine toralCentralizer_le_linActSubgroup hodd ha₂sq ha₂ne (γ := Pi.single g2i0 1)
      ⟨isRoot_single _ _, ?_⟩ (w := 1) (i := g2i0) (one_smul _ _) hy₂
    rw [rootChar_single_g2, ha₂0]
  obtain ⟨D, hD⟩ := hΦlin
  obtain ⟨hD00, hD11⟩ := chart_matrix_antidiag hodd (by omega) hD hinv
  have hdet : (D : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (D : Matrix (Fin 2) (Fin 2) F)).mp D.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two, hD00, hD11] at hdet
  have hq : (D : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hr : (D : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  set q := (D : Matrix (Fin 2) (Fin 2) F) 0 1 with hqdef
  set r := (D : Matrix (Fin 2) (Fin 2) F) 1 0 with hrdef
  have hDeta : (D : Matrix (Fin 2) (Fin 2) F) = !![0, q; r, 0] := by
    rw [Matrix.eta_fin_two (D : Matrix (Fin 2) (Fin 2) F), hD00, hD11]
  set κ : Fˣ := Units.mk0 (q * r) (mul_ne_zero hq hr) with hκ
  have hΦmem : ∀ A : SL2 F, rootChart Tag.G2 F 1 g2i0 A ∈ adjointGroup Tag.G2 F := fun A => by
    rw [rootChart_one]; exact simpleRootSL2_mem_adjointGroup g2i0 A
  have hA : ∀ t : Fˣ, HSL t ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by
    intro t
    rw [Subgroup.mem_comap, rootChart_one, simpleRootSL2_HSL]
    exact hTM (torusElt_mem_torusGroup _ _)
  have hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by
    intro s u v h
    rw [Subgroup.mem_comap]
    have hu₀ : u * u - (q * v) * (r * v) = 1 := by
      have hk : (κ : F) = q * r := rfl
      rw [hk] at h
      linear_combination h
    let B₀ : SL2 F := ⟨!![u, q * v; r * v, u], by
      rw [det_fin_two]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      linear_combination hu₀⟩
    set s' : Fˣ := s * (Units.mk0 q hq)⁻¹ with hs'
    have hconj : normTorusSL (κ : F) s u v h = glConjSL (diagGL s') B₀ := by
      have hq0 : q ≠ 0 := hq
      have hs0 : (s : F) ≠ 0 := s.ne_zero
      have hκv : (κ : F) = q * r := rfl
      refine SL2_ext ?_ ?_ ?_ ?_
      · rw [glConjSL_diagGL_apply_00]
        simp [coe_normTorusSL, B₀]
      · rw [glConjSL_diagGL_apply_01]
        simp [coe_normTorusSL, B₀, hs']
        field_simp
      · rw [glConjSL_diagGL_apply_10]
        simp [coe_normTorusSL, B₀, hs', hκv]
        field_simp
      · rw [glConjSL_diagGL_apply_11]
        simp [coe_normTorusSL, B₀]
    have hcomm : (D : Matrix (Fin 2) (Fin 2) F) * (B₀ : Matrix (Fin 2) (Fin 2) F) =
        (B₀ : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
      rw [hDeta]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hglB : glConjSL D B₀ = B₀ :=
      Subtype.ext (by rw [glConjSL_coe, hcomm, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one])
    have hyB : y * rootChart Tag.G2 F 1 g2i0 B₀ = rootChart Tag.G2 F 1 g2i0 B₀ * y := by
      have := hD B₀
      rw [hglB] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have hP : rootChart Tag.G2 F 1 g2i0 B₀ ∈
        adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F)) :=
      ⟨hΦmem B₀, Subgroup.mem_centralizer_singleton_iff.mpr hyB.symm⟩
    have hd := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i0 (fun _ => s') B₀
    rw [one_smul, rootChar_single_g2] at hd
    rw [hconj, ← show (fun _ : Fin Tag.G2.rank => s') g2i0 = s' from rfl]
    rw [← hd]
    exact mul_mem (mul_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)) (hPM hP))
      (inv_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)))
  have htop := eq_top_of_normTorus_seven h7 h2 κ hA hB
  have hall : ∀ A : SL2 F, rootChart Tag.G2 F 1 g2i0 A ∈ M := fun A => by
    have : A ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by rw [htop]; trivial
    exact this
  rw [adjointGroup_eq_iSup_rootPair_single]
  refine iSup_le fun i => ?_
  fin_cases i
  · rw [← range_simpleRootSL2_eq_rootPair, ← rootChart_one (K := F) (τ := Tag.G2)]
    rintro _ ⟨A, rfl⟩
    exact hall A
  · have hker : (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ) ∈
        rootCharKernel (τ := Tag.G2) (K := F) ![-1, 1] :=
      ⟨isRoot_single _ _, (rootChar_single_g2 _ _).trans rfl⟩
    exact (rootPair_le_toralCentralizer hker).trans hXM

end Gen

section Model

variable {F : Type} [Field F] [Finite F]

theorem centralizer_sup_eq_top_of_inverting_seven (hodd : Odd (Nat.card F)) (h7 : 7 ≤ Nat.card F)
    {c₁ y : ↥(adjointGroup Tag.G2 F)} (h₁ : (c₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1])
    (hinv : ∀ t ∈ torusGroup Tag.G2 F,
      (y : ModGL Tag.G2 F) * t * (y : ModGL Tag.G2 F)⁻¹ = t⁻¹) :
    Subgroup.centralizer ({c₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  apply Subgroup.map_injective (adjointGroup Tag.G2 F).subtype_injective
  rw [Subgroup.map_sup, map_centralizer_g2_eq_toralCentralizer h₁, map_centralizer_g2_eq_inf,
    Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (sup_le (fun x hx => (mem_toralCentralizer.mp hx).1) inf_le_left) ?_
  exact adjointGroup_le_toralCentralizer_sup_seven hodd h7 y.2 hinv

end Model

end CFSG.ClassicalInvolution.G2D4Models
