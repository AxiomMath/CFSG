module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxUnitary
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Lattice
open CFSG.RankThree.E6 CFSG.RankThree.Classical2
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace QuasiE6

theorem exists_chainRoot13_of_support : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain13 k l = e6RootVec m := by
  decide +kernel

theorem chainRoot13_add : ∀ i j k : Fin 3,
    chainRoot chain13 i j + chainRoot chain13 j k = chainRoot chain13 i k := by
  decide +kernel

@[expose] def rho₁ (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  (subsystemGroup Tag.E6 L support13).subtype.comp (a2Equiv₁ L).symm.toMonoidHom

variable {L : Type} [Field L]

theorem rho₁_range : (rho₁ L).range = subsystemGroup Tag.E6 L support13 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₁ L).symm X).2
  · intro hg
    exact ⟨a2Equiv₁ L ⟨g, hg⟩, by simp [rho₁]⟩

theorem rho₁_transvection {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rho₁ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain13 i j) ((ε : L) * t) := by
  obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := L) hij
  have hss : (s : L) * s = 1 := by rcases hs with rfl | rfl <;> simp
  refine ⟨⟨(s : L), (s : L), hss, hss⟩, fun t => ?_⟩
  have h : (a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.transvection hij t) =
      ⟨pinnedX Tag.E6 L (chainRoot chain13 i j) ((s : L) * t),
        pinnedX_chainRoot13_mem hij _⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, ← mul_assoc, hss, one_mul]
    rfl
  simp only [rho₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h]

theorem rho₁_diagonal (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    rho₁ L A ∈ torusGroup Tag.E6 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
      ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  have hrep : a2Equiv₁ L ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ = A := by
    rw [a2Equiv₁_apply]
    apply Subtype.ext
    rw [coe_a2Rep₁]
    change a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) ua ub) = _
    rw [a2Mat₁_torus, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hsymm : (a2Equiv₁ L).symm A = ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ := by
    rw [MulEquiv.symm_apply_eq, hrep]
  simp only [rho₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [hsymm]
  exact e6TorusPair_mem_torusGroup _ _ ua ub

theorem frame₁ : IsA2Frame (rho₁ L) (fun i j => chainRoot chain13 i j) where
  injective := Subtype.val_injective.comp (a2Equiv₁ L).symm.injective
  isRoot _ _ hij := (chainRoot13_mem_parabolicRoots hij).1
  neg i j := chainRoot_swap chain13 i j
  add := chainRoot13_add
  transv _ _ hij := rho₁_transvection hij
  range := by
    rw [rho₁_range, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    refine ⟨fun hr => ?_, fun ⟨i, j, hij, h⟩ => h ▸ chainRoot13_mem_parabolicRoots hij⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr.1
    obtain ⟨k, l, hkl, h⟩ := exists_chainRoot13_of_support m
      (fun i hi => hr.2 i ((mem_support13 i).not.2 hi))
    exact ⟨k, l, hkl, h.symm⟩
  diag := rho₁_diagonal

@[expose] def wE6 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd TwClass.wordE6

@[expose] def vWord : List (Fin Tag.E6.rank) := [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

@[expose] def vE6 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd vWord

@[expose] def listS₁ : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1], ![0, -1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def listS₂ : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, 0, -1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0]]

theorem w_smul (x : Fin Tag.E6.rank → ℤ) :
    (wE6 • x : Fin Tag.E6.rank → ℤ) = wordMat Tag.E6 TwClass.wordE6 *ᵥ x :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.E6 TwClass.wordE6 x

theorem v_smul (x : Fin Tag.E6.rank → ℤ) :
    (vE6 • x : Fin Tag.E6.rank → ℤ) = wordMat Tag.E6 vWord *ᵥ x :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.E6 vWord x

theorem S₂_sub : ∀ β ∈ rootFinset Tag.E6,
    (∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → β i = 0) → β ∈ listS₂ := by
  decide +kernel

theorem S₂_root : ∀ β ∈ listS₂, β ∈ rootFinset Tag.E6 ∧
    ∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → β i = 0 := by decide +kernel

theorem S₂_eq : TwClass.e6Six.S₂ = {r | r ∈ listS₂} := by
  ext β
  show (IsRoot Tag.E6 β ∧ ∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → β i = 0) ↔
    β ∈ listS₂
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₂_sub β (mem_rootFinset.2 hβ) hs
  · intro hβ
    exact ⟨mem_rootFinset.1 (S₂_root β hβ).1, (S₂_root β hβ).2⟩

theorem S₁_sub : ∀ β ∈ rootFinset Tag.E6, (∀ α ∈ listS₂, iform (τ := Tag.E6) β α = 0) →
    β ∈ listS₁ := by decide +kernel

theorem S₁_root : ∀ β ∈ listS₁, β ∈ rootFinset Tag.E6 ∧
    ∀ α ∈ listS₂, iform (τ := Tag.E6) β α = 0 := by decide +kernel

theorem S₁_eq : TwClass.e6Six.S₁ = {r | r ∈ listS₁} := by
  ext β
  show (IsRoot Tag.E6 β ∧ ∀ α ∈ TwClass.e6Six.S₂, iform (τ := Tag.E6) β α = 0) ↔ β ∈ listS₁
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₁_sub β (mem_rootFinset.2 hβ) fun α hα => by
      rw [S₂_eq] at hs
      exact hs α hα
  · intro hβ
    refine ⟨mem_rootFinset.1 (S₁_root β hβ).1, fun α hα => ?_⟩
    rw [S₂_eq] at hα
    exact (S₁_root β hβ).2 α hα

theorem v_img : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 vWord *ᵥ chainRoot chain13 i j ∈ listS₁ := by decide +kernel

theorem v_cover : ∀ r ∈ listS₁, ∃ i j : Fin 3, i ≠ j ∧
    r = wordMat Tag.E6 vWord *ᵥ chainRoot chain13 i j := by decide +kernel

theorem S₁_eq_chain : TwClass.e6Six.S₁ =
    {r | ∃ i j : Fin 3, i ≠ j ∧ r = vE6 • chainRoot chain13 i j} := by
  rw [S₁_eq]
  ext r
  show r ∈ listS₁ ↔ ∃ i j : Fin 3, i ≠ j ∧ r = vE6 • chainRoot chain13 i j
  simp only [v_smul]
  constructor
  · intro hr
    obtain ⟨i, j, hij, h⟩ := v_cover r hr
    exact ⟨i, j, hij, h⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact v_img i j hij

theorem graph₁ : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ (wordMat Tag.E6 vWord *ᵥ chainRoot chain13 i j) =
      wordMat Tag.E6 vWord *ᵥ chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

end QuasiE6

theorem isQuasisimple_e6Six_X₁ {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    CFSG.IsQuasisimple ↥(TwClass.e6Six.X₁ D) := by
  refine D.isQuasisimple_frame ?_
  refine D.isQuasisimple_fixedRoot_A2Frame hK
    (h := (QuasiE6.frame₁ (L := D.L)).transport QuasiE6.vE6) QuasiE6.S₁_eq_chain Fin.revPerm ?_
  intro i j hij
  show (QuasiE6.wE6 • (QuasiE6.vE6 • chainRoot chain13 i j) : Fin Tag.E6.rank → ℤ) =
    QuasiE6.vE6 • chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i)
  rw [QuasiE6.w_smul, QuasiE6.v_smul, QuasiE6.v_smul]
  exact QuasiE6.graph₁ i j hij

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
