module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.RankThree.PartOne.StrongP
open scoped Matrix

section Symplectic

variable {F : Type} [Field F] {m : ℕ}

private def wcSRk (m : ℕ) : Fin (m + 2) ⊕ Fin (m + 2) → ℕ :=
  Sum.elim (fun i => i.val) (fun i => 2 * m + 3 - i.val)

private theorem wcSRk_lt (i : Fin (m + 2) ⊕ Fin (m + 2)) : wcSRk m i < 2 * m + 4 := by
  rcases i with i | i
  · have := i.isLt
    simp only [wcSRk, Sum.elim_inl]
    omega
  · simp only [wcSRk, Sum.elim_inr]
    omega

private theorem wcS_ne10 : (1 : Fin (m + 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

private theorem wcS_single_ne {i j k l : Fin (m + 2)} {c : F}
    (h : (Matrix.single i j c : Matrix (Fin (m + 2)) (Fin (m + 2)) F) k l ≠ 0) :
    i = k ∧ j = l := by
  by_contra hne
  exact h (Matrix.single_apply_of_ne i j c k l hne)

private theorem wcS_sq01 :
    (Matrix.single (0 : Fin (m + 2)) (1 : Fin (m + 2)) (1 : F)) * Matrix.single 0 1 1 = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ wcS_ne10 _

private theorem wcS_sq10 :
    (Matrix.single (1 : Fin (m + 2)) (0 : Fin (m + 2)) (1 : F)) * Matrix.single 1 0 1 = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ wcS_ne10.symm _

private theorem wcS_unit_pair {R : Type*} [Ring R] {E : R} (h : E * E = 0) :
    (1 + E) * (1 - E) = 1 ∧ (1 - E) * (1 + E) = 1 := by
  have h1 : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
  have h2 : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
  exact ⟨by rw [h1, h, sub_zero], by rw [h2, h, sub_zero]⟩

private def wcSS : Matrix (Fin (m + 2)) (Fin (m + 2)) F := Matrix.single 1 1 1

private def wcSA : Matrix (Fin (m + 2)) (Fin (m + 2)) F := 1 + Matrix.single 0 1 1

private def wcSD : Matrix (Fin (m + 2)) (Fin (m + 2)) F := 1 - Matrix.single 1 0 1

private def wcSX : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  Matrix.fromBlocks 1 wcSS 0 1

private def wcSXi : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  Matrix.fromBlocks 1 (-wcSS) 0 1

private def wcSY : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  Matrix.fromBlocks wcSA 0 0 wcSD

private def wcSYi : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  Matrix.fromBlocks (1 - Matrix.single 0 1 1) 0 0 (1 + Matrix.single 1 0 1)

private theorem wcSX_mul_Xi :
    (wcSX : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) * wcSXi = 1 := by
  simp [wcSX, wcSXi, Matrix.fromBlocks_multiply]

private theorem wcSXi_mul_X :
    (wcSXi : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) * wcSX = 1 := by
  simp [wcSX, wcSXi, Matrix.fromBlocks_multiply]

private theorem wcSY_mul_Yi :
    (wcSY : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) * wcSYi = 1 := by
  obtain ⟨hA, -⟩ := wcS_unit_pair (wcS_sq01 (m := m) (F := F))
  obtain ⟨-, hD⟩ := wcS_unit_pair (wcS_sq10 (m := m) (F := F))
  simp [wcSY, wcSYi, wcSA, wcSD, Matrix.fromBlocks_multiply, hA, hD]

private theorem wcSYi_mul_Y :
    (wcSYi : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) * wcSY = 1 := by
  obtain ⟨-, hA⟩ := wcS_unit_pair (wcS_sq01 (m := m) (F := F))
  obtain ⟨hD, -⟩ := wcS_unit_pair (wcS_sq10 (m := m) (F := F))
  simp [wcSY, wcSYi, wcSA, wcSD, Matrix.fromBlocks_multiply, hA, hD]

private def wcSXU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  ⟨wcSX, wcSXi, wcSX_mul_Xi, wcSXi_mul_X⟩

private def wcSYU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F :=
  ⟨wcSY, wcSYi, wcSY_mul_Yi, wcSYi_mul_Y⟩

private theorem wcSS_transpose : (wcSS : Matrix (Fin (m + 2)) (Fin (m + 2)) F)ᵀ = wcSS := by
  simp [wcSS]

private theorem wcSA_transpose_mul :
    (wcSA : Matrix (Fin (m + 2)) (Fin (m + 2)) F)ᵀ * wcSD = 1 := by
  obtain ⟨h, -⟩ := wcS_unit_pair (wcS_sq10 (m := m) (F := F))
  have hT : (wcSA : Matrix (Fin (m + 2)) (Fin (m + 2)) F)ᵀ = 1 + Matrix.single 1 0 1 := by
    simp [wcSA]
  rw [hT, wcSD]
  exact h

private theorem wcSD_transpose_mul :
    (wcSD : Matrix (Fin (m + 2)) (Fin (m + 2)) F)ᵀ * wcSA = 1 := by
  obtain ⟨-, h⟩ := wcS_unit_pair (wcS_sq01 (m := m) (F := F))
  have hT : (wcSD : Matrix (Fin (m + 2)) (Fin (m + 2)) F)ᵀ = 1 - Matrix.single 0 1 1 := by
    simp [wcSD]
  rw [hT, wcSA]
  exact h

private theorem wcSX_symp :
    (wcSX : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F)ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 * wcSX = Matrix.fromBlocks 0 1 (-1) 0 := by
  simp [wcSX, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, wcSS_transpose]

private theorem wcSY_symp :
    (wcSY : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F)ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 * wcSY = Matrix.fromBlocks 0 1 (-1) 0 := by
  simp [wcSY, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, wcSA_transpose_mul,
    wcSD_transpose_mul]

private theorem wcSX_sub_one :
    (wcSX : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) - 1 =
      Matrix.fromBlocks 0 wcSS 0 0 := by
  ext (i | i) (j | j) <;> simp [wcSX, Matrix.one_apply]

private theorem wcSY_sub_one :
    (wcSY : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) - 1 =
      Matrix.fromBlocks (Matrix.single 0 1 1) 0 0 (-Matrix.single 1 0 1) := by
  ext (i | i) (j | j) <;> simp [wcSY, wcSA, wcSD, Matrix.one_apply]

private theorem wcSX_unitri :
    IsUnitri (wcSRk m) (wcSXU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F) := by
  intro i j h
  change ((wcSX : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) - 1) i j ≠ 0
    at h
  rw [wcSX_sub_one] at h
  rcases i with i | i <;> rcases j with j | j
  · simp at h
  · have h' : (wcSS : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i j ≠ 0 := h
    obtain ⟨rfl, rfl⟩ := wcS_single_ne h'
    simp only [wcSRk, Sum.elim_inl, Sum.elim_inr, Fin.val_one]
    omega
  · simp at h
  · simp at h

private theorem wcSY_unitri :
    IsUnitri (wcSRk m) (wcSYU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F) := by
  intro i j h
  change ((wcSY : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F) - 1) i j ≠ 0
    at h
  rw [wcSY_sub_one] at h
  rcases i with i | i <;> rcases j with j | j
  · have h' : (Matrix.single (0 : Fin (m + 2)) (1 : Fin (m + 2)) (1 : F)) i j ≠ 0 := h
    obtain ⟨rfl, rfl⟩ := wcS_single_ne h'
    simp only [wcSRk, Sum.elim_inl, Fin.val_one, Fin.val_zero]
    omega
  · simp at h
  · simp at h
  · have h' : (Matrix.single (1 : Fin (m + 2)) (0 : Fin (m + 2)) (1 : F)) i j ≠ 0 := by
      simpa using h
    obtain ⟨rfl, rfl⟩ := wcS_single_ne h'
    simp only [wcSRk, Sum.elim_inr, Fin.val_one, Fin.val_zero]
    omega

private theorem wcS_ne :
    (wcSXU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F) * wcSYU ≠ wcSYU * wcSXU := by
  intro h
  have h' := congrArg (fun g : GL (Fin (m + 2) ⊕ Fin (m + 2)) F =>
    (g : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) F)) h
  have := congrFun (congrFun h' (Sum.inl 0)) (Sum.inr 1)
  simp [wcSXU, wcSYU, wcSX, wcSY, Matrix.fromBlocks_multiply, wcSS, wcSA, wcSD, wcS_ne10,
    wcS_ne10.symm] at this

private theorem wcS_nonscalarPPair {p : ℕ} [Fact p.Prime] [CharP F p] :
    NonscalarPPair p (StatedSp (m + 2) F) := by
  haveI : Nonempty (Fin (m + 2) ⊕ Fin (m + 2)) := ⟨Sum.inl 0⟩
  have hx : (wcSXU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F) ∈ StatedSp (m + 2) F :=
    Subgroup.subset_closure wcSX_symp
  have hy : (wcSYU : GL (Fin (m + 2) ⊕ Fin (m + 2)) F) ∈ StatedSp (m + 2) F :=
    Subgroup.subset_closure wcSY_symp
  exact NonscalarPPair.of_unitri (r := wcSRk m) (m := 2 * m + 4) wcSRk_lt hx hy
    wcSX_unitri wcSY_unitri wcS_ne

end Symplectic

private theorem wcS_charP {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (h : Nat.card F = p ^ f) : CharP F p := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

theorem wcOn_psp {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 2 ≤ n) (h : CFSG.Open.StatedClassicalModel K .PSp n p f) : WCOn p K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F p := wcS_charP hF
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact (wcS_nonscalarPPair (F := F) (m := m) (p := p)).wcOn e

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
