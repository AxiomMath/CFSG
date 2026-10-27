module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusArith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Polynomial Module Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem dvd_X_pow_three_sub_C_of_mem_primaryFactors
    {k : Type} [Field k] {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) {h : k[X]}
    (hh : h ∈ primaryFactors (Matrix.toLin' (A : Matrix (Fin n) (Fin n) k))) :
    h ∣ X ^ 3 - C (c : k) := by
  have hroot : aeval (Matrix.toLin' (A : Matrix (Fin n) (Fin n) k)) (X ^ 3 - C (c : k)) = 0 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.aeval_X_pow_sub_C_eq_zero (p := 3) hA
  exact (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd k _ hroot)

theorem card_irreducible_dvd_X_pow_three_sub_C_le_two
    {k : Type} [Field k] [Fintype k] {c : kˣ}
    (hcop : Nat.Coprime 3 (Nat.card k - 1)) :
    ∀ s : Finset k[X], (∀ h ∈ s, Irreducible h ∧ h.Monic ∧ h ∣ X ^ 3 - C (c : k)) →
      s.card ≤ 2 := by
  classical
  intro s hs
  by_contra hle
  rw [not_le] at hle
  obtain ⟨h₁, h₁s, h₂, h₂s, h₃, h₃s, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.mp hle
  obtain ⟨i₁, m₁, d₁⟩ := hs h₁ h₁s
  obtain ⟨i₂, m₂, d₂⟩ := hs h₂ h₂s
  obtain ⟨i₃, m₃, d₃⟩ := hs h₃ h₃s
  have c₁₂ : IsCoprime h₁ h₂ := by
    rw [i₁.coprime_iff_not_dvd]
    intro hd
    exact h₁₂ (eq_of_monic_of_associated m₁ m₂ (i₁.associated_of_dvd i₂ hd))
  have c₁₃ : IsCoprime h₁ h₃ := by
    rw [i₁.coprime_iff_not_dvd]
    intro hd
    exact h₁₃ (eq_of_monic_of_associated m₁ m₃ (i₁.associated_of_dvd i₃ hd))
  have c₂₃ : IsCoprime h₂ h₃ := by
    rw [i₂.coprime_iff_not_dvd]
    intro hd
    exact h₂₃ (eq_of_monic_of_associated m₂ m₃ (i₂.associated_of_dvd i₃ hd))
  have hprod : h₁ * h₂ * h₃ ∣ X ^ 3 - C (c : k) :=
    (c₁₃.mul_left c₂₃).mul_dvd (c₁₂.mul_dvd d₁ d₂) d₃
  have hne : (X ^ 3 - C (c : k) : k[X]) ≠ 0 :=
    (monic_X_pow_sub_C (c : k) (by norm_num : (3 : ℕ) ≠ 0)).ne_zero
  have hdeg_prod : (h₁ * h₂ * h₃).natDegree =
      h₁.natDegree + h₂.natDegree + h₃.natDegree := by
    rw [Monic.natDegree_mul (m₁.mul m₂) m₃, Monic.natDegree_mul m₁ m₂]
  have hdeg_le : h₁.natDegree + h₂.natDegree + h₃.natDegree ≤ 3 := by
    have h := Polynomial.natDegree_le_of_dvd hprod hne
    rwa [hdeg_prod, natDegree_X_pow_sub_C] at h
  have hp₁ : 0 < h₁.natDegree := i₁.natDegree_pos
  have hp₂ : 0 < h₂.natDegree := i₂.natDegree_pos
  have hp₃ : 0 < h₃.natDegree := i₃.natDegree_pos
  have e₁ : h₁.natDegree = 1 := by omega
  have e₂ : h₂.natDegree = 1 := by omega
  have e₃ : h₃.natDegree = 1 := by omega
  have lin₁ : ∃ a : k, h₁ = X - C a := by
    refine ⟨-(h₁.coeff 0), ?_⟩
    rw [m₁.eq_X_add_C e₁]
    simp
  have lin₂ : ∃ a : k, h₂ = X - C a := by
    refine ⟨-(h₂.coeff 0), ?_⟩
    rw [m₂.eq_X_add_C e₂]
    simp
  obtain ⟨a₁, ha₁⟩ := lin₁
  obtain ⟨a₂, ha₂⟩ := lin₂
  have r₁ : a₁ ^ 3 = (c : k) := by
    have hdv : X - C a₁ ∣ X ^ 3 - C (c : k) := by rwa [ha₁] at d₁
    have h0 : a₁ ^ 3 - (c : k) = 0 := by
      simpa [IsRoot] using (dvd_iff_isRoot.mp hdv)
    exact sub_eq_zero.mp h0
  have r₂ : a₂ ^ 3 = (c : k) := by
    have hdv : X - C a₂ ∣ X ^ 3 - C (c : k) := by rwa [ha₂] at d₂
    have h0 : a₂ ^ 3 - (c : k) = 0 := by
      simpa [IsRoot] using (dvd_iff_isRoot.mp hdv)
    exact sub_eq_zero.mp h0
  have haeq : a₁ = a₂ := eq_of_pow_three_eq_pow_three hcop (r₁.trans r₂.symm)
  exact h₁₂ (by rw [ha₁, ha₂, haeq])

theorem card_primaryFactors_le_two
    {k : Type} [Field k] [Fintype k] [CharP k 2] {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hcop : Nat.Coprime 3 (Nat.card k - 1))
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    (primaryFactors (Matrix.toLin' (A : Matrix (Fin n) (Fin n) k))).card ≤ 2 := by
  refine card_irreducible_dvd_X_pow_three_sub_C_le_two (k := k) (c := c) hcop _ ?_
  intro h hh
  exact ⟨irreducible_of_mem_primaryFactors hh, monic_of_mem_primaryFactors hh,
    dvd_X_pow_three_sub_C_of_mem_primaryFactors hA hh⟩

theorem linear_not_three_components
    {k : Type} [Field k] [Fintype k] [CharP k 2] {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hcop : Nat.Coprime 3 (Nat.card k - 1))
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {K₁ K₂ K₃ : Subgroup (LinearFlag.projectiveSL n k)}
    (h₁ : IsComponentOf K₁ (fixSubgroup (LinearFlag.conjAut n k A)))
    (h₂ : IsComponentOf K₂ (fixSubgroup (LinearFlag.conjAut n k A)))
    (h₃ : IsComponentOf K₃ (fixSubgroup (LinearFlag.conjAut n k A)))
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  classical
  have hpk : (3 : k) ≠ 0 := by
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    rw [show (3 : k) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  obtain ⟨f₁, e₁⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
      (p := 3) hpk hA K₁ h₁
  obtain ⟨f₂, e₂⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
      (p := 3) hpk hA K₂ h₂
  obtain ⟨f₃, e₃⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
      (p := 3) hpk hA K₃ h₃
  have hne₁₂ : f₁.1.1 ≠ f₂.1.1 := by
    intro he
    exact h12 (by rw [e₁, e₂, he])
  have hne₁₃ : f₁.1.1 ≠ f₃.1.1 := by
    intro he
    exact h13 (by rw [e₁, e₃, he])
  have hne₂₃ : f₂.1.1 ≠ f₃.1.1 := by
    intro he
    exact h23 (by rw [e₂, e₃, he])
  have hlt : 2 < (primaryFactors (Matrix.toLin' (A : Matrix (Fin n) (Fin n) k))).card :=
    Finset.two_lt_card.mpr
      ⟨f₁.1.1, f₁.1.2, f₂.1.1, f₂.1.2, f₃.1.1, f₃.1.2, hne₁₂, hne₁₃, hne₂₃⟩
  have hle := card_primaryFactors_le_two hcop hA
  omega

end CFSG.LocalAnalysis.GLTheoremA
