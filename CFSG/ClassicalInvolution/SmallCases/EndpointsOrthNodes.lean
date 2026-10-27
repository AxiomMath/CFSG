module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.WeakCT.SpinOddWeak
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDWeak

public section

namespace CFSG.ClassicalInvolution

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] [Finite F] {G : Type} [Group G]

theorem smallEndpoint_omega7_of_nodes (hadm : StatedLieAdmissible .POmegaOdd 3 p f)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {U₀ U₁ Us : Subgroup G}
    (hgen : U₀ ⊔ U₁ ⊔ Us = ⊤) (hc : Commutes U₀ Us)
    (hp : ∃ W, LinearBlockStandardPair F W U₀ U₁)
    (hs : ∃ W, SymplecticBlockPair F W U₁ Us) :
    ∃ Ψ : spinGroup (Spin.quadOdd 3 F) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaOdd 3 p f := by
  let U : Fin 3 → Subgroup G := ![U₀, U₁, Us]
  have hU : ⨆ k, U k = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)
  have hcomm : ∀ i j : Fin 3, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exact hc
  have hpair : ∀ i j : Fin 3, i.val + 1 = j.val → j.val + 1 < 3 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exact hp
  have hsp : ∀ i j : Fin 3, i.val + 2 = 3 → j.val + 1 = 3 →
      ∃ W, SymplecticBlockPair F W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hsurj, hker, hqs, -, hmodel, -⟩ :=
    weakCT_spinOdd_of_pair hadm hF hq U hU hcomm hpair hsp
  exact ⟨Ψ, hsurj, hker, hqs, hmodel⟩

theorem smallEndpoint_omega9_of_nodes (hadm : StatedLieAdmissible .POmegaOdd 4 p f)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {U₀ U₁ U₂ Us : Subgroup G}
    (hgen : U₀ ⊔ U₁ ⊔ U₂ ⊔ Us = ⊤) (c02 : Commutes U₀ U₂) (c0s : Commutes U₀ Us)
    (c1s : Commutes U₁ Us) (p01 : ∃ W, LinearBlockStandardPair F W U₀ U₁)
    (p12 : ∃ W, LinearBlockStandardPair F W U₁ U₂)
    (hs : ∃ W, SymplecticBlockPair F W U₂ Us) :
    ∃ Ψ : spinGroup (Spin.quadOdd 4 F) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaOdd 4 p f := by
  let U : Fin 4 → Subgroup G := ![U₀, U₁, U₂, Us]
  have hU : ⨆ k, U k = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)) (le_iSup U 3)
  have hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exacts [c02, c0s, c1s]
  have hpair : ∀ i j : Fin 4, i.val + 1 = j.val → j.val + 1 < 4 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exacts [p01, p12]
  have hsp : ∀ i j : Fin 4, i.val + 2 = 4 → j.val + 1 = 4 →
      ∃ W, SymplecticBlockPair F W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hsurj, hker, hqs, -, hmodel, -⟩ :=
    weakCT_spinOdd_of_pair hadm hF hq U hU hcomm hpair hsp
  exact ⟨Ψ, hsurj, hker, hqs, hmodel⟩

theorem smallEndpoint_minus8_of_nodes (hadm : StatedLieAdmissible .POmegaMinus 4 p f)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {U₀ U₁ Us : Subgroup G}
    (hgen : U₀ ⊔ U₁ ⊔ Us = ⊤) (hc : Commutes U₀ Us)
    (hp : ∃ W, LinearBlockStandardPair F W U₀ U₁)
    (hs : ∃ W, TwistedB2BlockPair hirr W U₁ Us) :
    ∃ Ψ : spinGroup (Spin.quadMinus 4 F b c) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaMinus 4 p f := by
  let U : Fin (4 - 1) → Subgroup G := ![U₀, U₁, Us]
  have hU : ⨆ k, U k = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)
  have hcomm : ∀ i j : Fin (4 - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exact hc
  have hpair : ∀ i j : Fin (4 - 1), i.val + 1 = j.val → j.val + 2 < 4 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exact hp
  have htw : ∀ i j : Fin (4 - 1), i.val + 3 = 4 → j.val + 2 = 4 →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hsurj, hker, hqs, -, hmodel, -⟩ :=
    weakCT_spinMinus_of_pair hadm hp2 hF hq hirr U hU hcomm hpair htw
  exact ⟨Ψ, hsurj, hker, hqs, hmodel⟩

theorem smallEndpoint_minus10_of_nodes (hadm : StatedLieAdmissible .POmegaMinus 5 p f)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {U₀ U₁ U₂ Us : Subgroup G}
    (hgen : U₀ ⊔ U₁ ⊔ U₂ ⊔ Us = ⊤) (c02 : Commutes U₀ U₂) (c0s : Commutes U₀ Us)
    (c1s : Commutes U₁ Us) (p01 : ∃ W, LinearBlockStandardPair F W U₀ U₁)
    (p12 : ∃ W, LinearBlockStandardPair F W U₁ U₂)
    (hs : ∃ W, TwistedB2BlockPair hirr W U₂ Us) :
    ∃ Ψ : spinGroup (Spin.quadMinus 5 F b c) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaMinus 5 p f := by
  let U : Fin (5 - 1) → Subgroup G := ![U₀, U₁, U₂, Us]
  have hU : ⨆ k, U k = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)) (le_iSup U 3)
  have hcomm : ∀ i j : Fin (5 - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exacts [c02, c0s, c1s]
  have hpair : ∀ i j : Fin (5 - 1), i.val + 1 = j.val → j.val + 2 < 5 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exacts [p01, p12]
  have htw : ∀ i j : Fin (5 - 1), i.val + 3 = 5 → j.val + 2 = 5 →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hsurj, hker, hqs, -, hmodel, -⟩ :=
    weakCT_spinMinus_of_pair hadm hp2 hF hq hirr U hU hcomm hpair htw
  exact ⟨Ψ, hsurj, hker, hqs, hmodel⟩

end CFSG.ClassicalInvolution
