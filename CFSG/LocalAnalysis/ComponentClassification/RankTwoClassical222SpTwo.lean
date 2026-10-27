module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpJ23
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Two

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

theorem deltaCentral_alpha_sp {G : Type} [Group G] {A : Subgroup G} {n : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hp : (∃ ℓ, HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .a ℓ) ∨
      HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .b 1) :
    DeltaCentral A p (alphaGroup e p) := by
  obtain ⟨hp2, M, hpM, hM2, hcase⟩ : orderOf p = 2 ∧ ∃ M : GL (Fin n ⊕ Fin n) K,
      Represents e p M ∧ orderOf M = 2 ∧
        ((∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0) ∨
          commRank M = 1) := by
    rcases hp with ⟨ℓ, hp2, M, hpM, hM2, -, -, h0⟩ | ⟨hp2, M, hpM, hM2, hr, -⟩
    · exact ⟨hp2, M, hpM, hM2, Or.inl h0⟩
    · exact ⟨hp2, M, hpM, hM2, Or.inr hr⟩
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X hXH hXM hXg => ⟨X, hXH,
    ⟨1, by rw [map_one, mul_one]⟩, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      1 + c • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) := by
    rcases hcase with h0 | hr
    · exact commutant_typeA_sp hpM.2.1 hM2 h0 hXH hXM hXg
    · exact commutant_b1_sp hpM.2.1 hM2 hr hXH hXM hXg
  exact ⟨c, by rw [hc, add_sub_cancel_left]⟩

theorem deltaAlphaTwo_symplectic : DeltaAlphaTwo .symplectic := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    exact deltaCentral_alpha_sp hZ hp
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem symplecticJ23Two : SymplecticJ23Two := by
  intro G _ _ A D hD _ hZ _ p ℓ hp
  obtain ⟨a, b, hab, hb, -, hDC, hcent, -⟩ := symplecticJ23_of_family G A D hD hZ p ℓ hp
  refine ⟨a, b, ?_, hb, hDC, hcent⟩
  rcases hab with ⟨-, -, ha⟩ | ⟨-, ha⟩
  · exact ⟨_, ha⟩
  · exact ⟨_, ha⟩

end CFSG.ComponentClassification.RankTwoClassical
