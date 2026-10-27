module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Orthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem commutator_mem_of_chain_three {G : Type*} [Group G] [Finite G] {N K₁ O D : Subgroup G}
    [N.Normal] (hNK : N ≤ K₁) (hKO : K₁ ≤ O) (hOD : O ≤ D)
    (hK₁ : ∀ o ∈ O, ∀ k ∈ K₁, o * k * o⁻¹ ∈ K₁)
    (hO : ∀ d ∈ D, ∀ o ∈ O, d * o * d⁻¹ ∈ O)
    (h1 : N.relIndex K₁ ≤ 2) (h2 : K₁.relIndex O ≤ 2) (h3 : O.relIndex D ≤ 2)
    {α : G} {k : ℕ} (hk : α ^ (3 ^ k) = 1)
    (hαK : ∀ x ∈ K₁, α * x * α⁻¹ ∈ K₁) (hαO : ∀ x ∈ O, α * x * α⁻¹ ∈ O)
    (hαD : ∀ x ∈ D, α * x * α⁻¹ ∈ D) {δ : G} (hδ : δ ∈ D) :
    α * δ * α⁻¹ * δ⁻¹ ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have h10 : N.relIndex K₁ ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h20 : K₁.relIndex O ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hNO : N ≤ O := hNK.trans hKO
  have hNO0 : N.relIndex O ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hNKO : N.relIndex O = N.relIndex K₁ * K₁.relIndex O :=
    (Subgroup.relIndex_mul_relIndex N K₁ O hNK hKO).symm
  have Y1 : ∀ y ∈ K₁, α * y * α⁻¹ * y⁻¹ ∈ N := fun y hy =>
    pElement_comm_mem_of_relIndex_le N K₁ (fun o _ n hn => ‹N.Normal›.conj_mem n hn o) hk
      (fun i hi => ‹N.Normal›.conj_mem i hi α) hαK (h1.trans (by norm_num)) hy
  have Y2 : ∀ o ∈ O, α * o * α⁻¹ * o⁻¹ ∈ K₁ := fun o ho =>
    pElement_comm_mem_of_relIndex_le K₁ O hK₁ hk hαK hαO (h2.trans (by norm_num)) ho
  have Y2' : ∀ o ∈ O, α * o * α⁻¹ * o⁻¹ ∈ N := fun o ho => by
    have hc : α * o * α⁻¹ * o⁻¹ ∈ K₁ := Y2 o ho
    refine mem_of_comm_pow hp (n := N.relIndex K₁) (M := K₁) ?_ ?_ hk hc (Y1 _ hc)
    · exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h10) (by omega)
    · intro y
      exact pow_card_eq_one' (G := K₁ ⧸ N.subgroupOf K₁) (x := y)
  have Y3 : ∀ d ∈ D, α * d * α⁻¹ * d⁻¹ ∈ O := fun d hd =>
    pElement_comm_mem_of_relIndex_le O D hO hk hαO hαD (h3.trans (by norm_num)) hd
  have hc : α * δ * α⁻¹ * δ⁻¹ ∈ O := Y3 δ hδ
  refine mem_of_comm_pow hp (n := N.relIndex O) (M := O) ?_ ?_ hk hc (Y2' _ hc)
  · rw [hNKO]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero h10) h
      omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero h20) h
      omega
  · intro y
    exact pow_card_eq_one' (G := O ⧸ N.subgroupOf O) (x := y)

end CFSG.LocalAnalysis.GLTheoremA
