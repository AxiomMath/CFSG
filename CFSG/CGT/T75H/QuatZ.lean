module

public import CFSG.CGT.T75H.QuatCbar

public section

namespace CFSG.CGT.T75H

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_comm {A C : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {s : G} (hs : s ∈ A ⊔ C) :
    ∃ d ∈ A, ∃ c ∈ C, s = d * c := by
  have hA : A ≤ Subgroup.centralizer (C : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun c hc => (hcomm a ha c hc).symm
  have hs' : s ∈ ((A ⊔ C : Subgroup G) : Set G) := hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A C
    (hA.trans (Subgroup.centralizer_le_normalizer _))] at hs'
  obtain ⟨d, hd, c, hc, hdc⟩ := Set.mem_mul.1 hs'
  exact ⟨d, hd, c, hc, hdc.symm⟩

theorem false_of_quaternion_split [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {S : Sylow 2 G} {A C : Subgroup G} (hsup : A ⊔ C = (S : Subgroup G))
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {e : ℕ} (ϕ : QuaternionGroup (2 ^ e) ≃* C)
    (hfuse : ∀ g : G, ∀ c ∈ C, c * c = 1 → c ≠ 1 → g⁻¹ * c * g ∈ (S : Subgroup G) →
      g⁻¹ * c * g ∈ C) : False := by
  obtain ⟨z, c₀, hzC, -, -, hz1, hzz, huniq⟩ := exists_unique_involution_sq ϕ
  have hzcomm : ∀ c ∈ C, c * z = z * c := by
    intro c hc
    have hw : c * z * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hzC) (C.inv_mem hc)
    have hww : (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
      calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    rcases huniq _ hw hww with h | h
    · exfalso
      apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · calc c * z = (c * z * c⁻¹) * c := by group
        _ = z * c := by rw [h]
  have hzC' : z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm (hsup ▸ hs)
    calc d * c * z = d * (c * z) := by group
      _ = d * (z * c) := by rw [hzcomm c hc]
      _ = (d * z) * c := by group
      _ = (z * d) * c := by rw [hcomm d hd z hzC]
      _ = z * (d * c) := by group
  refine false_of_weakClosed_involution hna S hz1 hzz hzC' fun g hg => ?_
  have hgC : g⁻¹ * z * g ∈ C := hfuse g z hzC hzz hz1 hg
  have hgg : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  rcases huniq _ hgC hgg with h | h
  · exfalso
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · exact h

end CFSG.CGT.T75H
