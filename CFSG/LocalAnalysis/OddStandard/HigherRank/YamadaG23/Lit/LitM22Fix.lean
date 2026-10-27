module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitM22Cent

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem lit_inner_invol_conj {M : Type*} [Group M] (N : Subgroup M)
    (hcenter : Subgroup.center N = ⊥) (α : MulAut N) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    (hα : α ∈ inner N) :
    ∃ u : M, orderOf u = 2 ∧ u ∈ N ∧ ∀ h : N, (α h : M) = u * h * u⁻¹ := by
  obtain ⟨k, rfl⟩ := hα
  have hconj : ∀ h : N, (((MulAut.conj : N →* MulAut N) k) h : M) = (k : M) * h * (k : M)⁻¹ :=
    fun h => rfl
  have hz : ∀ z : N, k * (k * z * k⁻¹) * k⁻¹ = z := by
    intro z
    have := congrArg (fun φ : MulAut N => φ z) hα2
    simpa using this
  have hk2 : (k : M) * (k : M) = 1 := by
    have hc : k * k ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      calc z * (k * k) = (k * (k * z * k⁻¹) * k⁻¹) * (k * k) := by rw [hz z]
        _ = (k * k) * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hk1 : (k : M) ≠ 1 := by
    intro h1
    apply hα1
    have : k = 1 := Subtype.ext h1
    rw [this, map_one]
  exact ⟨(k : M), orderOf_eq_prime (by rw [sq]; exact hk2) hk1, k.2, hconj⟩

theorem lit_outer_invol_conj {M : Type*} [Group M] (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) (α : MulAut N) (hα2 : α * α = 1)
    (hα : α ∉ inner N) :
    ∃ u : M, orderOf u = 2 ∧ δ⁻¹ * u ∈ N ∧ ∀ h : N, (α h : M) = u * h * u⁻¹ := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  exact ⟨u, orderOf_eq_prime (by rw [sq]; exact hu2) hu1, hu, hαg⟩

theorem lit_card_fixSub {M : Type*} [Group M] (N : Subgroup M) (α : MulAut N) (u : M)
    (hα : ∀ h : N, (α h : M) = u * h * u⁻¹) :
    Nat.card ↥(fixSub α) = Nat.card ↥(centralizerIn N u) := by
  rw [← map_fixSub_conjOn N α u hα, Subgroup.card_map_of_injective N.subtype_injective]

theorem lit_m22_fix_card
    (α : MulAut NativeSporadic.M22) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ 9 ∣ Nat.card ↥(fixSub α) := by
  by_cases hα : α ∈ inner NativeSporadic.M22
  · obtain ⟨u, ho, hu, hconj⟩ :=
      lit_inner_invol_conj NativeSporadic.M22 m22_center_eq_bot' α hα2 hα1 hα
    rw [lit_card_fixSub _ α u hconj, lit_m22_inner_card u hu ho]
    norm_num
  · obtain ⟨u, ho, hu, hconj⟩ := lit_outer_invol_conj NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hα2
      hα
    rw [lit_card_fixSub _ α u hconj]
    rcases lit_m22_outer_card u hu ho with h | h <;> rw [h] <;> norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
