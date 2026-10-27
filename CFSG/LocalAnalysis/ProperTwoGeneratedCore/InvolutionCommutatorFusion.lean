module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsRooting

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G}

theorem centralInvolution_conj_mem_eq_of_commutators {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z)
    (hP : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * x = 1 → y * y = 1 →
      (x * y) ^ 2 = 1 ∨ (x * y) ^ 2 = z)
    (hQ : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ i₁ ∈ (S : Subgroup G), ∃ i₂ ∈ (S : Subgroup G), i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
        Commute i₁ t ∧ Commute i₂ t ∧ (i₁ * i₂) ^ 2 = z)
    (g : G) (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g⁻¹ * z * g = z := by
  by_contra hne
  have ht : orderOf (g⁻¹ * z * g) = 2 := (orderOf_inv_mul_mul_eq z g).trans hz.2.1
  have htz : IsConj (g⁻¹ * z * g) z := isConj_iff.mpr ⟨g, by group⟩
  obtain ⟨k, -, hkS, -, hs2, hsne⟩ := centralInvolution_transport hz hg htz hne
  obtain ⟨i₁, hi₁S, i₂, hi₂S, hi₁, hi₂, hc₁, hc₂, h12⟩ := hQ _ hg ht hne
  have hconj : ∀ a : G, a * a = 1 → (k⁻¹ * a * k) * (k⁻¹ * a * k) = 1 := fun a ha => by
    calc (k⁻¹ * a * k) * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
      _ = 1 := by rw [ha]; group
  have hsq : ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) ^ 2 = k⁻¹ * z * k := by
    rw [← h12, pow_two, pow_two]
    group
  rcases hP _ (hkS i₁ hi₁S hc₁).1 _ (hkS i₂ hi₂S hc₂).1 (hconj i₁ hi₁) (hconj i₂ hi₂) with
    h1 | h1 <;> rw [hsq] at h1
  · rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by decide)
  · exact hsne h1

theorem false_of_involution_commutators (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : IsCentralInvolution (S : Subgroup G) z)
    (hP : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * x = 1 → y * y = 1 →
      (x * y) ^ 2 = 1 ∨ (x * y) ^ 2 = z)
    (hQ : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ≠ z →
      ∃ i₁ ∈ (S : Subgroup G), ∃ i₂ ∈ (S : Subgroup G), i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
        Commute i₁ t ∧ Commute i₂ t ∧ (i₁ * i₂) ^ 2 = z) : False := by
  obtain ⟨g, hgS, hgne⟩ := centralInvolution_exists_conj_mem_ne hsimple hnonab hz
  exact hgne (centralInvolution_conj_mem_eq_of_commutators hz hP hQ g hgS)

end CFSG.ProperTwoGeneratedCore.Assembly
