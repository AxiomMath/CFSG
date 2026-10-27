module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResTBasic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup Equiv Equiv.Perm
open scoped commutatorElement

set_option maxRecDepth 100000 in
theorem centralizer_alt_six (g : Perm (Fin 6)) (h : ∀ a ∈ alternatingGroup (Fin 6), g * a = a * g) :
    g = 1 := by
  have key : ∀ g : Equiv.Perm (Fin 6), g * (c[0, 1, 2] : Perm (Fin 6)) = c[0, 1, 2] * g →
      g * (c[0, 1, 3] : Perm (Fin 6)) = c[0, 1, 3] * g →
      g * (c[0, 4, 5] : Perm (Fin 6)) = c[0, 4, 5] * g → g = 1 := by
    decide
  apply key g
  · exact h _ (by rw [mem_alternatingGroup]; decide)
  · exact h _ (by rw [mem_alternatingGroup]; decide)
  · exact h _ (by rw [mem_alternatingGroup]; decide)

variable {Y : Type} [Group Y]

theorem lattice_of_triple_cover {z : Y} {K : Subgroup Y}
    (hKz : ∀ k ∈ K, z * k = k * z) (hΓ : ∀ g : Y, z * g = g * z → ∃ k ∈ K, g = k ∨ g = k * z)
    (σ : K →* Perm (Fin 6)) (hσ : Function.Surjective σ) (hZ : Nat.card σ.ker = 3)
    (hperf : ⁅(alternatingGroup (Fin 6)).comap σ, (alternatingGroup (Fin 6)).comap σ⁆ =
      (alternatingGroup (Fin 6)).comap σ)
    (M : Subgroup Y) (hMz : ∀ m ∈ M, z * m = m * z)
    (hMn : ∀ g : Y, z * g = g * z → ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    (∀ t ∈ ((alternatingGroup (Fin 6)).comap σ).map K.subtype, t ∈ M) ∨
      ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
  by_cases hT : ∀ t ∈ ((alternatingGroup (Fin 6)).comap σ).map K.subtype, t ∈ M
  · exact Or.inl hT
  right
  set A6 := alternatingGroup (Fin 6) with hA6
  set T := A6.comap σ with hTdef
  have hTn : T.Normal := Normal.comap inferInstance σ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic σ.ker := isCyclic_of_prime_card hZ
  have hZcomm : ∀ a ∈ σ.ker, ∀ b ∈ σ.ker, a * b = b * a := by
    intro a ha b hb
    let _ := IsCyclic.commGroup (α := σ.ker)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : σ.ker) ⟨b, hb⟩)
  let M₀ : Subgroup K := (M.comap K.subtype) ⊓ T
  have hM₀n : M₀.Normal := by
    refine ⟨fun n hn g => ⟨?_, hTn.conj_mem n hn.2 g⟩⟩
    show ((g * n * g⁻¹ : K) : Y) ∈ M
    have := hMn (g : Y) (hKz g g.2) (n : Y) hn.1
    simpa using this
  have hM₀A : M₀.map σ ≤ A6 := by
    rintro _ ⟨m, hm, rfl⟩
    exact hm.2
  have hσM : (M₀.map σ).Normal := Normal.map hM₀n σ hσ
  have hsimple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hN : ((M₀.map σ).subgroupOf A6).Normal := Normal.subgroupOf hσM A6
  rcases hsimple.eq_bot_or_eq_top_of_normal ((M₀.map σ).subgroupOf A6) with hbot | htop
  ·
    have hM₀Z : ∀ u ∈ M₀, σ u = 1 := by
      intro u hu
      have : (⟨σ u, hM₀A (mem_map_of_mem σ hu)⟩ : A6) ∈ (M₀.map σ).subgroupOf A6 :=
        mem_subgroupOf.2 (mem_map_of_mem σ hu)
      rw [hbot, mem_bot] at this
      exact congrArg Subtype.val this
    have hMZ : ∀ m ∈ M, ∃ k : K, σ k = 1 ∧ (m = (k : Y) ∨ m = (k : Y) * z) := by
      intro m hm
      obtain ⟨k, hk, hmk⟩ := hΓ m (hMz m hm)
      refine ⟨⟨k, hk⟩, ?_, hmk⟩
      apply centralizer_alt_six
      intro a ha
      obtain ⟨κ, rfl⟩ := hσ a
      have hκT : κ ∈ T := ha
      set k' : K := ⟨k, hk⟩ with hk'
      have hzκ : z * (κ : Y) = (κ : Y) * z := hKz κ κ.2
      have hzκ' : z * (κ : Y) * z⁻¹ = (κ : Y) := (mul_inv_eq_iff_eq_mul).2 hzκ
      have hmκm : m * (κ : Y) * m⁻¹ = (k : Y) * κ * (k : Y)⁻¹ := by
        rcases hmk with rfl | rfl
        · rfl
        · calc ((k : Y) * z) * (κ : Y) * ((k : Y) * z)⁻¹
              = (k : Y) * (z * (κ : Y) * z⁻¹) * (k : Y)⁻¹ := by group
            _ = (k : Y) * κ * (k : Y)⁻¹ := by rw [hzκ']
      have hmem : ((k' * κ * k'⁻¹ * κ⁻¹ : K) : Y) ∈ M := by
        have hκM := hMn (κ : Y) hzκ (m⁻¹) (inv_mem hm)
        have hmκ : m * ((κ : Y) * m⁻¹ * (κ : Y)⁻¹) ∈ M := mul_mem hm hκM
        have key : ((k' * κ * k'⁻¹ * κ⁻¹ : K) : Y) = m * ((κ : Y) * m⁻¹ * (κ : Y)⁻¹) := by
          calc ((k' * κ * k'⁻¹ * κ⁻¹ : K) : Y) = (k : Y) * κ * (k : Y)⁻¹ * (κ : Y)⁻¹ := by
                simp [hk']
            _ = m * (κ : Y) * m⁻¹ * (κ : Y)⁻¹ := by rw [hmκm]
            _ = m * ((κ : Y) * m⁻¹ * (κ : Y)⁻¹) := by group
        rw [key]
        exact hmκ
      have hu : k' * κ * k'⁻¹ * κ⁻¹ ∈ M₀ :=
        ⟨hmem, T.mul_mem (hTn.conj_mem κ hκT k') (T.inv_mem hκT)⟩
      have h1 := hM₀Z _ hu
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc σ k' * σ κ = (σ k' * σ κ * (σ k')⁻¹ * (σ κ)⁻¹) * (σ κ * σ k') := by group
        _ = σ κ * σ k' := by rw [h1, one_mul]
    intro a ha b hb
    obtain ⟨k₁, hk₁, h₁⟩ := hMZ a ha
    obtain ⟨k₂, hk₂, h₂⟩ := hMZ b hb
    have hk₁k₂ : (k₁ : Y) * k₂ = k₂ * k₁ := by
      have := hZcomm k₁ hk₁ k₂ hk₂
      exact congrArg Subtype.val this
    have hz₁ : z * (k₁ : Y) = (k₁ : Y) * z := hKz k₁ k₁.2
    have hz₂ : z * (k₂ : Y) = (k₂ : Y) * z := hKz k₂ k₂.2
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact hk₁k₂
    · calc (k₁ : Y) * ((k₂ : Y) * z) = ((k₁ : Y) * k₂) * z := by group
        _ = (k₂ * k₁) * z := by rw [hk₁k₂]
        _ = (k₂ : Y) * (z * k₁) := by rw [mul_assoc, ← hz₁]
        _ = ((k₂ : Y) * z) * k₁ := by group
    · calc ((k₁ : Y) * z) * k₂ = (k₁ : Y) * (z * k₂) := by group
        _ = (k₁ : Y) * (k₂ * z) := by rw [hz₂]
        _ = ((k₁ : Y) * k₂) * z := by group
        _ = (k₂ * k₁) * z := by rw [hk₁k₂]
        _ = (k₂ : Y) * ((k₁ : Y) * z) := by group
    · calc ((k₁ : Y) * z) * ((k₂ : Y) * z) = (k₁ : Y) * (z * k₂) * z := by group
        _ = (k₁ : Y) * (k₂ * z) * z := by rw [hz₂]
        _ = ((k₁ : Y) * k₂) * (z * z) := by group
        _ = ((k₂ : Y) * k₁) * (z * z) := by rw [hk₁k₂]
        _ = (k₂ : Y) * (k₁ * z) * z := by group
        _ = (k₂ : Y) * (z * k₁) * z := by rw [hz₁]
        _ = ((k₂ : Y) * z) * ((k₁ : Y) * z) := by group
  ·
    exfalso
    apply hT
    have hlift : ∀ g : K, σ g ∈ A6 → ∃ d ∈ M₀, σ d = σ g := by
      intro g hg
      have : (⟨σ g, hg⟩ : A6) ∈ (M₀.map σ).subgroupOf A6 := by rw [htop]; exact mem_top _
      exact mem_map.1 (mem_subgroupOf.1 this)
    have hcomm : ⁅T, T⁆ ≤ M₀ := by
      rw [Subgroup.commutator_le]
      intro t₁ ht₁ t₂ ht₂
      obtain ⟨m₁, hm₁, hσ₁⟩ := hlift t₁ ht₁
      obtain ⟨m₂, hm₂, hσ₂⟩ := hlift t₂ ht₂
      have hz₁ : m₁⁻¹ * t₁ ∈ σ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ₁, inv_mul_cancel]
      have hz₂ : m₂⁻¹ * t₂ ∈ σ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ₂, inv_mul_cancel]
      have hq : ∀ m ∈ M₀, QuotientGroup.mk' M₀ m = 1 := fun m hm =>
        (QuotientGroup.eq_one_iff m).2 hm
      have e₁ : QuotientGroup.mk' M₀ t₁ = QuotientGroup.mk' M₀ (m₁⁻¹ * t₁) := by
        have : t₁ = m₁ * (m₁⁻¹ * t₁) := by group
        conv_lhs => rw [this]
        rw [map_mul, hq m₁ hm₁, one_mul]
      have e₂ : QuotientGroup.mk' M₀ t₂ = QuotientGroup.mk' M₀ (m₂⁻¹ * t₂) := by
        have : t₂ = m₂ * (m₂⁻¹ * t₂) := by group
        conv_lhs => rw [this]
        rw [map_mul, hq m₂ hm₂, one_mul]
      have hc : ⁅m₁⁻¹ * t₁, m₂⁻¹ * t₂⁆ = 1 :=
        commutatorElement_eq_one_iff_commute.2 (hZcomm _ hz₁ _ hz₂)
      have : QuotientGroup.mk' M₀ ⁅t₁, t₂⁆ = 1 := by
        rw [map_commutatorElement, e₁, e₂, ← map_commutatorElement, hc, map_one]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hTM₀ : T ≤ M₀ := by
      calc T = ⁅T, T⁆ := hperf.symm
        _ ≤ M₀ := hcomm
    rintro _ ⟨κ, hκ, rfl⟩
    exact (hTM₀ hκ).1

end CFSG.EvenSporadicStandard.M24Std
