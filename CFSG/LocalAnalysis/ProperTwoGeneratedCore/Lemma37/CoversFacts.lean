module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelTransport

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC

@[expose] def CoverPairingVanishes (K : Type*) [Group K] (Q : Subgroup K) : Prop :=
  ∀ P : K → K → ZMod 2,
    (∀ a ∈ Q, ∀ a' ∈ Q, ∀ b, InCenterOf Q b → P (a * a') b = P a b + P a' b) →
    (∀ a ∈ Q, ∀ b b', InCenterOf Q b → InCenterOf Q b' → P a (b * b') = P a b + P a b') →
    (∀ a b, InCenterOf Q a → InCenterOf Q b → P a b = 0) →
    (∀ g ∈ Subgroup.normalizer (Q : Set K), ∀ a ∈ Q, ∀ b, InCenterOf Q b →
      P (g * a * g⁻¹) (g * b * g⁻¹) = P a b) →
    ∀ a ∈ Q, ∀ b, InCenterOf Q b → P a b = 0

@[expose] def CoverCenterCondition (K : Type*) [Group K] (Q : Subgroup K) : Prop :=
  8 ≤ Nat.card {w : K // InCenterOf Q w} ∨
    ∀ w, InCenterOf Q w → ∃ a ∈ Q, ∃ b ∈ Q, w = a * b * a⁻¹ * b⁻¹

structure BenderCoverFacts (K : Type*) [Group K] (Q : Subgroup K) : Prop where
  center : CoverCenterCondition K Q
  pairing : CoverPairingVanishes K Q

variable {K K' : Type*} [Group K] [Group K']

theorem coverPairingVanishes_map_mulEquiv (e : K ≃* K') {Q : Subgroup K}
    (h : CoverPairingVanishes K Q) : CoverPairingVanishes K' (Q.map e.toMonoidHom) := by
  intro P h₁ h₂ h₃ h₄ a ha b hb
  have hmem : ∀ {x : K}, x ∈ Q → e x ∈ Q.map e.toMonoidHom := fun hx =>
    Subgroup.mem_map_of_mem e.toMonoidHom hx
  have key := h (fun x y => P (e x) (e y))
    (fun x hx x' hx' y hy => by
      simpa using h₁ _ (hmem hx) _ (hmem hx') _ (inCenterOf_map_apply e hy))
    (fun x hx y y' hy hy' => by
      simpa using h₂ _ (hmem hx) _ _ (inCenterOf_map_apply e hy) (inCenterOf_map_apply e hy'))
    (fun x y hx hy => h₃ _ _ (inCenterOf_map_apply e hx) (inCenterOf_map_apply e hy))
    (fun g hg x hx y hy => by
      have hg' : e g ∈ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') := by
        rw [← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.mem_map_of_mem _ hg
      simpa using h₄ _ hg' _ (hmem hx) _ (inCenterOf_map_apply e hy))
    _ (Subgroup.mem_map_equiv.mp ha) _ ((inCenterOf_map_iff e b).mp hb)
  simpa using key

theorem coverCenterCondition_map_mulEquiv (e : K ≃* K') {Q : Subgroup K}
    (h : CoverCenterCondition K Q) : CoverCenterCondition K' (Q.map e.toMonoidHom) := by
  rcases h with h | h
  · left
    rw [Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv (fun w => inCenterOf_map_iff e w))]
    exact h
  · right
    intro w hw
    obtain ⟨a, ha, b, hb, hab⟩ := h _ ((inCenterOf_map_iff e w).mp hw)
    refine ⟨e a, Subgroup.mem_map_of_mem _ ha, e b, Subgroup.mem_map_of_mem _ hb, ?_⟩
    apply e.symm.injective
    simpa using hab

theorem benderCoverFacts_map_mulEquiv (e : K ≃* K') {Q : Subgroup K}
    (h : BenderCoverFacts K Q) : BenderCoverFacts K' (Q.map e.toMonoidHom) :=
  ⟨coverCenterCondition_map_mulEquiv e h.center, coverPairingVanishes_map_mulEquiv e h.pairing⟩

theorem benderCoverFacts_sylow [Finite K] {p : ℕ} [Fact p.Prime] {P : Sylow p K}
    (h : BenderCoverFacts K P) (Q : Sylow p K) : BenderCoverFacts K (Q : Subgroup K) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K P Q
  rw [Sylow.coe_subgroup_smul]
  exact benderCoverFacts_map_mulEquiv (MulAut.conj g) h

theorem benderCoverFacts_sylow_of_mulEquiv [Finite K] (e : K ≃* K')
    (h : ∃ Q : Sylow 2 K', BenderCoverFacts K' (Q : Subgroup K')) (P : Sylow 2 K) :
    BenderCoverFacts K (P : Subgroup K) := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 2 K,
      (P₀ : Subgroup K) = (Q : Subgroup K').comap e.toMonoidHom :=
    ⟨Q.comapOfInjective e.toMonoidHom e.injective (fun x _ => ⟨e.symm x, by simp⟩),
      Sylow.coe_comapOfInjective _ _ _ _⟩
  have h₀ := benderCoverFacts_map_mulEquiv e.symm hQ
  rw [← Subgroup.comap_equiv_eq_map_symm', ← hP₀] at h₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact benderCoverFacts_sylow h₀ P

end CFSG.ProperTwoGeneratedCore.Lemma37
