module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDefs
import CFSG.HardMathSupport.Curtis.Proving.ToralNontrivialAction
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTower

public section

open CFSG.AGLEmbedding.ParabAutIrr CFSG.HardMathSupport.Curtis.Proving

namespace CFSG.HardMathSupport.Curtis.Coordinator

variable {p r : ℕ} {S : Type*} [Group S] {E : Subgroup (MulAut S)} {ζ γ : MulAut S}

theorem SPLAutData.isPGroup (h : SPLAutData p r S E ζ γ) : IsPGroup p E := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using h.elem.2 g g.2)⟩

theorem SPLAutData.comm_eq (h : SPLAutData p r S E ζ γ) {a b : MulAut S} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have := h.elem.1.1.1 ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem SPLAutData.commutator_eq_bot (h : SPLAutData p r S E ζ γ) :
    ⁅E, E⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha b hb
  exact (h.comm_eq hb ha)

theorem SPLAutData.gamma_mem_normalizer [Finite S] (h : SPLAutData p r S E ζ γ) :
    γ ∈ Subgroup.normalizer (E : Set (MulAut S)) := by
  have hmap : E.map (MulAut.conj γ).toMonoidHom ≤ E := by
    rintro _ ⟨w, hw, rfl⟩
    exact h.gamma_norm w hw
  have heq : E.map (MulAut.conj γ).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective])
  exact mem_normalizer_of_map_conj_eq heq

theorem SPLAutData.irrAct [Finite S] (h : SPLAutData p r S E ζ γ) : IrrAct γ E ⊥ := by
  have : Fact p.Prime := ⟨h.prime_p⟩
  have : Fact r.Prime := ⟨h.prime_r⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup (MulAut S)) := by
    intro a ha b hb
    rw [Subgroup.mem_bot, h.comm_eq ha hb]
    group
  have hpow : ∀ a ∈ E, a ^ p ∈ (⊥ : Subgroup (MulAut S)) := fun a ha =>
    Subgroup.mem_bot.2 (h.elem.2 a ha)
  have hidx : (⊥ : Subgroup (MulAut S)).relIndex E = p ^ 4 := by
    rw [Subgroup.relIndex_bot_left]
    exact h.card
  have hcX : ∀ x ∈ (⊥ : Subgroup (MulAut S)), γ * x * γ⁻¹ ∈ (⊥ : Subgroup (MulAut S)) := by
    intro x hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx]
    group
  have hnt : ∃ t ∈ E, γ * t * γ⁻¹ * t⁻¹ ∉ (⊥ : Subgroup (MulAut S)) := by
    obtain ⟨e, he, hne⟩ := h.gamma_act
    refine ⟨e, he, fun hmem => hne ?_⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have key := premise_of_nontrivial_action (X := (⊥ : Subgroup (MulAut S))) (T := E) (c := γ)
    h.dvd h.ndvd bot_le hcomm hpow hidx h.gamma_norm hcX h.gamma_pow hnt
  refine ⟨bot_le, fun W hW hWE hy => ?_⟩
  refine key W hW hWE (fun s hs v hv => ?_) (fun v hv => ?_)
  · have : s * v * s⁻¹ = v := by
      rw [h.comm_eq hs (hWE hv)]
      group
    rw [this]
    exact hv
  · exact (Subgroup.mem_normalizer_iff.1 hy v).1 hv

theorem SPLAutData.le_inn [Finite S] (h : SPLAutData p r S E ζ γ) (hR : OutPTwoGen S p) :
    E ≤ inn S := by
  have : Fact p.Prime := ⟨h.prime_p⟩
  obtain ⟨a, ha, b, hb, hgen⟩ := hR E h.isPGroup
  have hrel : p ^ 3 ≤ (⊥ : Subgroup (MulAut S)).relIndex E := by
    rw [Subgroup.relIndex_bot_left, h.card]
    exact Nat.pow_le_pow_right h.prime_p.pos (by norm_num)
  have hrank : NeedsThree E ⊥ :=
    needsThree_of_relIndex bot_le (h.commutator_eq_bot ▸ le_rfl)
      (fun a ha => Subgroup.mem_bot.2 (h.elem.2 a ha)) hrel
  have hyI : γ ∈ Subgroup.normalizer (inn S : Set (MulAut S)) := by
    rw [Subgroup.mem_normalizer_iff]
    exact fun x => ⟨fun hx => Subgroup.Normal.conj_mem inferInstance x hx γ,
      fun hx => by simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ hx γ⁻¹⟩
  exact le_of_two_generated h.isPGroup h.commutator_eq_bot.symm h.irrAct hrank
    h.gamma_mem_normalizer hyI ha hb hgen

end CFSG.HardMathSupport.Curtis.Coordinator
