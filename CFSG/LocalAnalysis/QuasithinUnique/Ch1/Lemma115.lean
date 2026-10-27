module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace Lemma115Hyp

section Local

variable {G : Type*} [Group G] [Finite G] {H S M : Subgroup G} {z : G}

theorem charTwo_inf (h : Lemma115Hyp H S M z) : CharTwo (H ⊓ M) :=
  charTwo_of_pCore_centralizer_le h.charTwo inf_le_right fun _ hx =>
    ⟨h.centralizer_le hx, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hx.1⟩

omit [Finite G] in
theorem inf_centralizer_le (h : Lemma115Hyp H S M z) :
    H ⊓ Subgroup.centralizer ({z} : Set G) ≤ H ⊓ M :=
  fun _ hx => ⟨hx.1, h.centralizer_z_le hx.2⟩

theorem oddCoreIn_properties (h : Lemma115Hyp H S M z) :
    oddCoreIn H ⊓ (H ⊓ M) = ⊥ ∧ oddCoreIn H ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ ∧
      (∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹) ∧
      ∀ x ∈ oddCoreIn H, ∀ y ∈ oddCoreIn H, x * y = y * x :=
  confined_involution_inverts_oddCoreIn h.charTwo_inf inf_le_left h.z_mem_H h.z_sq
    h.inf_centralizer_le

theorem inverts_oddCoreIn (h : Lemma115Hyp H S M z) :
    ∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹ :=
  h.oddCoreIn_properties.2.2.1

end Local

section Components

variable {G : Type*} [Group G] [Finite G] {H S M : Subgroup G} {z : G}

theorem component_action (h : Lemma115Hyp H S M z) {L : Subgroup G} (hL : IsComponentIn L H) :
    z ∈ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧ ¬ L ≤ M ∧
      CharTwo (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hn, hLA, hcomm, hchar⟩ := confined_sylow_central_involution_component_action
    h.charTwo_inf inf_le_left h.sylow h.z_mem h.z_central h.z_sq h.inf_centralizer_le hL
  exact ⟨hn, hcomm, fun hLM => hLA (le_inf hL.1 hLM), hchar⟩

theorem lemma115 (h : Lemma115Hyp H S M z) :
    CharTwo (H ⊓ M) ∧ (∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹) ∧
      ∀ L : Subgroup G, IsComponentIn L H → ⁅L, Subgroup.zpowers z⁆ = L ∧ ¬ L ≤ M :=
  ⟨h.charTwo_inf, h.inverts_oddCoreIn, fun _ hL =>
    let hc := h.component_action hL
    ⟨hc.2.1, hc.2.2.1⟩⟩

end Components

end Lemma115Hyp

end CFSG.QuasithinUnique
