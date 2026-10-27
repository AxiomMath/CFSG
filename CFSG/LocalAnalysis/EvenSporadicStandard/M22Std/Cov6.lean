module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def M22TwistedSylowData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G),
    orderOf t = 2 → (center L).map L.subtype = zpowers t → centralizer (L : Set G) = zpowers t →
    centralizer ({t} : Set G) = normalizer (L : Set G) →
    L.relIndex (centralizer ({t} : Set G)) = 2 → commutator L = ⊤ →
    IsSporadic (L ⧸ center L) .M22 →
    (∀ y ∈ centralizer ({t} : Set G), y ∉ L → orderOf y ≠ 2) →
    ∃ T : Sylow 2 (centralizer ({t} : Set G)),
      (∀ φ : MulAut (T : Subgroup (centralizer ({t} : Set G))),
        ∀ x : (T : Subgroup (centralizer ({t} : Set G))),
          ((x : centralizer ({t} : Set G)) : G) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L,
        ∃ z ∈ center (T : Subgroup (centralizer ({t} : Set G))),
          ((z : centralizer ({t} : Set G)) : G) = k⁻¹ * u * k

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_twisted (hTw : M22TwistedSylowData) (h : StdHyp G L) {t : G}
    (hc : CoverSetting L t) (hq : IsSporadic (L ⧸ center L) .M22)
    (hrel : L.relIndex (centralizer ({t} : Set G)) = 2)
    (hno : ∀ y ∈ centralizer ({t} : Set G), y ∉ L → orderOf y ≠ 2) : False := by
  have := h.simple
  obtain ⟨T, hfix, hcent⟩ := hTw G L t hc.orderOf_t hc.map_center hc.centralizer_L
    hc.centralizer_t hrel h.standard.1.1 hq hno
  obtain ⟨-, hfus, -, -⟩ :=
    ComponentClassification.StandardRecognition.rigid_index_two_centralizer_perfect_data_give_zStar
      hc.orderOf_t hc.le_centralizer hc.t_mem hrel.le T hfix hcent
      (fun x y _ hxL hx2 _ _ _ => absurd hx2 (hno x ‹_› hxL))
      (fun p hp hpL hp2 => absurd hp2 (hno p hp hpL))
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution h.nonabelian hc.orderOf_t
  apply hne
  have := hfus g⁻¹ (by rw [inv_inv]; exact mem_centralizer_singleton_iff.2 hcomm)
  simpa using this

end CFSG.EvenSporadicStandard.M22Std
