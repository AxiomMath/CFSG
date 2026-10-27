module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESteps
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

namespace ThmE

section QuotOdd


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem quotOdd_exists_W (hΩ : HypOmegaGen Ω) {S : Sylow 2 G} {W H : Subgroup G}
    (hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hC : CentPairs Ω (S : Subgroup G) W H) (hN : Odd (Nat.card N)) (hNH : N ≤ H) :
    ∃ Wb ∈ WSet (quotFamily Ω N), Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
      (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
      CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  set π := QuotientGroup.mk' N with hπ
  have hΩ' : HypOmegaGen (quotFamily Ω N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  obtain ⟨hWΩ, hWS, hWn⟩ := hW
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  refine ⟨W.map π, map_mem_WSet hΩ hΩ' hN hWΩ, Subgroup.map_mono hWS, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← AscQuot.map_conjSub, hWn s hs]
  intro Mb hMb _ Jb hJb Rb₁ Rb₂ hRb₁ hRb₁M hRb₁S hRb₂ hRb₂J hRb₂S hcb ab habR habW hab1 hab2
  obtain ⟨M₀, hM₀, rfl⟩ := hMb
  obtain ⟨M, hMΩ, J, hJ, R₁, R₂, hR₁, hR₁M, hR₂, hR₂J, hcomm, -, rfl, rfl, rfl⟩ :=
    exists_lift_pair_odd hΩ hΩ' hN hM₀ hJb hRb₁ hRb₁M hRb₂ hRb₂J hcb
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := by
    obtain ⟨M₁, -, hR₁M₁⟩ := exists_isSylow2In_of_mem_RSet hR₁
    obtain ⟨M₂, -, hR₂M₂⟩ := exists_isSylow2In_of_mem_RSet hR₂
    exact isPGroup_sup_of_commutes_or_eq hR₁M₁.2.1 hR₂M₂.2.1 hcomm
  have hPle : R₁ ⊔ R₂ ≤ (S : Subgroup G) ⊔ N :=
    le_sup_of_map_le (by rw [Subgroup.map_sup]; exact sup_le hRb₁S hRb₂S)
  obtain ⟨n, hn, hnle⟩ := exists_conj_le_of_le_sup hN hP2 hPle
  have hnπ : π n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hmapn : ∀ X : Subgroup G, (conjSub n X).map π = X.map π := fun X => by
    rw [AscQuot.map_conjSub, hnπ, conjSub_one]
  have hMn : conjSub n M ∈ Ω := hΩ.conjInvariant n M hMΩ
  have hJn : conjSub n J ∈ KPerp Ω (conjSub n M) := KPerp_conj hΩ.conjInvariant hJ n
  have hR₁n : conjSub n R₁ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₁ n
  have hR₂n : conjSub n R₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₂ n
  have hR₁nS : conjSub n R₁ ≤ (S : Subgroup G) := (conjSub_mono le_sup_left).trans hnle
  have hR₂nS : conjSub n R₂ ≤ (S : Subgroup G) := (conjSub_mono le_sup_right).trans hnle
  have hcommn : Commutes (conjSub n R₁) (conjSub n R₂) ∨ conjSub n R₂ = conjSub n R₁ := by
    rcases hcomm with h | h
    · exact Or.inl (h.conjSub n)
    · exact Or.inr (by rw [h])
  have habX : ab ∈ (conjSub n R₁ ⊔ conjSub n R₂).map π := by
    rw [Subgroup.map_sup, hmapn, hmapn]
    exact habR
  obtain ⟨b, hbX, rfl⟩ := habX
  have hbS : b ∈ (S : Subgroup G) := (sup_le hR₁nS hR₂nS) hbX
  obtain ⟨w, hwW, hwb⟩ := habW
  have hbW : b ∈ W := by
    have h1 : w⁻¹ * b ∈ (S : Subgroup G) ⊓ N := by
      refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hWS hwW)) hbS, ?_⟩
      have h0 : π (w⁻¹ * b) = 1 := by rw [map_mul, map_inv, hwb, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    rw [inf_bot_of_isPGroup hN hS2] at h1
    have : w = b := inv_mul_eq_one.mp h1
    rw [← this]
    exact hwW
  have hb2 : b * b = 1 := by
    have h1 : b * b ∈ (S : Subgroup G) ⊓ N :=
      ⟨(S : Subgroup G).mul_mem hbS hbS, (QuotientGroup.eq_one_iff _).mp
        (show π (b * b) = 1 by rw [map_mul]; exact hab2)⟩
    rw [inf_bot_of_isPGroup hN hS2] at h1
    exact h1
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hab1 (map_one π)
  have hMW : conjSub n M ⊓ W ∈ USet Ω :=
    inf_W_mem_USet' hΩ hWΩ hWS hMn hR₁n (conjSub_mono hR₁M) hR₁nS
  have hCb := hC _ hMn hMW _ hJn _ _ hR₁n (conjSub_mono hR₁M) hR₁nS hR₂n (conjSub_mono hR₂J)
    hR₂nS hcommn b hbX hbW hb1 hb2
  exact (centralizer_map_le hN hb2).trans (Subgroup.map_mono hCb)


theorem printedQuotOdd (r : ℕ) : PrintedQuotOdd r :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ hst hC hN hNH => quotOdd_exists_W hst.hyp hst.hW hC hN hNH⟩

instance instPrintedQuotOdd (r : ℕ) : PrintedQuotOdd r := printedQuotOdd r

end QuotOdd

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
