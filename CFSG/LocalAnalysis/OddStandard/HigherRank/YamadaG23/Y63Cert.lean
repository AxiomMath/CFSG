module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Setup
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Thet
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63QU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63QCand
public import Certificates.Certificate441836

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three.Sec2

theorem y63_Z4cube {G : Type} [Group G] {M : Subgroup G}
    (e : ↥M ≃* (Fin 3 → Multiplicative (ZMod 4))) :
    Nat.card ↥M = 64 ∧ ∀ m ∈ M, m ^ 4 = 1 := by
  refine ⟨?_, fun m hm => ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_pi]
    simp [Fintype.card_multiplicative, ZMod.card]
  · have h : (e ⟨m, hm⟩) ^ 4 = 1 := by
      ext i
      simp only [Pi.pow_apply, Pi.one_apply]
      generalize e ⟨m, hm⟩ i = a
      revert a
      decide
    have h2 : (⟨m, hm⟩ : ↥M) ^ 4 = 1 := e.injective (by rw [map_pow, h, map_one])
    exact congrArg Subtype.val h2

theorem hsSylowFacts_of_cert
    (h26HS : Lemma26HS) (hfin : Finite TauCeti.SporadicName.HS.Group) : HSSylowFacts := by
  intro G _ _ Q P M S t hPQ hQcard hHS ht htP ht2 hMP hPN hMc hMiso hSP hS64 hSM hΩ hSt hMt
  obtain ⟨D, hT, hW, hMul, hI, hMs, hSs, hQs⟩ := Certificates.certificate441836
  obtain ⟨inst, f, hmul, h1, hfv, hgen⟩ := y63_tg _ hT hW hMul
  obtain ⟨ψ⟩ := y63_equiv_P f h26HS hfin hHS
  obtain ⟨hMcard, hM4⟩ := y63_Z4cube hMiso.some
  have hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hMc) ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨k, hk, φ, hφ⟩ := y63_setup (D := D) hmul h1 hI hMs hSs
    (fun k hk => (hQs k hk).1) (fun i => f (PresentedGroup.of i)) hgen (hfv 0) (hfv 1) (hfv 2)
    (hfv 3) (hfv 4) ψ hMP hPN hcomm hMcard hM4 hSP hS64 hSM hΩ hSt hMt
  have hQk := hQs k hk
  obtain ⟨Θ, hΘ⟩ := y63_theta hmul h1 φ hPQ hQcard ht htP ht2 hQk.1.1 hφ
  refine ⟨y63_card_cen hΘ hQk.2.1, ?_⟩
  obtain ⟨U, hUQ, hUZ, hUu, hUd⟩ := y63_U hΘ hQk.2.1 hQk.2.2.1
  exact ⟨U, hUQ, hUZ, hUu, y63_cand hΘ hQk.2.1 hQk.2.2.2 hUd⟩

end CFSG.OddStandard.HigherRank.YamadaG23
