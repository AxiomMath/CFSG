module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.LieClAut

open Subgroup
open scoped commutatorElement
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner
  mem_sup_centralizer_of_three_pow_normalizer_cover)

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

theorem false_of_autThreePowInner_of_index (hq : Open.IsQuasisimple ↥L)
    (hC3 : ¬ 3 ∣ Nat.card (centralizer (L : Set Y)))
    (hX : AutThreePowInner (↥L ⧸ center ↥L)) (hN : ∃ N : Subgroup Y, N.Normal ∧ N.index = 3) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNn, hNi⟩ := hN
  have hcard : Nat.card (Y ⧸ N) = 3 := hNi
  have hcomm : ∀ a b : Y ⧸ N, a * b = b * a := by
    haveI := isCyclic_of_prime_card hcard
    exact fun a b => (IsCyclic.commGroup (α := Y ⧸ N)).mul_comm a b
  have hmk : ∀ g : Y, g ∈ N ↔ (g : Y ⧸ N) = 1 := fun g => (QuotientGroup.eq_one_iff g).symm
  have hLL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hLN : L ≤ N := by
    rw [← hLL, Subgroup.commutator_le]
    intro a _ b _
    rw [hmk]
    change QuotientGroup.mk' N ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hCN : centralizer (L : Set Y) ≤ N := fun c hc => by
    rw [hmk, ← orderOf_eq_one_iff]
    have h1 : orderOf (c : Y ⧸ N) ∣ 3 := hcard ▸ orderOf_dvd_natCard _
    have h2 : orderOf (c : Y ⧸ N) ∣ Nat.card (centralizer (L : Set Y)) := by
      refine (orderOf_map_dvd (QuotientGroup.mk' N) c).trans ?_
      have := orderOf_dvd_natCard (⟨c, hc⟩ : centralizer (L : Set Y))
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hC3
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hPN : (P : Subgroup Y) ≤ N := fun u hu => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
    have huk : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hu' := mem_sup_centralizer_of_three_pow_normalizer_cover hX L hLL (MulEquiv.refl _)
      (normalizer_eq_top (H := L) ▸ mem_top u) huk
    exact sup_le hLN hCN hu'
  have h3 := Subgroup.index_dvd_of_le hPN
  rw [hNi] at h3
  exact P.not_dvd_index h3

end CFSG.LocalAnalysis.RankThreeTheoremC.LieClAut
