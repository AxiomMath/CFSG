module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverCase3
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverPair
public import CFSG.LocalAnalysis.OddStandard.AltStdBalPartner

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem card_conjugate_eq (g : G) (H : Subgroup G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H :=
  card_cjSub g⁻¹ H

theorem mem_subStab_of_swap_of_unique (hU : WreathPairUniqueAt n)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 11 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) {g : G}
    (hg1 : cjSub (g⁻¹ * z * g) H = cjSub z H) (hg2 : cjSub (g⁻¹ * z * g) (cjSub z H) = H) :
    g ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  have hz2 := d.mul_self
  set w := g⁻¹ * z * g with hw
  have hw2 : w * w = 1 := by
    calc w * w = g⁻¹ * (z * z) * g := by rw [hw]; group
      _ = 1 := by rw [hz2]; group
  have h' := h.conj g
  have d' := d.conj g
  have hQ2' : Nat.card (CFSG.conjugate Q g) = 2 := by rw [card_conjugate_eq]; exact hQ2
  obtain ⟨e⟩ := h.iso
  obtain ⟨eH⟩ := hH.iso
  have hcardL : Nat.card (CFSG.conjugate L g) ≤ Nat.card H := by
    rw [card_conjugate_eq, Nat.card_congr e.toEquiv, Nat.card_congr eH.toEquiv]
  have hcomm := commutator_centralizer_le h' d' hQ2'
  have hHw : WreathPair (CFSG.conjugate L g) w n H :=
    wreathPair_of_swap hH (by omega) hw2 hg1 hcomm hcardL
  have hHg : WreathPair (CFSG.conjugate L g) w n (CFSG.conjugate H g) := hH.conjugate g
  have hu := hU G _ _ w h' d' hQ2' _ _ hHw hHg
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have key : cjSub g⁻¹ H = H ∨ cjSub g⁻¹ H = cjSub z H := by
    rcases hu with h1 | h1
    · exact Or.inl h1
    · right
      have : cjSub g⁻¹ H = cjSub w H := h1
      rw [this, hg1]
  have hgz : g⁻¹ * z = w * g⁻¹ := by rw [hw]; group
  have hconj : cjSub g⁻¹ (cjSub z H) = cjSub w (cjSub g⁻¹ H) := by
    rw [← cjSub_mul, ← cjSub_mul, hgz]
  have hmem : g⁻¹ ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
    rw [mem_subStab_pair_iff hne]
    rcases key with k1 | k1
    · left
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg1]
    · right
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg2]
  simpa using Subgroup.inv_mem _ hmem

end Swap

end CFSG.OddStandard.AltStdSec
