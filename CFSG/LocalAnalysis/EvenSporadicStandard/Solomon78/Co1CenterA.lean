module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.Classes

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem twoA_cent_eq :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {aG}, (∀ q ∈ twoAQ, g * q = q * g) → g = 1 ∨ g = aG := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoA twoA_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaA twoA_cent_check twoA_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE aG twoAD1 twoABray = GA ⊓ Subgroup.centralizer {aG} := twoAE_eq
  rw [twoA_tower_prod, hE, card_cent_aG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {aG}) b twoARoots.length
  have hT2 : Nat.card T ≤ 2 := by omega
  have hmemT : ∀ g ∈ GA ⊓ Subgroup.centralizer {aG}, (∀ q ∈ twoAQ, g * q = q * g) → g ∈ T :=
    fun g hg hq => mem_towerStab_of_lt hg _ fun i hi => hq (b i) (hb i hi).1
  intro g hg hq
  have hgT := hmemT g hg hq
  have h1T : (1 : GL24) ∈ T := T.one_mem
  have haT : aG ∈ T := hmemT aG (Subgroup.mem_inf.2 ⟨iotaA_mem_GA,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) fun q hq =>
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (twoAQ_le hq)).2).symm
  by_contra hne
  have hg1 : g ≠ 1 := fun h => hne (Or.inl h)
  have hga : g ≠ aG := fun h => hne (Or.inr h)
  have hsub : ({1, aG, g} : Set GL24) ⊆ (T : Set GL24) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h1T, haT, hgT]
  have hcard3 : ({1, aG, g} : Set GL24).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [aG_ne_one.symm, hg1.symm]),
      Set.ncard_pair hga.symm]
  have h3 : 3 ≤ Nat.card T := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hcard3, ← Nat.card_coe_set_eq] at this
  omega

theorem centerInvAt_aC :
    CenterInvAt aC := by
  have key : ∀ a : GA, (a : GL24) = aG → CenterInvAt a := by
    intro a ha z _ hzc
    have hza : (z : GL24) * aG = aG * z := by
      have := commute_coe_of_central hzc a.2 rfl
      rwa [ha] at this
    have hzK : (z : GL24) ∈ GA ⊓ Subgroup.centralizer {aG} :=
      Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 hza⟩
    have hq : ∀ q ∈ twoAQ, (z : GL24) * q = q * z := by
      intro q hq
      obtain ⟨hqA, hqc⟩ := Subgroup.mem_inf.1 (twoAQ_le hq)
      refine commute_coe_of_central hzc hqA ?_
      rw [ha]
      exact Subgroup.mem_centralizer_singleton_iff.1 hqc
    rcases twoA_cent_eq _ hzK hq with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans ha.symm))
  exact key aC coe_aC

end CFSG.EvenSporadicStandard.Solomon78
