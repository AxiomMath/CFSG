module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfectMat
public import CFSG.Sporadic.Co1Block.TwoACent
public import Certificates.Certificate24510

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.ComponentClassification.M12Cover

theorem twoA_cent_sq :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {aG}, (∀ q ∈ twoAQ, g * q = q * g) → g * g = 1 := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoA twoA_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaA twoA_cent_check twoA_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE aG twoAD1 twoABray = GA ⊓ Subgroup.centralizer {aG} := twoAE_eq
  rw [twoA_tower_prod, hE, card_cent_aG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {aG}) b twoARoots.length
  have hT2 : Nat.card T ≤ 2 := by omega
  intro g hg hq
  have hgT : g ∈ T := mem_towerStab_of_lt hg _ fun i hi => hq (b i) (hb i hi).1
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hdvd : orderOf (⟨g, hgT⟩ : T) ∣ 2 := by
    have h := orderOf_dvd_natCard (⟨g, hgT⟩ : T)
    rcases (by omega : Nat.card T = 1 ∨ Nat.card T = 2) with h1 | h1
    · rw [h1] at h
      exact h.trans (one_dvd _)
    · rw [h1] at h
      exact h
  have hsq : (⟨g, hgT⟩ : T) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
  have := congrArg Subtype.val hsq
  simpa [pow_two] using this

theorem fourClassesLarge_A :
    FourClassesLarge ↥(GA ⊓ Subgroup.centralizer {aG}) := by
  have hrepB := rep_brayElts (bidx := twoABray) rep_iotaA (centCheck_parts twoA_cent_check).1
  have hBGK : ∀ g ∈ brayEltsG aG twoAD1 twoABray, g ∈ GA ⊓ Subgroup.centralizer {aG} :=
    fun g hg => twoAE_le (Subgroup.subset_closure hg)
  obtain ⟨P, hPK, hP, hQ⟩ := exists_perfect_of_check hrepB hBGK Certificates.certificate24510
  have hQP : twoAQ ≤ P := by
    show Subgroup.closure (twoAQg '' {l | l < twoAQRows.length}) ≤ P
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < twoAQRows.length := hl
    refine hQ _ ?_ _ (qRep_twoA l hl')
    rw [List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem hl'
  refine fourClassesLarge_of_perfect_le hPK hP fun x hx hxP _ => ?_
  rw [pow_two]
  exact twoA_cent_sq x hx fun q hq => (hxP q (hQP hq)).symm

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
