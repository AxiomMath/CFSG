module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverMain
public import Certificates.Certificate291372

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.PresentedWords CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

noncomputable abbrev Zp : Subgroup Q3 :=
  genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)

theorem index_Zp_le : Zp.FiniteIndex ∧ Zp.index ≤ 920808 :=
  Certificates.certificate291372.2.1

theorem card_Zp_le :
    Finite Zp ∧ Nat.card Zp ≤ 4089470473293004800 := by
  obtain ⟨hf10, hc10⟩ := card_PG10_le
  have hle := genSub_le_range m0_eq
  have hfinR : Finite theta.range := Finite.of_surjective _ theta.rangeRestrict_surjective
  exact ⟨Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle),
    (Subgroup.card_le_of_le hle).trans
      ((Nat.card_le_card_of_surjective _ theta.rangeRestrict_surjective).trans hc10)⟩

noncomputable abbrev toGQ : Q3 →* PG m0 X0 := toG m0_eq

theorem card_ker_toG :
    Nat.card toGQ.ker = 3 := by
  obtain ⟨hfinQ, hcardQ⟩ := card_Q3_le m0_eq index_Zp_le
  obtain ⟨-, hG⟩ := perfect_and_card_G
  have hcardQ' := CFSG.GH74.Generic.card_eq_card_mul_card_ker toGQ (toG_surjective m0_eq)
  have hker_le : Nat.card toGQ.ker ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ Nat.card toGQ.ker := by omega
    have := Nat.mul_le_mul_left (Nat.card (PG m0 X0)) h4
    omega
  have hker_pos : 0 < Nat.card toGQ.ker := Nat.card_pos
  set z : Q3 := PresentedGroup.of (zeta 10) with hz
  have hz1 : z ∈ toGQ.ker := MonoidHom.mem_ker.2 (toG_zeta m0_eq (by norm_num))
  have hord : 3 ∣ orderOf z := Certificates.certificate291372.2.2
  have hdvdK : orderOf z ∣ Nat.card toGQ.ker := by
    rw [← Subgroup.orderOf_mk z hz1]
    exact orderOf_dvd_natCard _
  exact le_antisymm hker_le (Nat.le_of_dvd hker_pos (hord.trans hdvdK))

theorem card_G :
    Nat.card (PG m0 X0) = 1255205709190661721292800 := by
  obtain ⟨hfinQ, hcardQ⟩ := card_Q3_le m0_eq index_Zp_le
  obtain ⟨-, hG⟩ := perfect_and_card_G
  have hcardQ' := CFSG.GH74.Generic.card_eq_card_mul_card_ker toGQ (toG_surjective m0_eq)
  rw [card_ker_toG] at hcardQ'
  omega

theorem card_Q3 :
    Nat.card Q3 = 920808 * 4089470473293004800 := by
  have h := CFSG.GH74.Generic.card_eq_card_mul_card_ker toGQ (toG_surjective m0_eq)
  rw [card_ker_toG, card_G] at h
  omega

theorem index_Zp :
    Zp.index = 920808 := by
  obtain ⟨-, hidx⟩ := index_Zp_le
  obtain ⟨-, hc⟩ := card_Zp_le
  have h := Zp.index_mul_card
  rw [card_Q3] at h
  by_contra hne
  have hlt : Zp.index < 920808 := lt_of_le_of_ne hidx hne
  have h2 : Zp.index * Nat.card Zp ≤ Zp.index * 4089470473293004800 :=
    Nat.mul_le_mul_left _ hc
  omega

theorem card_Zp :
    Nat.card Zp = 4089470473293004800 := by
  have h := Zp.index_mul_card
  rw [card_Q3, index_Zp] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
