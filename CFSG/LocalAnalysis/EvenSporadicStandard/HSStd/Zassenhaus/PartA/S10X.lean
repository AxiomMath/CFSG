module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Upper

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd
  CFSG.Open

section Main

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u y : G}
  {σ : Equiv.Perm (Fin 5)}

theorem tBar_ne_one (S : FusionSetup G L A t u) : tBar S ≠ 1 := by
  intro h1
  have hT := S.tu_sq
  have h2 : mkT (t * u) ⟨t, S.t_mem_Cen_tu⟩ = mkT (t * u) 1 := by rw [map_one]; exact h1
  rcases (mkT_eq_mkT_iff hT).1 h2 with h3 | h3
  · exact S.t_ne (congrArg Subtype.val h3).symm
  · have h4 : (1 : G) = t * (t * u) := congrArg Subtype.val h3
    have : u = 1 := by
      rw [← mul_assoc, S.t_sq, one_mul] at h4
      exact h4.symm
    exact S.u_ne this

theorem orderOf_tBar (S : FusionSetup G L A t u) : orderOf (tBar S) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact tBar_sq S) (tBar_ne_one S)

theorem fusionOddCore_quotT_eq_bot (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (hOH : fusionOddCore ↥(Cen (t * u)) = ⊥) : fusionOddCore (QuotT (t * u)) = ⊥ := by
  have hw : wOf (t * u) * wOf (t * u) = 1 := Subtype.ext S.tu_sq
  have hw1 : wOf (t * u) ≠ 1 := by
    intro h1
    have h2 : t * u = 1 := congrArg Subtype.val h1
    have hu : u = t := by
      rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right S.t_sq]
    apply hn
    rw [hu]
  exact s3l_fusionOddCore_quot_zpowers hw hw1 (wOf_central (t * u)) hOH

theorem quot_isSporadic (hHiS : Harris311HiS) (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (eA : ↥A ≃* MulAut (alternatingGroup (Fin 6)))
    (hK : CFSG.SectionRank.IsKGroupCat (QuotT (t * u)))
    (hOH : fusionOddCore ↥(Cen (t * u)) = ⊥) (F : Five G t u y σ)
    (hnc : ∃ h : ↥(Cen (t * u)), (h : G) * y ≠ y * h) :
    IsSporadic (QuotT (t * u)) .HS := by
  obtain ⟨e⟩ := exists_mulEquiv_cent S hn eA
  exact harris_hs hHiS hK (fusionOddCore_quotT_eq_bot S hn hOH) (orderOf_tBar S) e
    (mkT (t * u) F.yH) (F.orderOf_mkT_yH hnc) (five_nonempty_mulEquiv_centralizer F)

theorem card_cent_tBar (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (eA : ↥A ≃* MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(centralizer ({tBar S} : Set (QuotT (t * u)))) = 2880 := by
  obtain ⟨e⟩ := exists_mulEquiv_cent S hn eA
  rw [Nat.card_congr e.toEquiv, card_z2_mulAut_alt6]

theorem upper_bound (hHiS : Harris311HiS) (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (eA : ↥A ≃* MulAut (alternatingGroup (Fin 6)))
    (hK : CFSG.SectionRank.IsKGroupCat (QuotT (t * u)))
    (hOH : fusionOddCore ↥(Cen (t * u)) = ⊥) (F : Five G t u y σ)
    (hnc : ∃ h : ↥(Cen (t * u)), (h : G) * y ≠ y * h)
    (h5760 : Nat.card ↥(centralizer ((Vsub t u : Subgroup G) : Set G)) = 5760) :
    Nat.card ↥(Cen (t * u)) = 88704000 ∧
      {g : G | IsConj u g ∧ g ∈ Cen (t * u)}.ncard ≤ 26951 := by
  have hX := quot_isSporadic hHiS S hn eA hK hOH F hnc
  exact ⟨card_cen_tu_eq S hn hX, ncard_conj_u_le S hn hX (card_cent_tBar S hn eA) h5760⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
