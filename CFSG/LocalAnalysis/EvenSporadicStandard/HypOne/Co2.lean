module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import Certificates.Certificate24444
public import Certificates.Certificate24445
public import Certificates.Certificate24446
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Models
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.HypOne.Co2

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore (commTT_iff rep_tp rep_arrayMap_ofNat co2Rep_natArr_iff)
open CFSG.Sporadic.Co2Cert (co2P co2PermEquiv co2Q_chainArrays co2Chain_check
  co2Q_originalSubgroup)
open CFSG.Sporadic.Co2Schreier (locZ locT locU zP tP uP rep_z rep_t rep_u locC_eq_centralizer
  locD_eq_centralizer card_locC card_locD card_locH3 invol_cases
  CTUC_Co2_all_involution_centralizers_odd_core_free)

theorem involution_cover :
    ∀ v ∈ co2P, orderOf v = 2 → ∃ r ∈ [locZ, locT, locU], ∃ c ∈ co2P, v = c * r * c⁻¹ := by
  intro v hv h2
  have ha : (⟨v, hv⟩ : co2P) * ⟨v, hv⟩ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← pow_two, ← h2, pow_orderOf_eq_one])
  have ha1 : (⟨v, hv⟩ : co2P) ≠ 1 := fun h => by
    have hv1 : v = 1 := congrArg Subtype.val h
    rw [hv1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have key : ∀ r : co2P, IsConj (⟨v, hv⟩ : co2P) r →
      ∃ c ∈ co2P, v = c * (r : Equiv.Perm (Fin 2300)) * c⁻¹ := by
    intro r hr
    obtain ⟨c, hc⟩ := isConj_iff.1 hr
    refine ⟨((c⁻¹ : co2P) : Equiv.Perm (Fin 2300)), (c⁻¹).2, ?_⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc' ⊢
    rw [← hc']
    group
  rcases invol_cases ⟨v, hv⟩ ha ha1 with h | h | h
  · obtain ⟨c, hc, e⟩ := key zP h
    exact ⟨locZ, by simp, c, hc, e⟩
  · obtain ⟨c, hc, e⟩ := key tP h
    exact ⟨locT, by simp, c, hc, e⟩
  · obtain ⟨c, hc, e⟩ := key uP h
    exact ⟨locU, by simp, c, hc, e⟩

theorem fourClassesLarge_z :
    FourClassesLarge ↥(centralizerIn co2P locZ) :=
  Certificates.certificate24444

theorem fourClassesLarge_t :
    FourClassesLarge ↥(centralizerIn co2P locT) :=
  Certificates.certificate24445

theorem fourClassesLarge_u :
    FourClassesLarge ↥(centralizerIn co2P locU) :=
  Certificates.certificate24446.1

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ co2P, orderOf v = 2 → FourClassesLarge (centralizerIn co2P v) := by
  refine fourClassesLarge_centralizerIn_of_reps co2P [locZ, locT, locU] involution_cover ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fourClassesLarge_z
  · exact fourClassesLarge_t
  · exact fourClassesLarge_u

theorem oddCore_centralizerIn :
    ∀ v ∈ co2P, orderOf v = 2 → CFSG.oddCore ↥(centralizerIn co2P v) = ⊥ := by
  intro v hv h2
  have ha : orderOf (⟨v, hv⟩ : co2P) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  exact CFSG.Sporadic.Co2Schreier.oddCore_bot_of_equiv
    (centralizerSubgroupEquiv co2P ⟨v, hv⟩).symm
    (CTUC_Co2_all_involution_centralizers_odd_core_free _ ha)

theorem center_native :
    Subgroup.center NativeSporadic.Co2 = ⊥ := by
  obtain ⟨hf, -, hs⟩ := CFSG.Sporadic.Co2.fam_co2_simplicity
  exact center_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)

theorem allInner_native :
    ∀ α : MulAut NativeSporadic.Co2, ∃ g : NativeSporadic.Co2, α = MulAut.conj g :=
  CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model NativeSporadic.Co2
    (MulEquiv.refl _)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Co2 :=
  hypothesisOne_of_innerModel co2PermEquiv center_native allInner_native oddCore_centralizerIn
    fourClassesLarge_centralizerIn

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.Co2 :=
  HasElemAbelianEight.of_mulEquiv co2PermEquiv.symm Certificates.certificate24446.2

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Co2) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  exact rowData_of_hasElemAbelianEight
    (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native)
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Co2) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_forall_eq_conj
    (forall_eq_conj_of_mulEquiv e.symm allInner_native)

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Co2) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.Co2
