module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneA
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneB
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.Sporadic.Schreier.Co1OddCore
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co2Schreier.OddCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.ComponentClassification.M12Cover
  CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Schreier (centralizerIn)

theorem exists_conj_of_isConj {v : GL24} (hv : v ∈ GA) {r : GA} (h : IsConj (⟨v, hv⟩ : GA) r) :
    ∃ c ∈ GA, v = c * (r : GL24) * c⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hv' : (⟨v, hv⟩ : GA) = c⁻¹ * r * c⁻¹⁻¹ := by
    rw [← hc]
    group
  refine ⟨((c⁻¹ : GA) : GL24), (c⁻¹ : GA).2, ?_⟩
  have := congrArg Subtype.val hv'
  simpa using this

theorem fourClassesLarge_centralizerIn_GA :
    ∀ v ∈ GA, orderOf v = 2 → FourClassesLarge (centralizerIn GA v) := by
  refine fourClassesLarge_centralizerIn_of_reps GA [aG, A₁, cG] ?_ ?_
  · intro v hv h2
    have hs : orderOf (⟨v, hv⟩ : GA) = 2 := by rw [Subgroup.orderOf_mk]; exact h2
    rcases involution_classes.1 ⟨v, hv⟩ hs with h | h | h
    · obtain ⟨c, hc, e⟩ := exists_conj_of_isConj hv h
      exact ⟨aG, by simp, c, hc, by rw [e, coe_aC]⟩
    · obtain ⟨c, hc, e⟩ := exists_conj_of_isConj hv h
      exact ⟨cG, by simp, c, hc, by rw [e, coe_cC]⟩
    · obtain ⟨c, hc, e⟩ := exists_conj_of_isConj hv h
      exact ⟨A₁, by simp, c, hc, by rw [e, coe_a₁]⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h
    · rw [h]
      exact fourClassesLarge_A
    · rw [h]
      exact fourClassesLarge_B
    · rw [h]
      exact fourClassesLarge_C

theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hx : e.symm y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e g)
  rw [h, Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e y, hx, map_one]

theorem assembly_oddCore_eq_oddCore (X : Type*) [Group X] :
    CFSG.Assembly.oddCore X = CFSG.oddCore X := rfl

theorem oddCore_free_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ b : B, orderOf b = 2 → CFSG.oddCore (Subgroup.centralizer ({b} : Set B)) = ⊥) :
    ∀ a : A, orderOf a = 2 → CFSG.oddCore (Subgroup.centralizer ({a} : Set A)) = ⊥ :=
  fun a ha => CFSG.Sporadic.Co2Schreier.oddCore_free_of_mulEquiv e h a ha

theorem center_GA : Subgroup.center GA = ⊥ := by
  have hs := CFSG.Sporadic.Co1.fam_co1_simplicity
  have hnp : ¬ (Nat.card NativeSporadic.Co1).Prime := by
    rw [CFSG.Sporadic.Co1.card_Co1]
    intro hp
    have h2 := hp.eq_one_or_self_of_dvd 2 (by norm_num)
    omega
  have h : Subgroup.center NativeSporadic.Co1 = ⊥ :=
    @center_eq_bot_of_isSimpleGroup NativeSporadic.Co1 Units.instGroup hs.1 hs.2.2 hnp
  exact @center_eq_bot_of_mulEquiv' NativeSporadic.Co1 GA Units.instGroup _ co1MatEquiv h

theorem hypothesisOne_GA :
    HypothesisOne GA := by
  have hCo2odd : ∀ a : CFSG.Sporadic.Co2Cert.co2P, orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥ :=
    fun a ha => CFSG.Sporadic.Co2Schreier.CTUC_Co2_all_involution_centralizers_odd_core_free a ha
  have hodd : ∀ b : NativeSporadic.Co1, orderOf b = 2 →
      CFSG.oddCore (Subgroup.centralizer ({b} : Set NativeSporadic.Co1)) = ⊥ := fun x hx =>
    (CFSG.Sporadic.Co1Schreier.OddCore.all_involution_centralizers_odd_core_free_of_inputs
      hCo2odd x hx).2.2.2
  have hGA : ∀ a : GA, orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set GA)) = ⊥ :=
    @oddCore_free_of_mulEquiv' GA NativeSporadic.Co1 _ Units.instGroup co1MatEquiv.symm hodd
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot center_GA)
    (@CFSG.Sporadic.Co1Schreier.OddCore.inner_of_mulEquiv GA NativeSporadic.Co1 _ Units.instGroup
      co1MatEquiv.symm (full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)) fun y hy => ?_
  have hy' : orderOf (y : GL24) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hy
  refine SmallNormalFree.centralizer_of_centralizerIn GA y ?_
    (fourClassesLarge_centralizerIn_GA y y.2 hy')
  rw [assembly_oddCore_eq_oddCore]
  exact hGA y hy

theorem hypothesisOne_native :
    HypothesisOne CFSG.Blueprint.NativeSporadic.Co1 :=
  @CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv GA NativeSporadic.Co1 _ Units.instGroup
    co1MatEquiv.symm hypothesisOne_GA

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Co1) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  exact @CFSG.Sporadic.Co1Schreier.OddCore.inner_of_mulEquiv Y NativeSporadic.Co1 _
    Units.instGroup e (full_automorphisms_inner_of_inputs
        Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)

theorem hypothesisOne_of_isSporadic_co1 {Y : Type} [Group Y] (h : IsSporadic Y .Co1)
    (hI : HypothesisOne NativeSporadic.Co1) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact @CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv NativeSporadic.Co1 Y Units.instGroup _
    e.symm hI

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
