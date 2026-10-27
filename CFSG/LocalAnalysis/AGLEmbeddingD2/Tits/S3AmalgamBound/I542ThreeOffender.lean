module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.ComponentExclusion
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusion
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.FStar
public import CFSG.Quasithin.H13.NQCatSubnormalCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81 CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
open CFSG.HardMathSupport.Meierfrankenfeld
open scoped commutatorElement

theorem thompsonJ_star_le_centralizer
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hGN : GNSetting X T)
    (E' : Subgroup (X ⧸ gnC T)) [hE : E'.Normal] (h3 : ¬ 3 ∣ Nat.card E') :
    gnImg T (thompsonJ T) ≤ Subgroup.centralizer (E' : Set (X ⧸ gnC T)) := by
  classical
  set Y := X ⧸ gnC T with hY
  have hKY : CFSG.Open.IsKGroup Y := isKGroup_gnQuot hGN
  have hO2 : CFSG.pCore 2 Y = ⊥ := pCore_two_gnQuot hGN
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have key : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.centralizer (E' : Set Y) := by
    intro A hA
    set A' : Subgroup Y := A.map (QuotientGroup.mk' (gnC T)) with hA'
    have hAel : CFSG.IsElementaryAbelian 2 ↥A' := isElementaryAbelian_map_mk hA
    have hAbest : CFSG.RankThree.FFModules.IsBestOffender (gnRep hV) A' :=
      isBestOffender_gnRep hV hGN hA
    have hA2 : ∀ a ∈ A', a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
    apply Coordinator.le_centralizer_of_le_centralizer_genFitting hO2 hA2
    by_contra hF
    rcases Coordinator.exists_pCore_or_component_of_not_le_centralizer hF with
      ⟨p, hp, hpA⟩ | ⟨K, hK, hKA⟩
    · apply hpA
      have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := p)
        (X := E') (Subgroup.Normal.isSubnormal hE)
      by_cases hp2 : p = 2
      · subst hp2
        rw [hO2] at hle
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := by simpa using hle hy
        rw [hy1, one_mul, mul_one]
      by_cases hp3 : p = 3
      · subst hp3
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : IsPGroup 3 ((CFSG.pCore 3 ↥E').map E'.subtype) :=
          (show IsPGroup 3 (CFSG.pCore 3 ↥E') from CFSG.pCore_isPGroup).map _
        obtain ⟨k, hk⟩ := hy' ⟨y, hy⟩
        have hyk : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have hyE : y ∈ E' := by
          obtain ⟨z, -, rfl⟩ := hy
          exact z.2
        have hdvd : orderOf y ∣ Nat.card E' := by
          have := orderOf_dvd_natCard (⟨y, hyE⟩ : E')
          rwa [Subgroup.orderOf_mk] at this
        have hcop : Nat.Coprime (3 ^ k) (Nat.card E') :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
        have : y = 1 := orderOf_eq_one_iff.mp
          (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyk)) hdvd)
        rw [this, one_mul, mul_one]
      · have hp5 : 5 ≤ p := by
          have h2 := hp.two_le
          have : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
          omega
        have hR := GeneralFF.oddPrimeCoreExclusion Y (Additive (IntMod (gnV T) hV)) (gnRep hV) hinj
          hO2 p hp hp5 (CFSG.pCore p Y) A' CFSG.pCore_isPGroup CFSG.pCore_normal hAel hAbest
        have hAc : A' ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have : ⁅y, a⁆ ∈ ⁅CFSG.pCore p Y, A'⁆ := Subgroup.commutator_mem_commutator hy ha
          rw [hR, Subgroup.mem_bot] at this
          exact commutatorElement_eq_one_iff_mul_comm.mp this
        exact hAc.trans (Subgroup.centralizer_le hle)
    · apply hKA
      have eK' : ↥K ≃* ↥(K.map E'.subtype) :=
        Subgroup.equivMapOfInjective K E'.subtype E'.subtype_injective
      have hK'c : CFSG.IsComponent (K.map E'.subtype) :=
        ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK' hK.1,
          Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal hE)⟩
      have hK3 : ¬ 3 ∣ Nat.card (K.map E'.subtype) := by
        intro h
        apply h3
        refine h.trans ?_
        rw [Subgroup.card_map_of_injective E'.subtype_injective]
        exact Subgroup.card_subgroup_dvd_card K
      have hcomm := commutator_eq_bot_of_isComponent_of_not_three_dvd Y
        (Additive (IntMod (gnV T) hV)) (gnRep hV) hinj hKY hO2 A' hAel hAbest _ hK'c hK3
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have : ⁅y, a⁆ ∈ ⁅K.map E'.subtype, A'⁆ := Subgroup.commutator_mem_commutator hy ha
      rw [hcomm, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
  unfold gnImg thompsonJ
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hA => key A hA

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
