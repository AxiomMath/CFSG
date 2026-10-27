module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem charTwo_of_forall_not_isComponentIn {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hE : ∀ K : Subgroup G, ¬ IsComponentIn K X) (hodd : oddCoreIn X = ⊥) : CharTwo X := by
  have hlayer : CFSG.layer ↥X = ⊥ := by
    refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK =>
      hE (K.map X.subtype) ⟨Subgroup.map_subtype_le K, ?_⟩
    have : (K.map X.subtype).subgroupOf X = K :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective K
    rw [this]
    exact hK
  have hF : CFSG.generalizedFitting ↥X = CFSG.fittingSubgroup ↥X := by
    rw [CFSG.generalizedFitting, hlayer, sup_bot_eq]
  have hfit : CFSG.fittingSubgroup ↥X ≤ CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      have hq : Nat.Prime p.1.1 := Nat.prime_of_mem_primeFactors p.1.2
      have hqodd : Odd p.1.1 := hq.odd_of_ne_two hp
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥X)).exists_card_eq
      rw [hn]
      exact hqodd.pow
  have hmap : (CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X).map X.subtype = pCoreOf 2 X ⊔ oddCoreIn X := by
    rw [Subgroup.map_sup, pCoreOf]
    rfl
  intro x hx
  have hx' : (⟨x, hx.1⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥X : Set ↥X) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 X ⊔ oddCoreIn X := by
      rw [← hmap]
      exact ⟨w, hfit hw, rfl⟩
    rw [hodd, sup_bot_eq] at hw'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 _ hw')
  have := CFSG.centralizer_generalizedFitting_le ↥X hx'
  rw [hF] at this
  have hmem : x ∈ pCoreOf 2 X ⊔ oddCoreIn X := by
    rw [← hmap]
    exact ⟨_, hfit this, rfl⟩
  rw [hodd, sup_bot_eq] at hmem
  exact hmem

end CFSG.QuasithinUnique
