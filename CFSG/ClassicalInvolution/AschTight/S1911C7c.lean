module

public import CFSG.ClassicalInvolution.AschTight.S1911C7b

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem sup_oddCore_sup_eq (hd : Sec19DataT p f K z S W L t V)
    (hgen : (K ⊔ sec19Y K z) ⊔ V = sec19X K z)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    (K ⊔ oddCoreOf (sec19X K z)) ⊔ V = sec19X K z := by
  have hd0 := hd.toSec19Data
  have hYX : sec19Y K z ≤ sec19X K z := Hall196.sec19Y_le_sec19X K z
  have hXY : sec19X K z ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    (Hall196.gammaGen_le_centralizer _ z).trans (Hall196.centralizer_le_normalizer_sec19Y hd.tight)
  have hOY : oddCoreOf (sec19Y K z) ≤ oddCoreOf (sec19X K z) := oddCoreOf_le_oddCoreOf hYX hXY
  have hWKV : W ≤ K ⊔ V := by
    conv_lhs => rw [sup_eq_inf_sup hd]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (le_sec19X_member hd0) (oddCoreOf_le_self _))
      (hd.leW.trans (le_sec19X hd0))
  · have hY : sec19Y K z ≤ (K ⊔ oddCoreOf (sec19X K z)) ⊔ V := by
      calc sec19Y K z ≤ W ⊔ sec19Y K z := le_sup_right
        _ = oddCoreOf (sec19Y K z) ⊔ W := h1
        _ ≤ (K ⊔ oddCoreOf (sec19X K z)) ⊔ V := by
          refine sup_le (hOY.trans (le_sup_right.trans le_sup_left)) (hWKV.trans ?_)
          exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    calc sec19X K z = (K ⊔ sec19Y K z) ⊔ V := hgen.symm
      _ ≤ (K ⊔ oddCoreOf (sec19X K z)) ⊔ V :=
        sup_le (sup_le (le_sup_left.trans le_sup_left) hY) le_sup_right

omit [IsSimpleGroup G] in
theorem inf_sec19X_eq (hd : Sec19DataT p f K z S W L t V)
    (hX : (K ⊔ oddCoreOf (sec19X K z)) ⊔ V = sec19X K z) :
    (S : Subgroup G) ⊓ sec19X K z = (S : Subgroup G) ⊓ K ⊔ V := by
  have hd0 := hd.toSec19Data
  apply le_antisymm
  · rintro x ⟨hxS, hxX⟩
    have hVM : V ≤ Subgroup.normalizer ((K ⊔ oddCoreOf (sec19X K z) : Subgroup G) : Set G) :=
      (hd.leW.trans (le_sec19X hd0)).trans (sec19X_le_normalizer_sup hd0)
    have hx : x ∈ (((K ⊔ oddCoreOf (sec19X K z)) ⊔ V : Subgroup G) : Set G) := by
      rw [hX]
      exact hxX
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ V hVM] at hx
    obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hx
    have hvS : v ∈ (S : Subgroup G) := hd.hWS (hd.leW hv)
    have hmS : m ∈ (S : Subgroup G) := by
      have := (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem hvS)
      simpa using this
    have hONK : oddCoreOf (sec19X K z) ≤ Subgroup.normalizer (K : Set G) :=
      (oddCoreOf_le_self _).trans (sec19X_le_normalizer_member hd0)
    have hmK : m ∈ K := mem_of_isPGroup_of_mem_sup hONK (oddCoreOf_odd_natCard _) hm
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hmS))
    exact Subgroup.mul_mem_sup ⟨hmS, hmK⟩ hv
  · exact le_inf (sup_le inf_le_left (hd.leW.trans hd.hWS))
      (sup_le (inf_le_right.trans (le_sec19X_member hd0)) (hd.leW.trans (le_sec19X hd0)))

theorem isSL2Three_sec19X (hd : Sec19DataT p f K z S W L t V)
    (hgen : (K ⊔ sec19Y K z) ⊔ V = sec19X K z)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    IsSL2Three (sec19X K z) (K ⊔ oddCoreOf (sec19X K z)) (p ^ f) where
  le := sup_le (le_sec19X_member hd.toSec19Data) (oddCoreOf_le_self _)
  normal := sec19X_le_normalizer_sup hd.toSec19Data
  sl2 := isSL2ModOdd_sup_oddCore hd.toSec19Data
  cyclic := by
    obtain ⟨v, hvV, hV⟩ := exists_eq_zpowers_V hd
    refine ⟨v, le_sec19X hd.toSec19Data (hd.leW hvV),
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hd.hWS (hd.leW hvV))), ?_⟩
    rw [← hV]
    exact sup_oddCore_sup_eq hd hgen h1
  wreathed := fun P hP => by
    have h₀ : IsSylow2In ((S : Subgroup G) ⊓ K ⊔ V) (sec19X K z) := by
      rw [← inf_sec19X_eq hd (sup_oddCore_sup_eq hd hgen h1)]
      exact Hall196.isSylow2In_inf_of_le_normalizer S
        (hd.hSz.trans (Hall196.centralizer_le_normalizer_sec19X K z))
    exact Hall196.IsWreathed.of_isSylow2In h₀ (Hall196.isWreathed_inf_sup hd) hP

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
