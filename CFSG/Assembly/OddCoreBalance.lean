module

public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.Milestones.CLS_component_free_centralizer_quotient_characteristic_two
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance

public section

namespace CFSG.Assembly.Dichotomy

theorem oddCore_eq_pPrimeCore (X : Type*) [Group X] :
    Assembly.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold Assembly.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem component_free_oddCore_balance (G : Type) [Group G] [Finite G]
    (hcomp : ¬ IsComponentType G) (t u : G)
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : Commute t u) :
    (oddCore (Subgroup.centralizer ({t} : Set G))).map
        (Subgroup.centralizer ({t} : Set G)).subtype ⊓
        Subgroup.centralizer ({u} : Set G) =
      (oddCore (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype ⊓
        Subgroup.centralizer ({t} : Set G) := by
  let P := Subgroup.zpowers t
  let Q := Subgroup.zpowers u
  have hP : IsPGroup 2 P :=
    IsPGroup.of_card (n := 1) (by simp [P, Nat.card_zpowers, ht])
  have hQ : IsPGroup 2 Q :=
    IsPGroup.of_card (n := 1) (by simp [Q, Nat.card_zpowers, hu])
  have hPt : Subgroup.centralizer (P : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    dsimp only [P]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hQu : Subgroup.centralizer (Q : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
    dsimp only [Q]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPQ : ⁅P, Q⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [hQu]
    dsimp only [P]
    rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le]
    simpa only [Set.singleton_subset_iff, SetLike.mem_coe,
      Subgroup.mem_centralizer_singleton_iff] using htu.eq
  have hchar (v : G) (hv : orderOf v = 2) :
      CFSG.IsCharacteristicP 2
        (Subgroup.centralizer ({v} : Set G) ⧸
          CFSG.pPrimeCore 2 (Subgroup.centralizer ({v} : Set G))) := by
    have hc := (CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two
      G hcomp v hv).1
    let C := Subgroup.centralizer ({v} : Set G)
    let e : (C ⧸ oddCore C) ≃* (C ⧸ CFSG.pPrimeCore 2 C) :=
      QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore C)
    change Subgroup.centralizer (CFSG.Open.pCore 2 (C ⧸ oddCore C) : Set _) ≤
      CFSG.Open.pCore 2 (C ⧸ oddCore C) at hc
    have he := CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2 e hc
    change Subgroup.centralizer (CFSG.pCore 2 (C ⧸ CFSG.pPrimeCore 2 C) : Set _) ≤
      CFSG.pCore 2 (C ⧸ CFSG.pPrimeCore 2 C)
    exact he
  have hbalance := CFSG.pPrimeCore_commuting_centralizers_balance G 2 P Q hP hQ hPQ
    (by rw [hPt]; exact hchar t ht) (by rw [hQu]; exact hchar u hu)
  dsimp only at hbalance
  rw [hPt, hQu] at hbalance
  rw [oddCore_eq_pPrimeCore, oddCore_eq_pPrimeCore]
  exact hbalance.1.trans hbalance.2

end CFSG.Assembly.Dichotomy
