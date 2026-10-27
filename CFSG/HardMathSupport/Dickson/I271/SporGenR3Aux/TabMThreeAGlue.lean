module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAType
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACover
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence CFSG.YGroups.Y443

section ThreeA


theorem centThreeA_MGriess_of_zeta {ζ : MGriess} (hζ3 : orderOf ζ = 3)
    (hinv : tGriess * ζ * tGriess⁻¹ = ζ⁻¹)
    (h23 : 23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ} : Set MGriess)))
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({ζ} : Set MGriess)) ∧
      Nonempty (↥(Subgroup.centralizer ({ζ} : Set MGriess)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({ζ} : Set MGriess)) ≃*
          NativeSporadic.Fi24prime)) :
    CentThreeA MGriess := by
  intro k α hk3 hα2 hαc hαk hH
  have I := CFSG.YGroups.Y443.gmsInterfaces_MGriess
  have hG := gmsF1Type_MGriess_uncond
  have hex := oddExhaustive_MGriess I
  have hOT : OddTypeOrdersCF tGriess xGriess :=
    oddTypeOrdersCF_MGriess I hex monster_clauses_MGriess.1
      (natCard_cent_tGriess_of monster_clauses_MGriess.2.2)
      CFSG.Sporadic.Presentation.Th.finite_card_le CFSG.Monster.Existence.Compat.card_nativeTh
      exists_hn_two_point'
  have hcls : IsConj tGriess α := by
    rcases (CFSG.YGroups.Y443.monster_clauses_MGriess).2.1 α hα2 with h | h
    · exact h
    · exfalso
      have h2 := (isTwoBCentralizer_MGriess α h).2.2.2.2.1
      rw [hαc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  have h23k : 23 ∣ Nat.card ↥(Subgroup.centralizer ({α} : Set MGriess) ⊓
      Subgroup.centralizer ({k} : Set MGriess)) := by
    obtain ⟨f⟩ := hH
    rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num
  have hn1 : ¬ 23 ∣ oddTypeStab 1 := by norm_num [oddTypeStab]
  have hn2 : ¬ 23 ∣ oddTypeStab 2 := by norm_num [oddTypeStab]
  obtain ⟨hy₀, hk₀, hζe⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabMThreeA.oddNbrType_zero_of_dvd I hG hex hOT
      (IsConj.refl tGriess) hζ3 hinv h23 hn1 hn2
  have hclass : ∀ x y : MGriess, IsConj tGriess x → y ∈ oddNbr tGriess xGriess x →
      OddNbrType xGriess x y 0 → IsConj (x * y) ζ := by
    intro x y hx hy hk
    have h := isConj_mul_of_oddNbrType I hy₀ hk₀ hx hy hk
    rwa [hζe] at h
  have hkζ : IsConj k ζ :=
    CFSG.HardMathSupport.Dickson.I271.TabMThreeA.isConj_of_oddNbrType_zero I hG hex hOT hcls hk3
      hαk h23k hn1 hn2 hclass
  exact quasisimple_centralizer_of_isConj (G := MGriess) (Q := NativeSporadic.Fi24prime)
    (D := Subgroup.centralizer ({ζ} : Set MGriess)) rfl hkζ hq

end ThreeA

section Transfer


theorem centThreeA_M_of_MGriess (h : CentThreeA MGriess) :
    CentThreeA (NativeSporadic.Carrier .M) := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  exact CentThreeA.of_equiv e.symm h

end Transfer

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
