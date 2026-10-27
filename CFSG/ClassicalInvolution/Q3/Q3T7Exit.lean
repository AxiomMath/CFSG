module

public import CFSG.ClassicalInvolution.Q3.Q3TWRowB
public import CFSG.ClassicalInvolution.Q3.Q3TWWOddMapPair
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinusMap
public import CFSG.ClassicalInvolution.Q3.Q3TWCollCert
public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TW
  CFSG.ClassicalInvolution.Asc77
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

section Chains

variable {G : Type} [Group G]

@[expose] def D4Chain3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
    (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
    (∀ i j : Fin 4, edgeD 4 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧ ⨆ k, U k = ⊤

@[expose] def B3Chain3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
    (∃ V, LinearBlockStandardPair (GaloisField 3 1) V (U 0) (U 1)) ∧
    (∃ V, SymplecticBlockPair (GaloisField 3 1) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

@[expose] def TD4Chain3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
    (∃ V, LinearBlockStandardPair (GaloisField 3 1) V (U 0) (U 1)) ∧
    (∃ V, TwistedB2BlockPair (minusCoeffs_irr 3 1) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

end Chains

section Exits

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem conclusionD_of_d4Chain3 (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)}
    (h : D4Chain3 Ω) : ConclusionD G := by
  obtain ⟨U, -, hcomm, hpair, hgen⟩ := h
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  obtain ⟨Ψ, -, -, -, -, hmodel, -⟩ := weakCT3_spinPlus hadm (by norm_num)
    (F := GaloisField 3 1) card_gf3 U hgen hcomm hpair
  exact Or.inl (oddLieType_of_model3 hnab hadm hmodel)

theorem conclusionD_of_b3Chain3
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)} (h : B3Chain3 Ω) :
    ConclusionD G := by
  obtain ⟨U, -, h02, h01, h12, hgen⟩ := h
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hW : WeakCT3OddMapPair 3 := weakCT3OddMapPair_of_collapse b3Collapse_proved le_rfl
  obtain ⟨Ψ, hker, hrange, -⟩ := hW (G := G) U
    (fun i j hij => by
      have hi : i.val = 0 := by omega
      have hj : j.val = 2 := by omega
      have e1 : i = 0 := Fin.ext hi
      have e2 : j = 2 := Fin.ext hj
      subst e1 e2
      exact h02)
    (fun i j hij hj => by
      have hi : i.val = 0 := by omega
      have hj' : j.val = 1 := by omega
      have e1 : i = 0 := Fin.ext hi
      have e2 : j = 1 := Fin.ext hj'
      subst e1 e2
      exact h01)
    (fun i j hi hj => by
      have hi' : i.val = 1 := by omega
      have hj' : j.val = 2 := by omega
      have e1 : i = 1 := Fin.ext hi'
      have e2 : j = 2 := Fin.ext hj'
      subst e1 e2
      exact h12)
  have hsurj : Function.Surjective Ψ := MonoidHom.range_eq_top.mp (hrange.trans hgen)
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadOdd 3 (GaloisField 3 1)) ⧸ Subgroup.center (spinGroup (quadOdd 3
        (GaloisField 3 1)))) .POmegaOdd 3 3 1 :=
    (curtisTitsConclusion_spinOdd.{0} hadm (by rw [card_gf3, pow_one])).1.2.2
  exact Or.inl (oddLieType_of_model3 hnab hadm
    (lieModel_of_surjective_simple3 hnab Ψ hsurj hker hmodel))

theorem conclusionD_of_td4Chain3
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)} (h : TD4Chain3 Ω) :
    ConclusionD G := by
  obtain ⟨U, -, h02, h01, h12, hgen⟩ := h
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hW : WeakCT3MinusMap 4 := weakCT3MinusMap_of_collapse td4Collapse_proved le_rfl
  obtain ⟨Ψ, hker, hψ⟩ := hW (G := G) U
    (fun i j hij => by
      have hi : i.val = 0 := by omega
      have hj : j.val = 2 := by omega
      have e1 : i = 0 := Fin.ext hi
      have e2 : j = 2 := Fin.ext hj
      subst e1 e2
      exact h02)
    (fun i j hij hj => by
      have hi : i.val = 0 := by omega
      have hj' : j.val = 1 := by omega
      have e1 : i = 0 := Fin.ext hi
      have e2 : j = 1 := Fin.ext hj'
      subst e1 e2
      exact h01)
    (fun i j hi hj => by
      have hi' : i.val = 1 := by omega
      have hj' : j.val = 2 := by omega
      have e1 : i = 1 := Fin.ext hi'
      have e2 : j = 2 := Fin.ext hj'
      subst e1 e2
      exact h12)
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← hψ k]
    exact Subgroup.map_le_range Ψ _
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ⧸
        Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) .POmegaMinus 4 3 1 :=
    (curtisTitsConclusion_spinMinus.{0} hirr hadm (by rw [card_gf3, pow_one])).1.2.2
  exact Or.inl (oddLieType_of_model3 hnab hadm
    (lieModel_of_surjective_simple3 hnab Ψ hsurj hker hmodel))

end Exits

end CFSG.ClassicalInvolution.Q3.Q3T7
