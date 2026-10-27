module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24D4
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3Z CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Blueprint CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.WeakCT

theorem catalogIs_isD4of_of_stated {G : Type} [Group G] {p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 p f) :
    catalogIs G (CFSG.LocalAnalysis.GLTheoremA.S8.isD4of (p ^ f)) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, -⟩ := hadm
  let q : TauCeti.PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.D 4 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, not_false⟩
  obtain ⟨e⟩ := nonempty_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus 4 K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) ⟨.D 4 q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv) (by
      simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact ⟨.lie ⟨.D 4 q, hv⟩, show q.card = p ^ f by rw [TauCeti.PrimePower.card_def], ⟨e⟩⟩

section Recognition


theorem d4_recognition_catalog {Y : Type} [Group Y] (x y : Fin 4 → Y)
    (hrel : ∀ a b : Fin 4, edgeD 4 a b → RelsHold (edgeSix (x a) (y a) (x b) (y b)) a2Words)
    (hne : ∀ a b : Fin 4, edgeD 4 a b → x a ≠ 1)
    (hcomm : ∀ a b : Fin 4, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a →
      ∀ u ∈ ({x a, y a} : Set Y), ∀ v ∈ ({x b, y b} : Set Y), u * v = v * u)
    (hdvd : Nat.card (d4Group x y) ∣ 3 * 4952179814400) :
    catalogIs ↥(d4Group x y) (CFSG.LocalAnalysis.GLTheoremA.S8.isD4of 3) := by
  set U : Fin 4 → Subgroup Y := fun a => Subgroup.closure ({x a, y a} : Set Y) with hU
  set N : Subgroup Y := d4Group x y with hNdef
  have hUN : ∀ a, U a ≤ N := fun a => le_iSup U a
  have hgen : ⨆ a, (U a).subgroupOf N = ⊤ :=
    CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U
  have hcomm' : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
      ∀ a ∈ (U i).subgroupOf N, ∀ b ∈ (U j).subgroupOf N, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    exact Subtype.ext (d4_closure_commute (hcomm i j hij h1 h2) a.1 ha b.1 hb)
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e3⟩ := d4_ringEq
  have hpair : ∀ i j : Fin 4, edgeD 4 i j → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W
      ((U i).subgroupOf N) ((U j).subgroupOf N) := by
    intro i j hij
    have h := linearBlockStandardPair_of_relsHold (edgeSix (x i) (y i) (x j) (y j))
      (hrel i j hij) (hne i j hij)
    have h' := LinearBlockStandardPair.of_ringEquiv e3 h
    have h'' : LinearBlockStandardPair (GaloisField 3 1)
        (Subgroup.closure (Set.range (edgeSix (x i) (y i) (x j) (y j)))) (U i) (U j) := h'
    exact ⟨_, CFSG.GH74.L5U5.linearBlockStandardPair_subgroupOf h'' N (hUN i) (hUN j)⟩
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 (by norm_num)
  obtain ⟨Ψ, -, -, -, hZ, hmodel, -⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3W.weakCT3_spinPlus hadm (by norm_num : 3 ≤ 4) hF
      (X := ↥N) (fun a => (U a).subgroupOf N) hgen hcomm' hpair
  have hcz : Nat.card (Subgroup.center ↥N) ∣
      Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 4 (GaloisField 3 1)))) := by
    rw [hZ]
    exact Subgroup.card_map_dvd _ Ψ
  have hquot : Nat.card (↥N ⧸ Subgroup.center ↥N) = 4952179814400 := d4_card_pomegaPlus hmodel
  have hcardN : Nat.card ↥N = 4952179814400 * Nat.card (Subgroup.center ↥N) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥N), hquot]
  have hZdvd3 : Nat.card (Subgroup.center ↥N) ∣ 3 := by
    have h1 : 4952179814400 * Nat.card (Subgroup.center ↥N) ∣ 4952179814400 * 3 := by
      rw [← hcardN, mul_comm 4952179814400 3]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hZ1 : Nat.card (Subgroup.center ↥N) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZdvd3 with h | h
    · exact h
    · exfalso
      rw [h] at hcz
      exact d4_center_spin_not_dvd hcz
  have hZbot : Subgroup.center ↥N = ⊥ := Subgroup.card_eq_one.1 hZ1
  let eN : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  have hstated : StatedClassicalModel ↥N .POmegaPlus 4 3 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eN
      (hmodel.statedClassicalModel_of_ne_zero (by norm_num))
  have h := catalogIs_isD4of_of_stated hstated
  rwa [pow_one] at h

end Recognition

section Fi24


theorem catalogIs_fiN : catalogIs ↥TabFi24.fiN (CFSG.LocalAnalysis.GLTheoremA.S8.isD4of 3) := by
  refine d4_recognition_catalog TabFi24.dx TabFi24.dy TabFi24.d4_hrel TabFi24.d4_hne
    TabFi24.d4_hcomm ?_
  have h := Subgroup.card_dvd_of_le TabFi24.fiN_le_lvl_two
  rw [TabFi24.card_lvl_two] at h
  simpa using h

end Fi24

end CFSG.HardMathSupport.Dickson.I271
