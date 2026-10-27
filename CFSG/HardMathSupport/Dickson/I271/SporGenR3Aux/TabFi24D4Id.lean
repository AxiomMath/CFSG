module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24A2
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Gen
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.Q3.Q3WSimply
public import CFSG.GH74.L5U5.Ident
public import CFSG.ClassicalInvolution.Generic.Base
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3Z CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Blueprint CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.WeakCT

theorem d4_closure_commute {Y : Type} [Group Y] {S T : Set Y}
    (h : ∀ u ∈ S, ∀ v ∈ T, u * v = v * u) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have h1 : ∀ u ∈ S, ∀ y ∈ Subgroup.closure T, u * y = y * u := by
    intro u hu y hy
    have hle : Subgroup.closure T ≤ Subgroup.centralizer ({u} : Set Y) := by
      rw [Subgroup.closure_le]
      intro v hv
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h u hu v hv).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  intro x hx y hy
  have hle : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set Y) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y' hy'
    exact (h1 u hu y' hy').symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem d4_center_spin_not_dvd :
    ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 4 (GaloisField 3 1)))) := by
  have hn3 : 3 ≤ 4 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 4 := ⟨by norm_num⟩
  haveI : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 4 (GaloisField 3 1))) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := GaloisField 3 1) hn3
  exact OrthAut.not_dvd_card_center_spin (Spin.quadPlus 4 (GaloisField 3 1))
    (range_spinMatrix_quadPlus hn3) hZ hcomap
    (fun x hx => OrthAut.spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx))
    (p := 3) (by norm_num)

theorem d4_card_pomegaPlus {Q : Type} [Group Q] (h : LieModel Q .POmegaPlus 4 3 1) :
    Nat.card Q = 4952179814400 := by
  have hc := (card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num)
      (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.1 rfl
  rw [hc]
  decide +kernel

theorem d4_ringEq : Nonempty (ZMod 3 ≃+* GaloisField 3 1) := by
  have := Fintype.ofFinite (ZMod 3)
  have := Fintype.ofFinite (GaloisField 3 1)
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
    simp)⟩

@[expose] def d4Group {Y : Type} [Group Y] (x y : Fin 4 → Y) : Subgroup Y :=
  ⨆ a, Subgroup.closure ({x a, y a} : Set Y)

section Recognition


theorem d4_recognition {Y : Type} [Group Y] (x y : Fin 4 → Y)
    (hrel : ∀ a b : Fin 4, edgeD 4 a b → RelsHold (edgeSix (x a) (y a) (x b) (y b)) a2Words)
    (hne : ∀ a b : Fin 4, edgeD 4 a b → x a ≠ 1)
    (hcomm : ∀ a b : Fin 4, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a →
      ∀ u ∈ ({x a, y a} : Set Y), ∀ v ∈ ({x b, y b} : Set Y), u * v = v * u)
    (hdvd : Nat.card (d4Group x y) ∣ 3 * 4952179814400) :
    Nat.card (d4Group x y) = 4952179814400 ∧ IsSimpleGroup (d4Group x y) ∧
      (∃ a b : d4Group x y, a * b ≠ b * a) ∧ LeafType 3 (d4Group x y) := by
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
  obtain ⟨Ψ, -, -, hqs, hZ, hmodel, -⟩ :=
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
  have hcardN' : Nat.card ↥N = 4952179814400 := by rw [hcardN, hZ1, mul_one]
  let eN : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  have hsimple : IsSimpleGroup ↥N := eN.isSimpleGroup_congr.1 hqs.2.1
  have hnab : ∃ a b : ↥N, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center ↥N = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro b
      exact hcon b a
    rw [hZbot] at htop
    haveI := hsimple
    exact bot_ne_top htop
  have hstated : StatedClassicalModel ↥N .POmegaPlus 4 3 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eN
      (hmodel.statedClassicalModel_of_ne_zero (by norm_num))
  have hleaf : LeafType 3 ↥N :=
    leafType_of_pow_four_dvd Nat.prime_three (isChevSimple_of_pomegaPlus hstated)
      (by rw [hcardN']; norm_num)
  exact ⟨hcardN', hsimple, hnab, hleaf⟩

end Recognition

end CFSG.HardMathSupport.Dickson.I271
