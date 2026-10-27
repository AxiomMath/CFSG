module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveNoCompK
public import Certificates.Certificate17489
public import Certificates.Certificate17494
public import Certificates.Certificate17495
public import Certificates.Certificate17540
public import Certificates.Certificate17541
public import Certificates.Certificate17542
public import Certificates.Certificate17543
public import Certificates.Certificate17544
public import Certificates.Certificate17598
public import Certificates.Certificate17613
public import Certificates.Certificate17614
public import Certificates.Certificate17615
public import Certificates.Certificate17616
public import Certificates.Certificate17617
public import Certificates.Certificate17618
public import Certificates.Certificate17619
public import Certificates.Certificate17625
public import Certificates.Certificate17626

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.MonsterFiveB

open CFSG.Open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus

theorem inv_conj_alg {G : Type*} [Group G] {T U h c : G} (hU : T * U * T⁻¹ = U⁻¹)
    (e : c * h = U * c) : (c⁻¹ * T * c) * h * (c⁻¹ * T * c)⁻¹ = h⁻¹ := by
  have hU' : U = c * h * c⁻¹ := by rw [e, mul_inv_cancel_right]
  subst hU'
  calc (c⁻¹ * T * c) * h * (c⁻¹ * T * c)⁻¹
      = c⁻¹ * (T * (c * h * c⁻¹) * T⁻¹) * c := by group
    _ = c⁻¹ * (c * h * c⁻¹)⁻¹ * c := by rw [hU]
    _ = h⁻¹ := by group

theorem invertedByTwoA_of_conj
    (ht : Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) = 2 * monsterBabyOrder)
    (ho : orderOf tGmat = 2) {h α : Gmat} (hα : IsConj tGmat α) (hinv : α * h * α⁻¹ = h⁻¹) :
    InvertedByTwoA h := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hα
  refine ⟨α, ?_, ?_, hinv⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) tGmat
    simp only [MulAut.conj_apply] at h1
    rw [← hc, h1, ho]
  · rw [← hc, natCard_centralizer_conj', ht]

theorem bOK
    (ht : Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) = 2 * monsterBabyOrder)
    (ho : orderOf tGmat = 2) (W : BWit) (h : ∀ p ∈ bEqs W, wordLin p.1 = wordLin p.2) :
    FiveBOrInv xFiveB (gw (rhsW W.v)) := by
  have hall : ∀ p ∈ bEqs W, gw p.1 = gw p.2 := fun p hp => Subtype.ext (h p hp)
  by_cases hW : W.inv = true
  · refine Or.inl ?_
    have m1 : (rhsW W.v ++ W.c, W.c ++ W.u) ∈ bEqs W := by
      unfold bEqs; rw [if_pos hW]; simp
    have m2 : (tW ++ W.u ++ tW ++ W.u, []) ∈ bEqs W := by
      unfold bEqs; rw [if_pos hW]; simp
    have e1 := hall _ m1
    have e2 := hall _ m2
    simp only [gw_append, gw_nil, gw_tW] at e1 e2
    have hT2 : tGmat * tGmat = 1 := by
      have := pow_orderOf_eq_one tGmat
      rwa [ho, pow_two] at this
    have hinv : tGmat * gw W.u * tGmat⁻¹ = (gw W.u)⁻¹ :=
      inv_of_sq hT2 (by simpa [mul_assoc] using e2)
    exact invertedByTwoA_of_conj ht ho (α := (gw W.c)⁻¹ * tGmat * gw W.c)
      (isConj_iff.2 ⟨(gw W.c)⁻¹, by group⟩) (inv_conj_alg hinv e1)
  · refine Or.inr ?_
    have m1 : (rhsW W.v ++ W.c, W.c ++ fiveGens[8]!) ∈ bEqs W := by
      unfold bEqs; rw [if_neg hW]; simp
    have e1 := hall _ m1
    simp only [gw_append] at e1
    have hx : xFiveB = gw fiveGens[8]! := rfl
    refine ⟨1, Nat.coprime_one_left 5, ?_⟩
    rw [pow_one, hx]
    exact isConj_of_eq e1

theorem bBatch {idxs : List ℕ} (h : ∀ p ∈ bEqsOf idxs, wordLin p.1 = wordLin p.2) {k : ℕ}
    (hk : k ∈ idxs) : ∀ p ∈ bEqs bWits[k]!, wordLin p.1 = wordLin p.2 := fun e he =>
  h e (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, he⟩)

theorem gw_rhsW_eq_prodAsc
    (v : Array ℕ) :
    gw (rhsW v) = prodAsc fiveGenG v := by
  rw [← lift_wordF_eq_rhsW (powEqs_of_relEqs relEqs_all) v]
  exact lift_wordF_eq fiveGenG v

set_option maxRecDepth 100000 in
theorem bWits_v : ∀ k < 31,
    (bWits[k]!).tgt = k ∧
      (bWits[k]!).v = _root_.Timmesfeld.PcReg.digitsOf 5 9 _root_.Timmesfeld.PcFive.repIdx[k]! := by
  have h : (List.range 31).all (fun k => (bWits[k]!).tgt == k &&
      (bWits[k]!).v == dg _root_.Timmesfeld.PcFive.repIdx[k]!) = true := by
    decide +kernel
  intro k hk
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  rw [digitsOf_eq_dg]
  exact this

@[expose] def bBins : List (List ℕ) :=
  [[0, 14], [1, 10], [2, 9], [3, 25], [4, 19], [5, 29], [6, 20], [7, 23], [8, 11], [12, 15],
    [13], [16, 26], [17, 22], [18], [21], [24], [27, 28], [30]]

theorem bBins_cover : ∀ k < 31, ∃ b ∈ bBins, k ∈ b := by decide +kernel

section Batches


theorem bBins_ok : ∀ b ∈ bBins, ∀ p ∈ bEqsOf b, wordLin p.1 = wordLin p.2 := by
  intro b hb
  simp only [bBins, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact Certificates.certificate17489
  · exact Certificates.certificate17494
  · exact Certificates.certificate17495
  · exact Certificates.certificate17540
  · exact Certificates.certificate17541
  · exact Certificates.certificate17542
  · exact Certificates.certificate17543
  · exact Certificates.certificate17544
  · exact Certificates.certificate17598
  · exact Certificates.certificate17613
  · exact Certificates.certificate17614
  · exact Certificates.certificate17615
  · exact Certificates.certificate17616
  · exact Certificates.certificate17617
  · exact Certificates.certificate17618
  · exact Certificates.certificate17619
  · exact Certificates.certificate17625
  · exact Certificates.certificate17626

end Batches

section Targets


theorem m5bTargets_of_certs : M5BTargets := by
  intro k hk
  have hk31 : k < 31 := by
    have : _root_.Timmesfeld.PcFive.repIdx.size = 31 := rfl
    omega
  obtain ⟨b, hb, hkb⟩ := bBins_cover k hk31
  have h1 := bOK natCard_centralizer_tGmat CFSG.Monster.Tri.orderOf_tGmat _
    (bBatch (bBins_ok b hb) hkb)
  rw [(bWits_v k hk31).2, gw_rhsW_eq_prodAsc] at h1
  exact h1

end Targets

section Class


theorem m5bClass_of_certs : M5BClass := m5bClass_of_targets m5bTargets_of_certs

end Class

end CFSG.HardMathSupport.Dickson.I271.MonsterFiveB
