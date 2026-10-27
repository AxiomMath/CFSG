module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGood
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
public import CFSG.YGroups.Y443.Tri.Finiteness
public import CFSG.Monster.Tri.GmatF1Type

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat

open CFSG.Open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.AGLEmbedding.Norton.MON5_7

theorem natCard_centralizer_tGmat :
    Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) = 2 * monsterBabyOrder := by
  rw [Nat.card_congr CFSG.Monster.Tri.centEquivCgen.toEquiv,
    CFSG.Monster.AxisCount.Baby.natCard_Cgen, CFSG.Monster.AxisCount.natCard_Jstar]
  norm_num [monsterBabyOrder]

theorem good_of_twoARep (ht : Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) =
    2 * monsterBabyOrder) (ho : orderOf tGmat = 2) {h : Gmat} (H : TwoARep h) : Good h := by
  have hord : ∀ a : Gmat, IsConj tGmat a → orderOf a = 2 := fun a ha => by
    obtain ⟨c, hc⟩ := isConj_iff.1 ha
    have h := MulEquiv.orderOf_eq (MulAut.conj c) tGmat
    simp only [MulAut.conj_apply] at h
    rw [← hc, h, ho]
  have hcard : ∀ a : Gmat, IsConj tGmat a →
      Nat.card ↥(Subgroup.centralizer ({a} : Set Gmat)) = 2 * monsterBabyOrder := fun a ha => by
    obtain ⟨c, hc⟩ := isConj_iff.1 ha
    rw [← hc, natCard_centralizer_conj', ht]
  rcases H with ⟨α, hα, hinv⟩ | ⟨a, b, ha, hb, hah, hbh, hab, hne⟩
  · exact Or.inl ⟨α, hord α hα, hcard α hα, hinv⟩
  · exact Or.inr ⟨a, b, Subgroup.mem_centralizer_singleton_iff.2 hah,
      Subgroup.mem_centralizer_singleton_iff.2 hbh, hord a ha, hord b hb, hab, hne,
      hcard a ha, hcard b hb⟩

@[expose] def dg (i : ℕ) : Array ℕ :=
  (List.foldl (fun (b : Array ℕ × ℕ) a => (b.fst.setIfInBounds (8 - a) (b.snd % 5), b.snd / 5))
    (Array.replicate 9 0, i) (List.range' 0 9)).fst

theorem digitsOf_eq_dg (i : ℕ) : _root_.Timmesfeld.PcReg.digitsOf 5 9 i = dg i := by
  unfold _root_.Timmesfeld.PcReg.digitsOf dg
  simp [Id.run]
  generalize (List.foldl (fun (b : Array ℕ × ℕ) a =>
    (b.fst.setIfInBounds (8 - a) (b.snd % 5), b.snd / 5)) (Array.replicate 9 0, i)
    (List.range' 0 9)).fst = A
  rfl

set_option maxRecDepth 100000 in
theorem fiveReps_v : ∀ k < 31,
    (fiveReps[k]!).v =
      _root_.Timmesfeld.PcReg.digitsOf 5 9 _root_.Timmesfeld.PcFive.repIdx[k]! := by
  have h : (List.range 31).all (fun k =>
      (fiveReps[k]!).v == dg _root_.Timmesfeld.PcFive.repIdx[k]!) = true := by
    decide +kernel
  intro k hk
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [digitsOf_eq_dg]
  simpa using this

set_option maxRecDepth 100000 in
theorem fivePw_eq : fivePw = _root_.Timmesfeld.PcFive.pw := by decide +kernel

set_option maxRecDepth 100000 in
theorem fiveCw_eq : fiveCw = _root_.Timmesfeld.PcFive.cw := by decide +kernel

set_option maxRecDepth 100000 in
theorem fiveNImg_eq : ∀ j < _root_.Timmesfeld.PcFive.auts.size, ∀ i < 9,
    _root_.Timmesfeld.PcReg.digitsOf 5 9 (_root_.Timmesfeld.PcFive.auts[j]!)[i]! =
      (fiveNImg[j]!)[i]! := by
  have h : ∀ j < _root_.Timmesfeld.PcFive.auts.size, ∀ i < 9,
      dg (_root_.Timmesfeld.PcFive.auts[j]!)[i]! = (fiveNImg[j]!)[i]! := by
    decide +kernel
  intro j hj i hi
  rw [digitsOf_eq_dg]
  exact h j hj i hi

theorem twoATwoCommuting_five_Gmat :
    TwoATwoCommuting 5 Gmat := by
  have hcard0 : Nat.card Gmat = monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have : Finite Gmat := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num [monsterOrder])
  have hcard : Nat.card Gmat = 5 ^ 9 * (monsterOrder / 5 ^ 9) := by
    rw [hcard0]; norm_num [monsterOrder]
  have hm : ¬ 5 ∣ monsterOrder / 5 ^ 9 := by norm_num [monsterOrder]
  have ht := natCard_centralizer_tGmat
  refine MonsterFiveCensus.twoATwoCommuting_five_of_rel hcard hm
    (fun i : Fin 9 => gw fiveGens[i.val]!) ?_ ?_ fiveNImg fiveNImg_eq
    (fun j => gw fiveNW[j]!) ?_ ?_
  · rw [← fivePw_eq, ← fiveCw_eq]
    exact fiveRels_holds
  · exact fiveGen_eight_ne_one
  · intro j hj i hi
    exact fiveNorm_holds j (by have : _root_.Timmesfeld.PcFive.auts.size = 3 := rfl; omega) i hi
  · intro k hk
    have hk31 : k < 31 := by
      have : _root_.Timmesfeld.PcFive.repIdx.size = 31 := rfl
      omega
    have h1 := fiveReps_twoARep k hk31
    rw [MonsterFiveCensus.lift_wordF_eq] at h1
    rw [← fiveReps_v k hk31]
    exact good_of_twoARep ht CFSG.Monster.Tri.orderOf_tGmat h1

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
