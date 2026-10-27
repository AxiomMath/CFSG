module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native


abbrev CM : Subgroup Pv := Subgroup.centralizer ({zP} : Set Pv)

@[expose] def mElt (k : ℕ) : Pv := treeElt hP mPar mLab k

theorem mIm_spec : ∀ k < 161280, mIm[k]! = pAct3 (mElt k) base3 :=
  tree_spec m_tree_check hP valid3_base3 fun l hl _ ht => arrStep_eq (prep_hArrs l hl) ht

theorem mSim_spec : ∀ k < 161280, mSim[k]! = pAct3 (sigmaPv (mElt k)) base3 := by
  intro k hk
  rw [tree_spec m_sim_check (fun l => sigmaPv (hP l)) valid3_base3
    (fun l hl _ ht => arrStep_eq (prep_vArrs l hl) ht) k hk, mElt, map_treeElt]

theorem mElt_mem : ∀ k < 161280, mElt k ∈ CM := treeElt_mem m_tree_check hP CM hP_mem

theorem mElt_inj {k k' : ℕ} (hk : k < 161280) (hk' : k' < 161280) (h : mElt k = mElt k') :
    k = k' :=
  distinct_spec m_distinct_check hk hk' (by rw [mIm_spec k hk, mIm_spec k' hk', h])

theorem card_CM : Nat.card CM = 161280 := by
  have e : CM = onM.subgroupOf Pv := by
    ext x
    rw [CFSG.Sporadic.ONOddCore.mem_centralizer_zP_iff, Subgroup.mem_subgroupOf]
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe onM_le).toEquiv, card_onM]

theorem exists_mElt {x : Pv} (hx : x ∈ CM) : ∃ k < 161280, mElt k = x := by
  let φ : Fin 161280 → CM := fun k => ⟨mElt k, mElt_mem k k.isLt⟩
  have hinj : Function.Injective φ := fun a b h =>
    Fin.ext (mElt_inj a.isLt b.isLt (congrArg Subtype.val h))
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_CM, Nat.card_fin])
  obtain ⟨k, hk⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨k, k.isLt, congrArg Subtype.val hk⟩

theorem map3_pathEval {k : ℕ} (hk : k < 161280) {t : Pt3} (ht : Valid3 t) :
    map3 (pathEval hArrs mPar mLab k) t = pAct3 (mElt k) t := by
  simp only [pAct3, map3, pathEval_spec m_tree_check hP prep_hArrs k hk _ ht.1,
    pathEval_spec m_tree_check hP prep_hArrs k hk _ ht.2.1,
    pathEval_spec m_tree_check hP prep_hArrs k hk _ ht.2.2, mElt]

theorem tTest_of_twist {k : ℕ} (hk : k < 161280) (h : mElt k * sigmaPv (mElt k) = 1) :
    tTest k = true := by
  unfold tTest
  rw [beq_iff_eq, mSim_spec k hk, map3_pathEval hk (valid3_pAct3 _ valid3_base3), ← pAct3_mul,
    h, pAct3_one]

theorem card_twist_le : Nat.card {x : Pv // x ∈ CM ∧ x * sigmaPv x = 1} ≤ 1344 := by
  have hg : ∀ x : {x : Pv // x ∈ CM ∧ x * sigmaPv x = 1}, ∃ k, k < 161280 ∧ mElt k = x.1 :=
    fun x => exists_mElt x.2.1
  choose g hg1 hg2 using hg
  have hmem : ∀ x, g x ∈ tList.toFinset := fun x =>
    List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (hg1 x),
      tTest_of_twist (hg1 x) (by rw [hg2 x]; exact x.2.2)⟩)
  have hinj : Function.Injective fun x => (⟨g x, hmem x⟩ : {k // k ∈ tList.toFinset}) := by
    intro a b h
    apply Subtype.ext
    rw [← hg2 a, ← hg2 b]
    exact congrArg mElt (congrArg Subtype.val h)
  calc Nat.card _ ≤ Nat.card {k // k ∈ tList.toFinset} := Nat.card_le_card_of_injective _ hinj
    _ = tList.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ tList.length := List.toFinset_card_le _
    _ ≤ 1344 := t_count_check

theorem cover_spec {k : ℕ} (hk : k < 161280) (h : mSim[k]! = mIm[k]!) :
    ∃ j < 60, fIm[j]! = mIm[k]! ∨ zfIm[j]! = mIm[k]! := by
  have hc := allBelowN_spec cover_check hk
  unfold cTest at hc
  rw [h] at hc
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, h1, Or.inl h2⟩
  · exact ⟨_, h1, Or.inr h2⟩

end CFSG.ComponentClassification.SolMax.ONOut
