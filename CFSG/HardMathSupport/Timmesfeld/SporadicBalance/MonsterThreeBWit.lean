module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBRoots
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWords
public import CFSG.YGroups.Y443.Native.Align
public import CFSG.Monster.Tri.GmatF1Type
public import CFSG.Monster.AxisCount.BabySetup

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
  CFSG.Monster.B.Pinned CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.Monster.Existence
open _root_.Timmesfeld.M3B (Vec E WT sigW eOf)

theorem agreeAll_append_iff {l₁ l₂ : List (List Native.Gen × List Native.Gen)} :
    agreeAll (l₁ ++ l₂) = true ↔ agreeAll l₁ = true ∧ agreeAll l₂ = true := by
  unfold agreeAll
  rw [List.all_append, Bool.and_eq_true]

theorem gw_flatMap {α : Type*} (f : α → List Native.Gen) :
    ∀ l : List α, gw (l.flatMap f) = (l.reverse.map fun a => gw (f a)).prod
  | [] => by simp [gw_nil]
  | a :: l => by
    rw [List.flatMap_cons, gw_append, gw_flatMap f l, List.reverse_cons, List.map_append,
      List.prod_append]
    simp

theorem isConj_of_mul_eq {G : Type*} [Group G] {T A c : G} (h : c * T = A * c) : IsConj T A := by
  refine isConj_iff.2 ⟨c, ?_⟩
  rw [h]; group

theorem conj_inv_of_sq {G : Type*} [Group G] {A H : G} (hA : A * A = 1)
    (hH : H * (A * (H * A)) = 1) : A * H * A⁻¹ = H⁻¹ := by
  have hA' : A⁻¹ = A := (eq_inv_of_mul_eq_one_left hA).symm
  rw [hA']
  have : H * (A * H * A) = 1 := by rw [← hH]; group
  exact eq_inv_of_mul_eq_one_right this

theorem gw_tStarW : gw tStarW = tGmat := Subtype.ext (by exact wordLin_tWord)

theorem natCard_centralizer_tStar :
    Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) = 2 * monsterBabyOrder := by
  rw [Nat.card_congr CFSG.Monster.Tri.centEquivCgen.toEquiv,
    CFSG.Monster.AxisCount.Baby.natCard_Cgen, CFSG.Monster.AxisCount.natCard_Jstar]
  norm_num [monsterBabyOrder]

@[expose] def IsTwoA (t : Gmat) : Prop :=
  orderOf t = 2 ∧ Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * monsterBabyOrder

theorem IsTwoA.of_isConj {t a : Gmat} (ht : IsTwoA t) (h : IsConj t a) : IsTwoA a := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, ?_⟩
  · have := MulEquiv.orderOf_eq (MulAut.conj c) t
    simp only [MulAut.conj_apply] at this
    rw [← hc, this, ht.1]
  · rw [← hc, natCard_centralizer_conj', ht.2]

section Blocks


theorem invEqs_sound (ht : IsTwoA (gw tstdW)) {a h r : List Native.Gen}
    (H : agreeAll (invEqs a h r) = true) : InvertedByTwoA (gw r) := by
  have hall := agreeAll_sound H
  have e1 := hall (a ++ a, []) (by simp [invEqs])
  have e2 := hall (a ++ r ++ a ++ r, []) (by simp [invEqs])
  have e3 := hall (tstdW ++ h, h ++ a) (by simp [invEqs])
  simp only [gw_append, gw_nil] at e1 e2 e3
  have hα := ht.of_isConj (isConj_of_mul_eq e3)
  exact ⟨gw a, hα.1, hα.2, conj_inv_of_sq e1 (by simpa [mul_assoc] using e2)⟩

theorem conjEqs_sound {c r : List Native.Gen} {z : ℕ} (H : agreeAll (conjEqs c r z) = true) :
    (gw c)⁻¹ * gw r * gw c = tbw ^ z := by
  have e := agreeAll_sound H (c ++ r, powL z tbW ++ c) (by simp [conjEqs])
  simp only [gw_append, tb_gw_powL] at e
  have hw : gw tbW = tbw := rfl
  rw [hw] at e
  rw [mul_assoc, e]
  group

@[expose] def KleinPair (A B : Gmat) : Prop :=
  orderOf A = 2 ∧ orderOf B = 2 ∧ A * B = B * A ∧ A ≠ B ∧
    Nat.card ↥(Subgroup.centralizer ({A} : Set Gmat)) = 2 * monsterBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({B} : Set Gmat)) = 2 * monsterBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({A * B} : Set Gmat)) = 2 * monsterBabyOrder

theorem kleinData_of_pair {A B x : Gmat} (h : KleinPair A B) (hA : A * x = x * A)
    (hB : B * x = x * B) : KleinData x := by
  obtain ⟨ha, hb, hab, hne, hca, hcb, hcab⟩ := h
  exact ⟨A, B, Subgroup.mem_centralizer_singleton_iff.2 hA,
    Subgroup.mem_centralizer_singleton_iff.2 hB, ha, hb, hab, hne, hca, hcb, hcab⟩

theorem kleinEqs_sound (ht : IsTwoA (gw tstdW)) {a b ha hb hab : List Native.Gen}
    {rs : List (List Native.Gen)} (H : agreeAll (kleinEqs a b ha hb hab rs) = true)
    (hm : EdgeNoncomm.moveCheck (a ++ b) (aV ()) = true) :
    KleinPair (gw a) (gw b) ∧ ∀ r ∈ rs, gw a * gw r = gw r * gw a ∧ gw b * gw r = gw r * gw b := by
  have hall := agreeAll_sound H
  have e1 := hall (a ++ a, []) (by simp [kleinEqs])
  have e3 := hall (a ++ b, b ++ a) (by simp [kleinEqs])
  have e4 := hall (tstdW ++ ha, ha ++ a) (by simp [kleinEqs])
  have e5 := hall (tstdW ++ hb, hb ++ b) (by simp [kleinEqs])
  have e6 := hall (tstdW ++ hab, hab ++ (b ++ a)) (by simp [kleinEqs])
  simp only [gw_append, gw_nil] at e1 e3 e4 e5 e6
  have hA := ht.of_isConj (isConj_of_mul_eq e4)
  have hB := ht.of_isConj (isConj_of_mul_eq e5)
  have hAB := ht.of_isConj (isConj_of_mul_eq e6)
  have hne : gw b * gw a ≠ 1 := by
    have := gw_ne_one_of_moveCheck hm
    rwa [gw_append] at this
  refine ⟨⟨hA.1, hB.1, e3.symm, fun h => hne (by rw [← h]; exact e1), hA.2, hB.2, hAB.2⟩, ?_⟩
  intro r hr
  have f1 := hall (a ++ r, r ++ a) (by
    simp only [kleinEqs, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, by simp⟩)
  have f2 := hall (b ++ r, r ++ b) (by
    simp only [kleinEqs, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, by simp⟩)
  simp only [gw_append] at f1 f2
  exact ⟨f1.symm, f2.symm⟩

end Blocks

section Words


@[expose] def vecL (v : List ℕ) : Fin 12 → ZMod 3 := fun i => ((v.getD i.val 0 : ℕ) : ZMod 3)

theorem toE_eOf (v : List ℕ) : toE (eOf v 0) = (vecL v, 0) := by
  unfold toE eOf
  rw [vfun_vofFn]
  refine Prod.ext (funext fun i => ?_) rfl
  show toZ (Fin.ofNat 3 (v.getD i.val 0)) = ((v.getD i.val 0 : ℕ) : ZMod 3)
  apply ZMod.val_injective
  rw [toZ_val, Fin.val_ofNat, ZMod.val_natCast]

theorem repG_eq (k : ℕ) (v : List ℕ) : repG k v = tG k * tbSys.nf (vecL v, 0) := by
  rw [repG, toE_eOf]

theorem gw_qW (v : List ℕ) : gw (qW v) = secN3 12 tbq (vecL v) := by
  rw [secN3_eq_prod, qW, gw_flatMap, List.reverse_reverse, ← List.map_coe_finRange_eq_range,
    List.map_map, List.ofFn_eq_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [tb_gw_powL, vecL, ZMod.val_natCast, pow_mod_three (tbq_pow_three i)]
  rfl

theorem gw_nfW (v : List ℕ) (z : ℕ) : gw (nfW v z) = tbSys.nf (vecL v, 0) * tbw ^ z := by
  rw [nfW, gw_append, gw_qW, tb_gw_powL, Sys.nf]
  simp only [ZMod.val_zero, pow_zero, mul_one]
  rfl

theorem gw_letterW (h1 : gw b1iW = tbb₁⁻¹) (h2 : gw b2iW = tbb₂⁻¹) :
    ∀ i, gw (letterW i) = letterG i
  | 0 => by
    have h : letterW 0 = tbB1 := by unfold letterW; rw [ite_eq_left rfl]
    rw [h, letterG_zero]; rfl
  | 1 => by
    have h : letterW 1 = tbB2 := by
      unfold letterW; rw [ite_eq_right (by decide), ite_eq_left rfl]
    rw [h, letterG_one]; rfl
  | 2 => by
    have h : letterW 2 = b1iW := by
      unfold letterW; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    rw [h, letterG_two]; exact h1
  | 3 => by
    have h : letterW 3 = b2iW := by
      unfold letterW
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left rfl]
    rw [h, letterG_three]; exact h2
  | i + 4 => by
    have h0 : i + 4 ≠ 0 := by omega
    have h1' : i + 4 ≠ 1 := by omega
    have h2' : i + 4 ≠ 2 := by omega
    have h3' : i + 4 ≠ 3 := by omega
    have hW : letterW (i + 4) = if i + 4 - 4 < 12 then tbQ (i + 4 - 4) else [] := by
      unfold letterW
      rw [ite_eq_right h0, ite_eq_right h1', ite_eq_right h2', ite_eq_right h3']
    have hG : letterG (i + 4) =
        if h : i + 4 - 4 < 12 then tbq ⟨i + 4 - 4, h⟩ else 1 := by
      unfold letterG
      rw [ite_eq_right h0, ite_eq_right h1', ite_eq_right h2', ite_eq_right h3']
    rw [hW, hG]
    split_ifs
    · rfl
    · exact gw_nil

theorem gw_wtW (h1 : gw b1iW = tbb₁⁻¹) (h2 : gw b2iW = tbb₂⁻¹) :
    ∀ t : WT, gw (wtW t) = evalG letterG t
  | .gen i => by rw [wtW, evalG]; exact gw_letterW h1 h2 i
  | .mul a b => by rw [wtW, gw_append, gw_wtW h1 h2 a, gw_wtW h1 h2 b, evalG]
  | .pow t k => by rw [wtW, tb_gw_powL, gw_wtW h1 h2 t, evalG]

end Words

section Ident


theorem tkW_one : tkW 1 = tkW1 := by
  unfold tkW; rw [ite_eq_left rfl]

theorem tkW_two : tkW 2 = tkW2 := by
  unfold tkW; rw [ite_eq_right (by decide), ite_eq_left rfl]

theorem tkW_three : tkW 3 = tkW3 := by
  unfold tkW; rw [ite_eq_right (by decide), ite_eq_right (by decide)]

theorem tG_eq {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) : tG k = evalG letterG (uWT k) ^ 8 := by
  have hsig : sigW[k - 1]! = .pow (uWT k) 8 := by
    interval_cases k <;> rfl
  unfold tG
  rw [ite_eq_right (by omega), hsig, evalG]

theorem base_facts (hE : agreeAll m3bBaseEqs = true) :
    gw b1iW = tbb₁⁻¹ ∧ gw b2iW = tbb₂⁻¹ ∧ (∀ k, 1 ≤ k → k ≤ 3 → gw (tkW k) = tG k) ∧
      (∀ k < 4, tG k ^ 3 = 1) ∧ IsConj tGmat (gw tstdW) := by
  simp only [m3bBaseEqs, agreeAll, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hE
  obtain ⟨l1, l2, u1, u2, u3, t1, t2, t3, c1, c2, c3, s⟩ := hE
  have L1 := agree_sound l1
  have L2 := agree_sound l2
  simp only [gw_append, gw_nil] at L1 L2
  have hb1 : gw b1iW = tbb₁⁻¹ := eq_inv_of_mul_eq_one_left L1
  have hb2 : gw b2iW = tbb₂⁻¹ := eq_inv_of_mul_eq_one_left L2
  have hw := gw_wtW hb1 hb2
  have e1 : gw tkW1 = tG 1 := by
    rw [agree_sound t1, tb_gw_powL, agree_sound u1, hw, tG_eq le_rfl (by norm_num)]
  have e2 : gw tkW2 = tG 2 := by
    rw [agree_sound t2, tb_gw_powL, agree_sound u2, hw, tG_eq (by norm_num) (by norm_num)]
  have e3 : gw tkW3 = tG 3 := by
    rw [agree_sound t3, tb_gw_powL, agree_sound u3, hw, tG_eq (by norm_num) le_rfl]
  refine ⟨hb1, hb2, fun k hk1 hk3 => ?_, fun k hk => ?_, ?_⟩
  · interval_cases k
    · rw [tkW_one, e1]
    · rw [tkW_two, e2]
    · rw [tkW_three, e3]
  · interval_cases k
    · unfold tG; rw [ite_eq_left rfl, one_pow]
    · rw [← e1, ← tb_gw_powL, agree_sound c1, gw_nil]
    · rw [← e2, ← tb_gw_powL, agree_sound c2, gw_nil]
    · rw [← e3, ← tb_gw_powL, agree_sound c3, gw_nil]
  · have e := agree_sound s
    simp only [gw_append, gw_tStarW] at e
    exact (isConj_of_mul_eq e.symm).symm

theorem gw_repW {k : ℕ} (htk : gw (tkW k) = tG k) (v : List ℕ) (z : ℕ) :
    gw (repW k v z) = tG k * tbSys.nf (vecL v, 0) * tbw ^ z := by
  rw [repW, gw_append, htk, gw_nfW, mul_assoc]

theorem vecL_eq {v v' : List ℕ} (h : ∀ i < 12, v.getD i 0 = v'.getD i 0) : vecL v = vecL v' := by
  funext i
  unfold vecL
  rw [h i.val i.isLt]

theorem nf_vecL_single {v : List ℕ} (i : Fin 12) (h : vecL v = Pi.single i 1) :
    tbSys.nf (vecL v, 0) = tbq i := by
  rw [h, tbSys_nf_single]

theorem nf_vecL_zero {v : List ℕ} (h : vecL v = 0) : tbSys.nf (vecL v, 0) = 1 := by
  rw [h]
  exact Sys.nf_eone tbSys

theorem goodK_tbw_sq (hw : GoodK tbw) : GoodK (tbw ^ 2) := by
  have h2 : tbb₁⁻¹ * tbw * tbb₁ = tbw ^ 2 := isAct_b₁.2
  rw [← h2]
  have := goodK_conj hw tbb₁⁻¹
  rwa [inv_inv] at this

theorem goodK_of_conj_pow {c r : Gmat} {z : ℕ} (h : c⁻¹ * r * c = tbw ^ z) (hw : GoodK (tbw ^ z)) :
    GoodK r := by
  rw [← h] at hw
  have := goodK_conj hw c
  simpa [mul_assoc] using this

theorem rootGood_of_eqs (ht : IsTwoA tGmat) (hE : agreeAll m3bEqs = true)
    (hM : m3bMoves.all (fun w => EdgeNoncomm.moveCheck w (aV ())) = true) :
    ∀ c ∈ rootClaims, RootGood c := by
  unfold m3bEqs at hE
  rw [agreeAll_append_iff] at hE
  obtain ⟨hB, hC⟩ := hE
  obtain ⟨hb1, hb2, htk, -, hstd⟩ := base_facts hB
  have hT : IsTwoA (gw tstdW) := ht.of_isConj hstd
  simp only [m3bClassEqs, agreeAll_append_iff, and_assoc] at hC
  obtain ⟨kw, iq1, cq0, c1, i1a, i1b, c1d, i20, i21, i22, k3, c3h, i3g⟩ := hC
  simp only [m3bMoves, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hM
  obtain ⟨mw, m3⟩ := hM
  obtain ⟨pw, cw⟩ := kleinEqs_sound hT kw mw
  have hw : GoodK tbw := Or.inr (kleinData_of_pair pw (cw tbW (List.mem_singleton_self _)).1
    (cw tbW (List.mem_singleton_self _)).2)
  have hw2 := goodK_tbw_sq hw
  have hw1 : GoodK (tbw ^ 1) := by rw [pow_one]; exact hw
  have ht1 := htk 1 le_rfl (by norm_num)
  have ht2 := htk 2 (by norm_num) (by norm_num)
  have ht3 := htk 3 (by norm_num) le_rfl
  intro c hc
  simp only [rootClaims, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    exact hw
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    rw [repG_eq, show tG 0 = 1 from ite_eq_left rfl, one_mul,
      nf_vecL_single 1 (by funext i; fin_cases i <;> simp [vecL])]
    exact Or.inl (invEqs_sound hT iq1)
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    rw [repG_eq, show tG 0 = 1 from ite_eq_left rfl, one_mul,
      nf_vecL_single 0 (by funext i; fin_cases i <;> simp [vecL])]
    exact goodK_of_conj_pow (conjEqs_sound cq0) hw2
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e he
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    rw [repG_eq, hv]
    interval_cases e
    · have h := conjEqs_sound c1
      rw [gw_repW ht1] at h
      exact goodK_of_conj_pow h hw1
    · have h := invEqs_sound hT i1a
      rw [gw_repW ht1] at h
      exact Or.inl h
    · have h := invEqs_sound hT i1b
      rw [gw_repW ht1] at h
      exact Or.inl h
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have hv : vecL [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [0, 0, 0, 1] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    have h := conjEqs_sound c1d
    rw [gw_repW ht1, pow_zero, mul_one] at h
    rw [repG_eq, hv]
    exact goodK_of_conj_pow h hw1
  ·
    unfold RootGood
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e he
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    rw [repG_eq, hv]
    interval_cases e
    · have h := invEqs_sound hT i20
      rw [gw_repW ht2] at h
      exact Or.inl h
    · have h := invEqs_sound hT i21
      rw [gw_repW ht2] at h
      exact Or.inl h
    · have h := invEqs_sound hT i22
      rw [gw_repW ht2] at h
      exact Or.inl h
  ·
    unfold RootGood
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e _
    obtain ⟨p3, c3⟩ := kleinEqs_sound hT k3 m3
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 0 := by
      funext i; fin_cases i <;> simp [vecL]
    rw [repG_eq, nf_vecL_zero hv, mul_one]
    have ct := c3 (tkW 3) List.mem_cons_self
    have cw := c3 tbW (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rw [ht3] at ct
    have hw' : gw tbW = tbw := rfl
    rw [hw'] at cw
    refine Or.inr (kleinData_of_pair p3 ?_ ?_)
    · rw [← mul_assoc, ct.1, mul_assoc, ((Commute.pow_right (show Commute _ tbw from cw.1) e)).eq,
        mul_assoc]
    · rw [← mul_assoc, ct.2, mul_assoc, ((Commute.pow_right (show Commute _ tbw from cw.2) e)).eq,
        mul_assoc]
  ·
    unfold RootGood
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGood
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have h := conjEqs_sound c3h
    rw [gw_repW ht3, pow_zero, mul_one] at h
    rw [repG_eq]
    exact goodK_of_conj_pow h hw1
  ·
    unfold RootGood
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGood
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have hv : vecL [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [0, 1, 0, 1] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    have h := invEqs_sound hT i3g
    rw [gw_repW ht3, pow_zero, mul_one] at h
    rw [repG_eq, hv]
    exact Or.inl h

end Ident

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
