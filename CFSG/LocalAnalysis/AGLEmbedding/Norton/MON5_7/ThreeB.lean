module

public import Certificates.Certificate125360
public import Certificates.Certificate125361
public import Certificates.Certificate125362
public import Certificates.Certificate125363
public import Certificates.Certificate125364
public import Certificates.Certificate125365
public import Certificates.Certificate125366
public import Certificates.Certificate125367
public import Certificates.Certificate125368
public import Certificates.Certificate125369
public import Certificates.Certificate125370
public import Certificates.Certificate125371
public import Certificates.Certificate125372
public import Certificates.Certificate125373
public import Certificates.Certificate125374

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def tbMat (R : List (List ℕ)) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => ((R.getD i []).getD j 0 : ZMod 3)

@[expose] def tbM : Matrix (Fin 12) (Fin 12) (ZMod 3) := tbMat tbMRows

@[expose] def tbXMat : Matrix (Fin 12) (Fin 12) (ZMod 3) := tbMat tbXRows

@[expose] def tbYMat : Matrix (Fin 12) (Fin 12) (ZMod 3) := tbMat tbYRows

theorem tbMat_val (R : List (List ℕ)) (hR : ∀ i j : Fin 12, tbEntry R i j < 3) (i j : Fin 12) :
    (tbMat R i j).val = tbEntry R i j := by
  have h := hR i j
  show (((R.getD i []).getD j 0 : ℕ) : ZMod 3).val = _
  exact ZMod.val_natCast_of_lt h

theorem tbOrder_check :
    agreeAll tbOrderPairs = true ∧ agreeAll tbWOrderPairs = true ∧
      (EdgeNoncomm.moveCheck tbW (aV ()) || EdgeNoncomm.moveCheck tbW (bV ()) ||
        EdgeNoncomm.moveCheck tbW (wV ())) = true := Certificates.certificate125360

theorem tbCentral_check : agreeAll tbCentralPairs = true := Certificates.certificate125361

theorem tbChain_check0 : agreeAll (tbChainPairs [0]) = true :=
  Certificates.certificate125362

theorem tbChain_check1 : agreeAll (tbChainPairs [1, 10]) = true :=
  Certificates.certificate125363

theorem tbChain_check2 : agreeAll (tbChainPairs [2, 9]) = true :=
  Certificates.certificate125364

theorem tbChain_check3 : agreeAll (tbChainPairs [3, 8]) = true :=
  Certificates.certificate125365

theorem tbChain_check4 : agreeAll (tbChainPairs [4, 7]) = true :=
  Certificates.certificate125366

theorem tbChain_check5 : agreeAll (tbChainPairs [5, 6]) = true :=
  Certificates.certificate125367

theorem tbChain_check : ∀ g ∈ ([[0], [1, 10], [2, 9], [3, 8], [4, 7], [5, 6]] : List (List ℕ)),
    agreeAll (tbChainPairs g) = true := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tbChain_check0
  · exact tbChain_check1
  · exact tbChain_check2
  · exact tbChain_check3
  · exact tbChain_check4
  · exact tbChain_check5

theorem tbAct1_check0 : agreeAll (tbTreePairs tbB1 tbXTree tbXTreeC [0, 1, 2]) = true :=
  Certificates.certificate125368

theorem tbAct1_check1 : agreeAll (tbTreePairs tbB1 tbXTree tbXTreeC [3, 4, 5]) = true :=
  Certificates.certificate125369

theorem tbAct1_check2 : agreeAll (tbTreePairs tbB1 tbXTree tbXTreeC [6, 7, 8]) = true :=
  Certificates.certificate125370

theorem tbAct1_check3 : agreeAll (tbTreePairs tbB1 tbXTree tbXTreeC [9, 10, 11]) = true :=
  Certificates.certificate125371

theorem tbAct1_check : ∀ g ∈ ([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]] : List (List ℕ)),
    agreeAll (tbTreePairs tbB1 tbXTree tbXTreeC g) = true := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact tbAct1_check0
  · exact tbAct1_check1
  · exact tbAct1_check2
  · exact tbAct1_check3

theorem tbAct2_check0 : agreeAll (tbTreePairs tbB2 tbYTree tbYTreeC [0, 1, 2, 3]) = true :=
  Certificates.certificate125372

theorem tbAct2_check1 : agreeAll (tbTreePairs tbB2 tbYTree tbYTreeC [4, 5, 6, 7]) = true :=
  Certificates.certificate125373

theorem tbAct2_check2 : agreeAll (tbTreePairs tbB2 tbYTree tbYTreeC [8, 9, 10, 11]) = true :=
  Certificates.certificate125374

theorem tbAct2_check : ∀ g ∈ ([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]] : List (List ℕ)),
    agreeAll (tbTreePairs tbB2 tbYTree tbYTreeC g) = true := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact tbAct2_check0
  · exact tbAct2_check1
  · exact tbAct2_check2

theorem tb_gw_powL (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (wordLin_powL k w)

@[expose] noncomputable def tbq (i : Fin 12) : Gmat := gw (tbQ i)

@[expose] noncomputable def tbw : Gmat := gw tbW

@[expose] noncomputable def tbb₁ : Gmat := gw tbB1

@[expose] noncomputable def tbb₂ : Gmat := gw tbB2

@[expose] def tbc₁ (i : Fin 12) : ℕ := tbC1.getD i 0

@[expose] def tbc₂ (i : Fin 12) : ℕ := tbC2.getD i 0

theorem tbq_pow_three (i : Fin 12) : tbq i ^ 3 = 1 := by
  have h := agreeAll_sound tbOrder_check.1 (powL 3 (tbQ i), [])
    (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)
  simpa [tb_gw_powL, gw_nil, tbq] using h

theorem tbw_pow_three : tbw ^ 3 = 1 := by
  have h := agreeAll_sound tbOrder_check.2.1 (powL 3 tbW, []) (by simp [tbWOrderPairs])
  simpa [tb_gw_powL, gw_nil, tbw] using h

theorem tbw_ne_one : tbw ≠ 1 := by
  have h := tbOrder_check.2.2
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact gw_ne_one_of_moveCheck h
  · exact gw_ne_one_of_moveCheck h
  · exact gw_ne_one_of_moveCheck h

theorem tbq_mul_tbw (i : Fin 12) : tbq i * tbw = tbw * tbq i := by
  have h := agreeAll_sound tbCentral_check (tbW ++ tbQ i, tbQ i ++ tbW)
    (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)
  simpa [gw_append, tbq, tbw] using h

theorem tbq_conj_tbw (i : Fin 12) : tbq i * tbw * (tbq i)⁻¹ = tbw := by
  rw [mul_inv_eq_iff_eq_mul]
  exact tbq_mul_tbw i

theorem tbChain_mem {i j : ℕ} (hij : i < j) (hj : j < 12) {g : List ℕ} (hg : i ∈ g) :
    (tbQ j ++ tbQ i, tbQ i ++ powL (tbEntry tbMRows i j) tbW ++ tbQ j) ∈ tbChainPairs g := by
  unfold tbChainPairs
  refine List.mem_flatMap.2 ⟨i, hg, ?_⟩
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
  simp [hij]

theorem tbChain_group {i : ℕ} (hi : i < 11) :
    ∃ g ∈ ([[0], [1, 10], [2, 9], [3, 8], [4, 7], [5, 6]] : List (List ℕ)), i ∈ g := by
  interval_cases i <;> simp

theorem tbq_chain_aux {i j : Fin 12} (hij : i < j) :
    tbq i * tbq j = tbq j * tbw ^ tbEntry tbMRows i j * tbq i := by
  have hij' : (i : ℕ) < j := Fin.lt_def.1 hij
  obtain ⟨g, hg, hig⟩ := tbChain_group (i := i) (by have := j.2; omega)
  have h := agreeAll_sound (tbChain_check g hg) _ (tbChain_mem hij' j.2 hig)
  simpa [gw_append, tb_gw_powL, tbq, tbw, mul_assoc] using h

theorem tbq_chain (i j : Fin 12) (hij : i < j) :
    tbq i * tbq j * (tbq i)⁻¹ = tbq j * tbw ^ (tbM i j).val := by
  have e : (tbM i j).val = tbEntry tbMRows i j := tbMat_val tbMRows (by decide +kernel) i j
  rw [mul_inv_eq_iff_eq_mul, e]
  exact tbq_chain_aux hij

theorem tbRowWord_gw (R : List (List ℕ)) (i : ℕ) :
    gw (tbRowWord R i) = (List.ofFn fun j : Fin 12 => tbq j ^ tbEntry R i j).prod := by
  have key : ∀ ws : List (List Native.Gen), gw ws.reverse.flatten = (ws.map gw).prod := by
    intro ws
    induction ws with
    | nil => simp [gw_nil]
    | cons a t ih => simp [List.reverse_cons, List.flatten_append, gw_append, ih]
  unfold tbRowWord
  rw [List.map_reverse, key]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, tb_gw_powL, tbq]

theorem tbAct_aux (b : List Native.Gen) (R : List (List ℕ)) (c : List ℕ) (gs : List ℕ)
    (hall : agreeAll (tbActPairs b R c gs) = true) {i : ℕ} (hi : i ∈ gs) :
    gw (tbQ i) * gw b =
      gw b * (List.ofFn fun j : Fin 12 => tbq j ^ tbEntry R i j).prod * tbw ^ c.getD i 0 := by
  have h := agreeAll_sound hall (b ++ tbQ i, powL (c.getD i 0) tbW ++ tbRowWord R i ++ b)
    (List.mem_map.2 ⟨i, hi, rfl⟩)
  simp only [gw_append, tb_gw_powL, tbRowWord_gw] at h
  rw [show tbw = gw tbW from rfl]
  simpa [mul_assoc] using h

noncomputable def tbqN (i : ℕ) : Gmat := gw (tbQ i)

theorem tbqN_comm {i : ℕ} (hi : i < 12) : Commute (tbqN i) tbw := tbq_mul_tbw ⟨i, hi⟩

theorem tbqN_swap {i j : ℕ} (hij : i < j) (hj : j < 12) :
    tbqN j * tbqN i = tbqN i * tbqN j * tbw ^ (2 * tbEntry tbMRows i j) := by
  have h := tbq_chain_aux (i := ⟨i, by omega⟩) (j := ⟨j, hj⟩) (Fin.mk_lt_mk.2 hij)
  change tbqN i * tbqN j = tbqN j * tbw ^ tbEntry tbMRows i j * tbqN i at h
  generalize tbEntry tbMRows i j = M at h ⊢
  have hc : tbw ^ M * tbqN i = tbqN i * tbw ^ M := ((tbqN_comm (by omega)).pow_right M).symm.eq
  have e3 : tbw ^ (M + 2 * M) = 1 := by
    rw [show M + 2 * M = 3 * M by ring, pow_mul, tbw_pow_three, one_pow]
  calc tbqN j * tbqN i = tbqN j * tbqN i * tbw ^ (M + 2 * M) := by rw [e3, mul_one]
    _ = tbqN j * (tbw ^ M * tbqN i) * tbw ^ (2 * M) := by
      rw [hc, pow_add]
      simp only [mul_assoc]
    _ = tbqN i * tbqN j * tbw ^ (2 * M) := by rw [← mul_assoc (tbqN j), ← h]

theorem tbqN_swap_pow {i j : ℕ} (hij : i < j) (hj : j < 12) (a : ℕ) :
    tbqN j * tbqN i ^ a = tbqN i ^ a * tbqN j * tbw ^ (2 * tbEntry tbMRows i j * a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hc : tbw ^ (2 * tbEntry tbMRows i j * a) * tbqN i =
        tbqN i * tbw ^ (2 * tbEntry tbMRows i j * a) :=
      ((tbqN_comm (by omega)).pow_right _).symm.eq
    calc tbqN j * tbqN i ^ (a + 1) = tbqN j * tbqN i ^ a * tbqN i := by rw [pow_succ, mul_assoc]
      _ = tbqN i ^ a * tbqN j * (tbw ^ (2 * tbEntry tbMRows i j * a) * tbqN i) := by
        rw [ih]
        simp only [mul_assoc]
      _ = tbqN i ^ a * (tbqN j * tbqN i) * tbw ^ (2 * tbEntry tbMRows i j * a) := by
        rw [hc]
        simp only [mul_assoc]
      _ = tbqN i ^ (a + 1) * tbqN j * tbw ^ (2 * tbEntry tbMRows i j * (a + 1)) := by
        have e : 2 * tbEntry tbMRows i j * (a + 1) =
            2 * tbEntry tbMRows i j + 2 * tbEntry tbMRows i j * a := by ring
        rw [tbqN_swap hij hj, pow_succ, e, pow_add]
        simp only [mul_assoc]

noncomputable def tbQProd (e : ℕ → ℕ) (m : ℕ) : Gmat :=
  ((List.range m).map fun i => tbqN i ^ e i).prod

theorem tbQProd_succ (e : ℕ → ℕ) (m : ℕ) : tbQProd e (m + 1) = tbQProd e m * tbqN m ^ e m := by
  simp [tbQProd, List.range_succ, List.prod_append]

theorem tbQProd_congr {e e' : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, e i = e' i) :
    tbQProd e m = tbQProd e' m := by
  unfold tbQProd
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.1 hi)]

theorem tbQProd_comm (e : ℕ → ℕ) : ∀ {m : ℕ}, m ≤ 12 → Commute (tbQProd e m) tbw
  | 0, _ => by simp [tbQProd]
  | m + 1, hm => by
    rw [tbQProd_succ]
    exact (tbQProd_comm e (m := m) (by omega)).mul_left ((tbqN_comm (by omega)).pow_left _)

@[expose] def tbNFs (e : ℕ → ℕ) (j m : ℕ) : ℕ :=
  ((List.range m).map fun i => 2 * tbEntry tbMRows i j * e i).sum

@[expose] def tbNFz (e : ℕ → ℕ) (j : ℕ) : ℕ := tbNFs e j j

theorem tbNFs_succ (e : ℕ → ℕ) (j m : ℕ) :
    tbNFs e j (m + 1) = tbNFs e j m + 2 * tbEntry tbMRows m j * e m := by
  simp [tbNFs, List.range_succ]

theorem tbqN_mul_tbQProd {j : ℕ} (hj : j < 12) (e : ℕ → ℕ) : ∀ {m : ℕ}, m ≤ j →
    tbqN j * tbQProd e m = tbQProd e m * tbqN j * tbw ^ tbNFs e j m
  | 0, _ => by simp [tbQProd, tbNFs]
  | m + 1, hm => by
    have hc : tbw ^ tbNFs e j m * tbqN m ^ e m = tbqN m ^ e m * tbw ^ tbNFs e j m :=
      (((tbqN_comm (by omega)).pow_right _).pow_left _).symm.eq
    rw [tbQProd_succ, tbNFs_succ]
    calc tbqN j * (tbQProd e m * tbqN m ^ e m) = tbqN j * tbQProd e m * tbqN m ^ e m :=
          (mul_assoc _ _ _).symm
      _ = tbQProd e m * tbqN j * tbw ^ tbNFs e j m * tbqN m ^ e m := by
        rw [tbqN_mul_tbQProd hj e (m := m) (by omega)]
      _ = tbQProd e m * (tbqN j * tbqN m ^ e m) * tbw ^ tbNFs e j m := by
        simp only [mul_assoc, hc]
      _ = tbQProd e m * (tbqN m ^ e m * tbqN j * tbw ^ (2 * tbEntry tbMRows m j * e m)) *
            tbw ^ tbNFs e j m := by
        rw [tbqN_swap_pow (i := m) (by omega) hj]
      _ = tbQProd e m * tbqN m ^ e m * tbqN j *
            tbw ^ (tbNFs e j m + 2 * tbEntry tbMRows m j * e m) := by
        rw [pow_add, pow_mul_comm tbw (tbNFs e j m)]
        simp only [mul_assoc]

theorem tbqN_mul_tbQProd_self {j : ℕ} (hj : j < 12) (e : ℕ → ℕ) :
    tbqN j * tbQProd e (j + 1) =
      tbQProd (Function.update e j (e j + 1)) (j + 1) * tbw ^ tbNFz e j := by
  have hc : tbw ^ tbNFz e j * tbqN j ^ e j = tbqN j ^ e j * tbw ^ tbNFz e j :=
    (((tbqN_comm hj).pow_right _).pow_left _).symm.eq
  have hm := tbqN_mul_tbQProd hj e (m := j) le_rfl
  rw [tbQProd_succ, tbQProd_succ, Function.update_self,
    tbQProd_congr (e := Function.update e j (e j + 1)) (e' := e) (m := j)
      (fun i hi => Function.update_of_ne (by omega) _ _)]
  calc tbqN j * (tbQProd e j * tbqN j ^ e j) = tbqN j * tbQProd e j * tbqN j ^ e j :=
        (mul_assoc _ _ _).symm
    _ = tbQProd e j * tbqN j * tbw ^ tbNFz e j * tbqN j ^ e j := by rw [hm, tbNFz]
    _ = tbQProd e j * tbqN j ^ (e j + 1) * tbw ^ tbNFz e j := by
      rw [pow_succ']
      simp only [mul_assoc, hc]

theorem tbqN_mul_tbQProd_top {j : ℕ} (hj : j < 12) (e : ℕ → ℕ) : ∀ {m : ℕ}, j < m → m ≤ 12 →
    tbqN j * tbQProd e m = tbQProd (Function.update e j (e j + 1)) m * tbw ^ tbNFz e j
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, h1, h2 => by
    by_cases hmj : m = j
    · subst hmj
      exact tbqN_mul_tbQProd_self hj e
    · have hc : tbw ^ tbNFz e j * tbqN m ^ e m = tbqN m ^ e m * tbw ^ tbNFz e j :=
        (((tbqN_comm (by omega)).pow_right _).pow_left _).symm.eq
      rw [tbQProd_succ, tbQProd_succ, Function.update_of_ne hmj]
      calc tbqN j * (tbQProd e m * tbqN m ^ e m) = tbqN j * tbQProd e m * tbqN m ^ e m :=
            (mul_assoc _ _ _).symm
        _ = tbQProd (Function.update e j (e j + 1)) m * tbw ^ tbNFz e j * tbqN m ^ e m := by
          rw [tbqN_mul_tbQProd_top hj e (m := m) (by omega) (by omega)]
        _ = tbQProd (Function.update e j (e j + 1)) m * tbqN m ^ e m * tbw ^ tbNFz e j := by
          simp only [mul_assoc, hc]

@[expose] def tbNF (L : List ℕ) : (ℕ → ℕ) × ℕ :=
  L.foldl (fun s j => (Function.update s.1 j (s.1 j + 1), s.2 + tbNFz s.1 j)) (fun _ => 0, 0)

theorem gw_tbTreeWord (L : List ℕ) (hL : ∀ j ∈ L, j < 12) :
    gw (tbTreeWord L) = tbQProd (tbNF L).1 12 * tbw ^ (tbNF L).2 := by
  induction L using List.reverseRecOn with
  | nil => simp [tbTreeWord, tbNF, tbQProd, gw_nil]
  | append_singleton L j ih =>
    have hj : j < 12 := hL j (by simp)
    have e1 : tbTreeWord (L ++ [j]) = tbTreeWord L ++ tbQ j := by simp [tbTreeWord]
    have e2 : (tbNF (L ++ [j])).1 = Function.update (tbNF L).1 j ((tbNF L).1 j + 1) := by
      simp [tbNF, List.foldl_append]
    have e3 : (tbNF (L ++ [j])).2 = (tbNF L).2 + tbNFz (tbNF L).1 j := by
      simp [tbNF, List.foldl_append]
    have eq : gw (tbQ j) = tbqN j := rfl
    have ht := tbqN_mul_tbQProd_top hj (tbNF L).1 (m := 12) hj le_rfl
    rw [e1, gw_append, ih (fun k hk => hL k (by simp [hk])), e2, e3, eq, ← mul_assoc, ht, pow_add,
      pow_mul_comm tbw (tbNF L).2]
    simp only [mul_assoc]

theorem tbw_pow_mod (n : ℕ) : tbw ^ n = tbw ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, tbw_pow_three, one_pow, one_mul]

theorem tbQProd_mod (e : ℕ → ℕ) : ∀ {m : ℕ}, m ≤ 12 → tbQProd e m = tbQProd (fun i => e i % 3) m
  | 0, _ => rfl
  | m + 1, hm => by
    have hq : tbqN m ^ 3 = 1 := tbq_pow_three ⟨m, by omega⟩
    rw [tbQProd_succ, tbQProd_succ, tbQProd_mod e (by omega)]
    conv_lhs => rw [← Nat.div_add_mod (e m) 3, pow_add, pow_mul, hq, one_pow, one_mul]

theorem tbQProd_ofFn (e : ℕ → ℕ) :
    tbQProd e 12 = (List.ofFn fun j : Fin 12 => tbq j ^ e j).prod := by
  unfold tbQProd
  congr 1

@[expose] def tbTreeOK (R : List (List ℕ)) (c : List ℕ) (T : List (List ℕ)) (Tc : List ℕ) (i : ℕ) :
    Bool :=
  (T.getD i []).all (fun j => decide (j < 12)) &&
    (List.range 12).all (fun j => (tbNF (T.getD i [])).1 j % 3 == tbEntry R i j) &&
    (((tbNF (T.getD i [])).2 + Tc.getD i 0) % 3 == c.getD i 0 % 3)

theorem tbXTree_ok : ∀ i : Fin 12, tbTreeOK tbXRows tbC1 tbXTree tbXTreeC i = true := by
  decide +kernel

theorem tbYTree_ok : ∀ i : Fin 12, tbTreeOK tbYRows tbC2 tbYTree tbYTreeC i = true := by
  decide +kernel

theorem tbTree_aux (b : List Native.Gen) (R : List (List ℕ)) (c : List ℕ) (T : List (List ℕ))
    (Tc : List ℕ) (gs : List ℕ) (hall : agreeAll (tbTreePairs b T Tc gs) = true) {i : ℕ}
    (hok : tbTreeOK R c T Tc i = true) (hi : i ∈ gs) :
    gw (tbQ i) * gw b =
      gw b * (List.ofFn fun j : Fin 12 => tbq j ^ tbEntry R i j).prod * tbw ^ c.getD i 0 := by
  have h := agreeAll_sound hall
    (b ++ tbQ i, tbTreeWord (T.getD i []) ++ powL (Tc.getD i 0) tbW ++ b)
    (List.mem_map.2 ⟨i, hi, rfl⟩)
  simp only [tbTreeOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at hok
  obtain ⟨⟨hL, hE⟩, hZ⟩ := hok
  simp only [gw_append, tb_gw_powL] at h
  have ew : gw tbW = tbw := rfl
  have hw : gw (tbTreeWord (T.getD i [])) =
      (List.ofFn fun j : Fin 12 => tbq j ^ tbEntry R i j).prod * tbw ^ (tbNF (T.getD i [])).2 := by
    rw [gw_tbTreeWord _ hL, tbQProd_mod _ le_rfl,
      tbQProd_congr (e' := fun j => tbEntry R i j) (fun j hj => hE j hj), tbQProd_ofFn]
  have hc := ((tbQProd_comm (fun j => tbEntry R i j) (m := 12) le_rfl).pow_right (Tc.getD i 0)).eq
  rw [tbQProd_ofFn] at hc
  have hz : tbw ^ (Tc.getD i 0 + (tbNF (T.getD i [])).2) = tbw ^ c.getD i 0 := by
    rw [tbw_pow_mod (Tc.getD i 0 + _), tbw_pow_mod (c.getD i 0), add_comm (Tc.getD i 0), hZ]
  rw [h, hw, ew, ← hz, pow_add, ← mul_assoc (tbw ^ Tc.getD i 0), ← hc]
  simp only [mul_assoc]

theorem tbb₁_conj (i : Fin 12) :
    tbb₁⁻¹ * tbq i * tbb₁ = (List.ofFn fun j => tbq j ^ (tbXMat i j).val).prod *
      tbw ^ tbc₁ i := by
  have hg : ∃ g ∈ ([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]] : List (List ℕ)), (i : ℕ) ∈ g := by
    have := i.2
    interval_cases hi : (i : ℕ) <;> simp
  obtain ⟨g, hg, hig⟩ := hg
  have h := tbTree_aux tbB1 tbXRows tbC1 tbXTree tbXTreeC g (tbAct1_check g hg) (tbXTree_ok i) hig
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  have e : ∀ j : Fin 12, (tbXMat i j).val = tbEntry tbXRows i j := fun j =>
    tbMat_val tbXRows (by decide +kernel) i j
  simp only [e]
  simpa [tbb₁, tbc₁, tbq, mul_assoc] using h

theorem tbb₂_conj (i : Fin 12) :
    tbb₂⁻¹ * tbq i * tbb₂ = (List.ofFn fun j => tbq j ^ (tbYMat i j).val).prod *
      tbw ^ tbc₂ i := by
  have hg : ∃ g ∈ ([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]] : List (List ℕ)), (i : ℕ) ∈ g := by
    have := i.2
    interval_cases hi : (i : ℕ) <;> simp
  obtain ⟨g, hg, hig⟩ := hg
  have h := tbTree_aux tbB2 tbYRows tbC2 tbYTree tbYTreeC g (tbAct2_check g hg) (tbYTree_ok i) hig
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  have e : ∀ j : Fin 12, (tbYMat i j).val = tbEntry tbYRows i j := fun j =>
    tbMat_val tbYRows (by decide +kernel) i j
  simp only [e]
  simpa [tbb₂, tbc₂, tbq, mul_assoc] using h

end CFSG.AGLEmbedding.Norton.MON5_7
