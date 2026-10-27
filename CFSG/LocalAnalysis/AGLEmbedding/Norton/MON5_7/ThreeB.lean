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

theorem tbAct1_check0 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [0, 1, 2]) = true :=
  Certificates.certificate125368

theorem tbAct1_check1 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [3, 4, 5]) = true :=
  Certificates.certificate125369

theorem tbAct1_check2 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [6, 7, 8]) = true :=
  Certificates.certificate125370

theorem tbAct1_check3 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [9, 10, 11]) = true :=
  Certificates.certificate125371

theorem tbAct1_check : ∀ g ∈ ([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]] : List (List ℕ)),
    agreeAll (tbActPairs tbB1 tbXRows tbC1 g) = true := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact tbAct1_check0
  · exact tbAct1_check1
  · exact tbAct1_check2
  · exact tbAct1_check3

theorem tbAct2_check0 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [0, 1, 2, 3]) = true :=
  Certificates.certificate125372

theorem tbAct2_check1 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [4, 5, 6, 7]) = true :=
  Certificates.certificate125373

theorem tbAct2_check2 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [8, 9, 10, 11]) = true :=
  Certificates.certificate125374

theorem tbAct2_check : ∀ g ∈ ([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]] : List (List ℕ)),
    agreeAll (tbActPairs tbB2 tbYRows tbC2 g) = true := by
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

theorem tbb₁_conj (i : Fin 12) :
    tbb₁⁻¹ * tbq i * tbb₁ = (List.ofFn fun j => tbq j ^ (tbXMat i j).val).prod *
      tbw ^ tbc₁ i := by
  have hg : ∃ g ∈ ([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]] : List (List ℕ)), (i : ℕ) ∈ g := by
    have := i.2
    interval_cases hi : (i : ℕ) <;> simp
  obtain ⟨g, hg, hig⟩ := hg
  have h := tbAct_aux tbB1 tbXRows tbC1 g (tbAct1_check g hg) hig
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
  have h := tbAct_aux tbB2 tbYRows tbC2 g (tbAct2_check g hg) hig
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  have e : ∀ j : Fin 12, (tbYMat i j).val = tbEntry tbYRows i j := fun j =>
    tbMat_val tbYRows (by decide +kernel) i j
  simp only [e]
  simpa [tbb₂, tbc₂, tbq, mul_assoc] using h

end CFSG.AGLEmbedding.Norton.MON5_7
