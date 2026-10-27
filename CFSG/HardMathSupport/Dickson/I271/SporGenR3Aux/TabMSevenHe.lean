module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenHeRec
public import Certificates.Certificate17480
public import Certificates.Certificate17481
public import Certificates.Certificate17482
public import Certificates.Certificate17483
public import Certificates.Certificate17484
public import Certificates.Certificate17485
public import Certificates.Certificate17490
public import Certificates.Certificate17491
public import Certificates.Certificate17492
public import Certificates.Certificate17493
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held
import all TauCeti.GroupTheory.Presentation.GroupPresentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.TwoGen (img2)

@[expose] def heE (c : ℕ) : List (ℕ × Bool) :=
  if c = 0 then [(0, true)] else if c = 1 then [(1, true)] else if c = 2 then [(1, false)]
  else heMacS.getD (c - 3) []

@[expose] def normA (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.map fun l => if l.1 = 0 then (0, true) else l

@[expose] def invL (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

theorem wordProd_cons {G : Type*} [Group G] (x : ℕ → G) (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    wordProd x (l :: w) = (if l.2 then x l.1 else (x l.1)⁻¹) * wordProd x w := by
  simp [wordProd]

theorem wordProd_append {G : Type*} [Group G] (x : ℕ → G) (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp [wordProd]

theorem wordProd_invL {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (invL w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [invL, wordProd]
  | cons l w ih =>
    have h : invL (l :: w) = invL w ++ [(l.1, !l.2)] := by simp [invL]
    rw [h, wordProd_append, ih, wordProd_cons, wordProd_cons, mul_inv_rev]
    cases l.2 <;> simp [wordProd]

theorem wordProd_normA {G : Type*} [Group G] (x : ℕ → G) (hx : (x 0)⁻¹ = x 0)
    (w : List (ℕ × Bool)) : wordProd x (normA w) = wordProd x w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨i, s⟩ := l
    have h : normA ((i, s) :: w) = (if i = 0 then (0, true) else (i, s)) :: normA w := rfl
    rw [h, wordProd_cons, wordProd_cons, ih]
    by_cases hi : i = 0
    · subst hi
      cases s <;> simp [hx]
    · simp [hi]

theorem wordProd_eq_one_of_rotate {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool))
    (k : ℕ) (h : wordProd x (w.rotate k) = 1) : wordProd x w = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, wordProd_append] at h
  rw [← List.take_append_drop (k % w.length) w, wordProd_append]
  exact mul_eq_one_comm.1 h

@[expose] def heRels : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true)],
   [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
   [(0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true),
    (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true),
    (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true),
    (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true),
    (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)],
   [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
    (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
    (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)]]

theorem heRelLetters : TauCeti.Sporadic.hePresentation.relatorLetters = heRels := by
  simp [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.hePresentation, TauCeti.GroupPresentation.generatorCount, FreeGroup.invRev,
    heRels]

theorem heMacC_spell : ∀ i < heMacW.length,
    (heMacC.getD i []).flatMap heE = normA (invL (heMacS.getD i [])) := by
  decide

theorem heMacC_lt : ∀ i < heMacW.length, ∀ c ∈ heMacC.getD i [], c < 3 + i := by
  decide

theorem heRelC_spell : ∀ j < 7,
    (heRelC.getD j []).flatMap heE = normA ((heRels.getD j []).rotate (heRot.getD j 0)) := by
  decide

theorem heRelC_lt : ∀ j < 7, ∀ c ∈ heRelC.getD j [], c < 3 + heMacW.length := by
  decide

theorem heRelC_length : heRelC.length = 7 := by
  decide

theorem getD_mem_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem gw_reverse_flatten (ws : List (List Native.Gen)) :
    gw ws.reverse.flatten = (ws.map gw).prod := by
  induction ws with
  | nil => exact gw_nil
  | cons w ws ih =>
    rw [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, gw_append, ih, List.map_cons, List.prod_cons]

@[expose] noncomputable def heAG : Gmat := gw heA

@[expose] noncomputable def heBG : Gmat := gw heB

@[expose] noncomputable def heVal (c : ℕ) : Gmat := wordProd (img2 heAG heBG) (heE c)

theorem gw_heProdW {L : List ℕ} (h : ∀ c ∈ L, gw (heCodeW c) = heVal c) :
    gw (heProdW L) = wordProd (img2 heAG heBG) (L.flatMap heE) := by
  unfold heProdW
  rw [gw_reverse_flatten]
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.flatMap_cons, wordProd_append,
      h c (by simp), ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    rfl

section Words

variable (hW : ∀ w ∈ heWordList (), gw w = 1)
include hW

theorem heAG_mul_self : heAG * heAG = 1 := by
  have hmem : heProdW (heRelC.getD 0 []) ∈ heWordList () := by
    simp only [heWordList, List.mem_append, List.mem_map]
    exact Or.inr ⟨heRelC.getD 0 [], getD_mem_of_lt (by rw [heRelC_length]; norm_num), rfl⟩
  have h := hW _ hmem
  have h0 : heRelC.getD 0 [] = [0, 0] := by decide
  rw [h0] at h
  simpa [heProdW, heCodeW, gw_append, heAG] using h

theorem heAG_inv : heAG⁻¹ = heAG :=
  (eq_inv_of_mul_eq_one_right (heAG_mul_self hW)).symm

theorem gw_heBi : gw heBi = heBG⁻¹ := by
  have h := hW (heBi ++ heB)
    (List.mem_append_left _ (List.mem_append_left _ (.tail _ (.head _))))
  rw [gw_append] at h
  exact eq_inv_of_mul_eq_one_right h

theorem gw_code : ∀ c, c < 3 + heMacW.length → gw (heCodeW c) = heVal c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | h3
    · simp [heCodeW, heVal, heE, wordProd, img2, heAG]
    · simp [heCodeW, heVal, heE, wordProd, img2, heBG]
    · rw [show heCodeW 2 = heBi from rfl, gw_heBi hW]
      simp [heVal, heE, wordProd, img2]
    · obtain ⟨i, rfl⟩ : ∃ i, c = 3 + i := ⟨c - 3, by omega⟩
      have hi : i < heMacW.length := by omega
      have hcw : heCodeW (3 + i) = heMacW.getD i [] := by
        rw [heCodeW, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show 3 + i - 3 = i by omega]
      have hmem : heMacW.getD i [] ++ heProdW (heMacC.getD i []) ∈ heWordList () := by
        simp only [heWordList, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      have h := hW _ hmem
      have hlt := heMacC_lt i hi
      have hx : (img2 heAG heBG 0)⁻¹ = img2 heAG heBG 0 := by
        simpa [img2] using heAG_inv hW
      rw [gw_append, gw_heProdW (fun c' hc' => ih c' (hlt c' hc') (by have := hlt c' hc'; omega)),
        heMacC_spell i hi, wordProd_normA _ hx, wordProd_invL] at h
      rw [hcw, eq_inv_of_mul_eq_one_right h, inv_inv, heVal, heE, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), show 3 + i - 3 = i by omega]

theorem heRel_of_words : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
    wordProd (img2 heAG heBG) v = 1 := by
  rw [heRelLetters]
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hj7 : j < 7 := by simpa [heRels] using hj
  have hjc : j < heRelC.length := by rw [heRelC_length]; exact hj7
  have hmem : heProdW (heRelC.getD j []) ∈ heWordList () := by
    simp only [heWordList, List.mem_append, List.mem_map]
    exact Or.inr ⟨heRelC.getD j [], getD_mem_of_lt hjc, rfl⟩
  have h := hW _ hmem
  have hx : (img2 heAG heBG 0)⁻¹ = img2 heAG heBG 0 := by
    simpa [img2] using heAG_inv hW
  rw [gw_heProdW (fun c hc => gw_code hW c (heRelC_lt j hj7 c hc)), heRelC_spell j hj7,
    wordProd_normA _ hx] at h
  have h' := wordProd_eq_one_of_rotate _ _ _ h
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h'

end Words

section Comm


theorem gw_heD : gw heD = dG := rfl

theorem gw_heD6 : gw heD6 = dG⁻¹ := by
  have h6 : heD6 = heD ++ heD ++ heD ++ heD ++ heD ++ heD := rfl
  rw [h6]
  simp only [gw_append]
  rw [gw_heD]
  refine eq_inv_of_mul_eq_one_left ?_
  have h7 := dG_pow
  simpa [pow_succ, mul_assoc] using h7

variable (hW : ∀ w ∈ heWordList (), gw w = 1)
include hW

theorem heAG_comm_dG : heAG * dG = dG * heAG := by
  have h := hW (heA ++ heD ++ heA ++ heD6)
    (List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.head _)))))
  simp only [gw_append] at h
  rw [gw_heD, gw_heD6] at h
  have h1 : heAG * (dG * heAG) = dG := by
    have := congrArg (dG * ·) h
    exact (by simpa [mul_assoc] using this : gw heA * (dG * gw heA) = dG)
  calc heAG * dG = heAG * (dG * heAG) * heAG⁻¹ := by group
    _ = dG * heAG := by rw [h1, heAG_inv hW]

theorem heBG_comm_dG : heBG * dG = dG * heBG := by
  have hU := hW (heUi ++ heU) (List.mem_append_left _ (List.mem_append_left _ (.head _)))
  rw [gw_append] at hU
  have hUi : gw heUi = (gw heU)⁻¹ := eq_inv_of_mul_eq_one_right hU
  have h := hW (heU ++ heD ++ heUi ++ heD6)
    (List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))))
  simp only [gw_append] at h
  rw [gw_heD, gw_heD6, hUi] at h
  have hc : gw heU * dG = dG * gw heU := by
    have h2 : (gw heU)⁻¹ * (dG * gw heU) = dG := by
      have := congrArg (dG * ·) h
      simpa [mul_assoc] using this
    calc gw heU * dG = gw heU * ((gw heU)⁻¹ * (dG * gw heU)) := by rw [h2]
      _ = dG * gw heU := by group
  have hB : heB = heU ++ heU ++ heU := rfl
  have hBG : heBG = gw heU * (gw heU * gw heU) := by
    rw [heBG, hB, gw_append, gw_append]
  rw [hBG]
  have hc' : Commute (gw heU) dG := hc
  have := ((hc'.mul_left hc').mul_left hc').eq
  simpa [mul_assoc] using this

end Comm

section Checks


theorem fix_of_chunks {v : Native.DVec} {chunks : List (List ℕ)}
    (h : ∀ ks ∈ chunks, CFSG.YGroups.Y443.fixAll (heChunk ks) v = true)
    (hcov : ∀ k < (heWordList ()).length, ∃ ks ∈ chunks, k ∈ ks) :
    ∀ w ∈ heWordList (), wordLin w (interp v) = interp v := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
  obtain ⟨ks, hks, hkk⟩ := hcov k hk
  have := CFSG.YGroups.Y443.fixAll_sound (h ks hks) ((heWordList ()).getD k [])
    (List.mem_map.2 ⟨k, hkk, rfl⟩)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this

theorem heWordList_length : (heWordList ()).length = 15 := by
  rfl


open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem heWords_fix_a :
    ∀ w ∈ heWordList (), wordLin w (interp (aV ())) = interp (aV ()) := by
  refine fix_of_chunks (chunks := [[0, 7, 14], [1, 2, 5, 6], [3, 10, 12], [4, 8, 9, 11, 13]]) ?_ ?_
  · intro ks hks
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
    rcases hks with rfl | rfl | rfl | rfl
    · exact Certificates.certificate17480
    · exact Certificates.certificate17481
    · exact Certificates.certificate17482
    · exact Certificates.certificate17483
  · rw [heWordList_length]
    decide

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem heWords_fix_b :
    ∀ w ∈ heWordList (), wordLin w (interp (bV ())) = interp (bV ()) := by
  refine fix_of_chunks (chunks := [[0, 3, 5, 14], [1, 2, 4, 8, 10, 11, 13], [6, 7, 9, 12]]) ?_ ?_
  · intro ks hks
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
    rcases hks with rfl | rfl | rfl
    · exact Certificates.certificate17484
    · exact Certificates.certificate17485
    · exact Certificates.certificate17490
  · rw [heWordList_length]
    decide

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem heWords_fix_w :
    ∀ w ∈ heWordList (), wordLin w (interp (wV ())) = interp (wV ()) := by
  refine fix_of_chunks (chunks := [[0, 3, 5, 14], [1, 2, 4, 8, 10, 11, 13], [6, 7, 9, 12]]) ?_ ?_
  · intro ks hks
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
    rcases hks with rfl | rfl | rfl
    · exact Certificates.certificate17491
    · exact Certificates.certificate17492
    · exact Certificates.certificate17493.1
  · rw [heWordList_length]
    decide


theorem heWords_eq_one : ∀ w ∈ heWordList (), gw w = 1 := fun w hw =>
  Subtype.ext (CFSG.YGroups.Y443.wordLin_eq_one (heWords_fix_a w hw) (heWords_fix_b w hw)
    (heWords_fix_w w hw))

theorem heAG_ne_one : heAG ≠ 1 :=
  gw_ne_one_of_moveCheck Certificates.certificate17493.2

end Checks

section Main


theorem tabMSeven_he_le_cent_dG :
    Subgroup.closure ({heAG, heBG} : Set Gmat) ≤ Subgroup.centralizer ({dG} : Set Gmat) ∧
      Nonempty (↥(Subgroup.closure ({heAG, heBG} : Set Gmat)) ≃* ↥CFSG.Sporadic.HeldB.heP) := by
  have hW := heWords_eq_one
  refine ⟨?_, tabMSeven_nonempty_mulEquiv_heP_of_relators (heRel_of_words hW) heAG_ne_one⟩
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (heAG_comm_dG hW)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (heBG_comm_dG hW)

end Main

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
