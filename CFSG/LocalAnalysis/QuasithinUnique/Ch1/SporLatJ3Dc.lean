module

public import Certificates.Certificate10501
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Sporadic.Schreier.PairJ3Order

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.J3K

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.Schreier
open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm
open CFSG.KD.J3Dc (L C D Om Lm memOK B0 Sb sbOK sgwOK sgOK invOK)

@[expose] noncomputable def ga : ↥j3P := ⟨j3Gen 0, j3Gen_mem_P 0 (by norm_num)⟩

@[expose] noncomputable def gb : ↥j3P := ⟨j3Gen 1, j3Gen_mem_P 1 (by norm_num)⟩

@[expose] noncomputable def sg (i : ℕ) : ↥j3P := wordElt ga gb (CFSG.KD.J3Dc.J.sgw.getD i [])

@[expose] noncomputable def sl : List ↥j3P := [sg 0, sg 1, sg 2, (sg 0)⁻¹, (sg 1)⁻¹, (sg 2)⁻¹]

@[expose] noncomputable def S : Subgroup ↥j3P := Subgroup.closure {x | x ∈ [sg 0, sg 1, sg 2]}

@[expose] noncomputable def gensY (j : ℕ) : List ↥j3P :=
  [sg 0, sg 1, sg 2] ++ (CFSG.KD.J3Dc.J.mw.getD j []).map (wordElt ga gb)

@[expose] noncomputable def Y (j : ℕ) : Subgroup ↥j3P := Subgroup.closure {x | x ∈ gensY j}

theorem gen : Subgroup.closure ({ga, gb} : Set ↥j3P) = ⊤ := by
  have e : ({ga, gb} : Set ↥j3P) =
      ((↑) : ↥j3P → Equiv.Perm (Fin 6156)) ⁻¹' {j3Gen 0, j3Gen 1} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [e]
  exact Subgroup.closure_closure_coe_preimage

theorem tab_size (g : ↥j3P) : (tab 6156 g).toArray.size = 6156 := by
  simp [CFSG.QuasithinUnique.K1.SporadicPerm.tab]

theorem tab_getD (g : ↥j3P) (p : ℕ) : (tab 6156 g).toArray.getD p 0 = act 6156 g p :=
  img_tab g p

theorem act_coe (g : ↥j3P) {p : ℕ} (hp : p < 6156) :
    act 6156 g p = ((g : Equiv.Perm (Fin 6156)) ⟨p, hp⟩ : ℕ) := by
  have e := act_eq g ⟨p, hp⟩
  rw [Subgroup.smul_def, Equiv.Perm.smul_def] at e
  exact e

theorem good_congr {t : Array ℕ} {f g : ℕ → ℕ} (h : Good 6156 t f) (e : ∀ p < 6156, f p = g p) :
    Good 6156 t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

theorem labF_lt {n : ℕ} {f : ℕ → ℕ} (hf : ∀ p < n, f p < n) {x : List ℕ} (hx : ∀ p ∈ x, p < n) :
    ∀ p ∈ labF f x, p < n := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (insN_mem hp)
  exact hf q (hx q hq)

theorem om_spec {n : ℕ} {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good n (letters.getD l #[]) (M l)) {x0 : List ℕ}
    (hx0 : ∀ p ∈ x0, p < n) {O : OmegaData (List ℕ)}
    (hO : omOKG (fun l x => labF (M l) x) x0 letters.size O = true) :
    OmegaSpec ptAct letters x0 O :=
  (omOKG_sound (fun x => ∀ p ∈ x, p < n) hx0 (fun l hl x hx =>
    ⟨labF_lt (fun p hp => ((hG l hl).2 p hp).2) hx, by
      rw [getElem!_eq_getD']; exact ptAct_good (hG l hl) hx⟩) hO).1

theorem ot_spec {n : ℕ} {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good n (letters.getD l #[]) (M l)) {X0 : List (List ℕ)}
    (hX0 : ∀ x ∈ X0, ∀ p ∈ x, p < n) {O : OmegaData (List (List ℕ))}
    (hO : omOKG (fun l X => X.map (labF (M l))) X0 letters.size O = true) :
    OmegaSpec (tupAct ptAct) letters X0 O :=
  (omOKG_sound (fun X => ∀ x ∈ X, ∀ p ∈ x, p < n) hX0 (fun l hl X hX => by
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact labF_lt (fun p hp => ((hG l hl).2 p hp).2) (hX x hx)
    · unfold tupAct
      refine List.map_congr_left fun x hx => ?_
      rw [getElem!_eq_getD']
      exact ptAct_good (hG l hl) (hX x hx)) hO).1

@[expose] noncomputable def tabs (els : Array ↥j3P) : Array (Array ℕ) :=
  els.map fun g => (tab 6156 g).toArray

theorem tabs_size (els : Array ↥j3P) : (tabs els).size = els.size := Array.size_map ..

theorem tabs_get (els : Array ↥j3P) : ∀ l < (tabs els).size,
    (tabs els)[l]! = (tab 6156 (els.getD l 1)).toArray := by
  intro l hl
  rw [tabs_size] at hl
  unfold tabs
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl, Option.getD_some]

theorem tabs_getD (els : Array ↥j3P) {l : ℕ} (hl : l < (tabs els).size) :
    (tabs els).getD l #[] = (tab 6156 (els.getD l 1)).toArray := by
  rw [← getElem!_eq_getD']
  exact tabs_get els l hl

section Checks


theorem facts : CFSG.KC.SLDc.dcCheck C D = true ∧
    (∀ l < 2, (j3StrongArrs[l]!).size = 6156 ∧
      ∀ p < 6156, (j3StrongArrs[l]!).getD p 0 = L l p ∧ L l p < 6156) ∧
    sgwOK = true ∧ (∀ i < 3, sgOK i = true) ∧ invOK = true ∧
    D.sep = [0, 1, 3, 2] ∧ D.mw.length = 5 ∧ (List.range 5).all memOK = true ∧
    (List.range 5).map (fun j => (Om j).lbl.size) = [1, 3, 3, 9, 15] ∧
    sbOK = true ∧ Sb.lbl.size = 128 :=
  Certificates.certificate10501

theorem good_gen {l : ℕ} (hl : l < 2) {g : ↥j3P} (hg : (g : Equiv.Perm (Fin 6156)) = j3Gen l) :
    Good 6156 (tab 6156 g).toArray (L l) := by
  obtain ⟨hsz, hval⟩ := facts.2.1 l hl
  refine ⟨tab_size g, fun p hp => ⟨?_, (hval p hp).2⟩⟩
  have e3 : (j3StrongArrs[l]!)[p]! = ((j3StrongPerm l) ⟨p, hp⟩ : ℕ) :=
    rep_j3StrongPerm (by omega) ⟨p, hp⟩
  have e4 : (j3StrongArrs[l]!).getD p 0 = (j3StrongArrs[l]!)[p]! := by
    rw [Array.getD_eq_getD_getElem?, getElem!_pos _ p (by omega),
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [tab_getD, act_coe g hp, hg, ← (hval p hp).1, e4, e3]
  rfl

theorem good_a : Good 6156 (tab 6156 ga).toArray (L 0) := good_gen (by norm_num) rfl

theorem good_b : Good 6156 (tab 6156 gb).toArray (L 1) := good_gen (by norm_num) rfl

theorem good_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 6156 (tab 6156 (wordElt ga gb w)).toArray (wordF L w) := by
  have hel : ∀ l < (#[ga, gb] : Array ↥j3P).size,
      (#[(tab 6156 ga).toArray, (tab 6156 gb).toArray] : Array (Array ℕ)).getD l #[] =
        (tab 6156 ((#[ga, gb] : Array ↥j3P).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l <;> rfl
  have e := wordTabA_eq #[ga, gb] _ hel w (by simpa using hw)
  change Good 6156 (tab 6156 (evalElt #[ga, gb] w)).toArray (wordF L w)
  rw [← e]
  refine good_word (fun l hl => ?_) (by simpa using hw)
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · exact good_a
  · exact good_b

theorem sgw_lt {i : ℕ} (hi : i < 3) : ∀ l ∈ CFSG.KD.J3Dc.J.sgw.getD i [], l < 2 := by
  have h := facts.2.2.1
  unfold sgwOK at h
  rw [Bool.and_eq_true] at h
  have hlen := Nat.eq_of_beq_eq_true h.1
  have hmem : CFSG.KD.J3Dc.J.sgw.getD i [] ∈ CFSG.KD.J3Dc.J.sgw := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  intro l hl
  exact Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 h.2 _ hmem) l hl)

theorem good_sg {i : ℕ} (hi : i < 3) : Good 6156 (tab 6156 (sg i)).toArray (L (Nat.add 2 i)) := by
  refine good_congr (good_wordElt (sgw_lt hi)) fun p hp => ?_
  have h := facts.2.2.2.1 i hi
  unfold sgOK at h
  exact (beq_iff_eq.1 (all_range h p hp)).symm

theorem good_sg_inv {i : ℕ} (hi : i < 3) :
    Good 6156 (tab 6156 (sg i)⁻¹).toArray (L (Nat.add 5 i)) := by
  have hg := good_sg hi
  have hinv := facts.2.2.2.2.1
  unfold invOK at hinv
  refine ⟨tab_size _, fun p hp => ?_⟩
  have hq := act_lt (sg i)⁻¹ hp
  have e1 : act 6156 (sg i) (act 6156 (sg i)⁻¹ p) = p := by
    rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]
  have e2 : act 6156 (sg i) (act 6156 (sg i)⁻¹ p) = L (Nat.add 2 i) (act 6156 (sg i)⁻¹ p) := by
    rw [← tab_getD]
    exact (hg.2 _ hq).1
  have e3 := beq_iff_eq.1 (all_range (all_range hinv i hi) _ hq)
  rw [← e2, e1] at e3
  rw [tab_getD, ← e3]
  refine ⟨rfl, ?_⟩
  rw [e3]
  exact hq

theorem hL : ∀ l < 2 + C.ns, Good 6156 (tab 6156 ((ga :: gb :: sl).getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  interval_cases l
  · exact good_a
  · exact good_b
  · exact good_sg (i := 0) (by norm_num)
  · exact good_sg (i := 1) (by norm_num)
  · exact good_sg (i := 2) (by norm_num)
  · exact good_sg_inv (i := 0) (by norm_num)
  · exact good_sg_inv (i := 1) (by norm_num)
  · exact good_sg_inv (i := 2) (by norm_num)

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ [sg 0, sg 1, sg 2]}
  have hg : ∀ y ∈ [sg 0, sg 1, sg 2], y ∈ Subgroup.closure {x | x ∈ [sg 0, sg 1, sg 2]} :=
    fun y hy => Subgroup.subset_closure hy
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact Subgroup.inv_mem _ (hg _ (by simp))
  · exact Subgroup.inv_mem _ (hg _ (by simp))
  · exact Subgroup.inv_mem _ (hg _ (by simp))


theorem hsep : ∀ g : ↥j3P, (∀ p ∈ D.sep, act 6156 g p = p) → g = 1 := by
  intro g hg
  rw [facts.2.2.2.2.2.1] at hg
  have hmem : (g : Equiv.Perm (Fin 6156)) ∈ j3Chain.originalSubgroup := by
    rw [← j3P_eq_original]
    exact g.2
  have h1 := j3_baseFaithful _ hmem fun x hx => by
    have e := hg x.val hx
    rw [act_coe g x.2] at e
    exact Fin.ext e
  exact Subtype.ext h1

theorem stab_B0_eq_one (g : ↥j3P) (hg : lab 6156 (tupLab ptLab) B0 g = B0) : g = 1 := by
  apply hsep g
  rw [facts.2.2.2.2.2.1]
  have e : ∀ q < 6156, ptAct (tab 6156 g).toArray [q] = [act 6156 g q] := by
    intro q _
    rw [ptAct_tab]
    exact sortN_of_pairwise (List.pairwise_singleton _ _)
  have hg' : [ptAct (tab 6156 g).toArray [0], ptAct (tab 6156 g).toArray [1],
      ptAct (tab 6156 g).toArray [3], ptAct (tab 6156 g).toArray [2]] = [[0], [1], [3], [2]] := hg
  rw [e 0 (by norm_num), e 1 (by norm_num), e 3 (by norm_num), e 2 (by norm_num)] at hg'
  simp only [List.cons.injEq, and_true] at hg'
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hg'.1
  · exact hg'.2.1
  · exact hg'.2.2.1
  · exact hg'.2.2.2

theorem B0_valid : ∀ x ∈ B0, PtValid 6156 x := by
  decide

theorem card_S : Nat.card S = 128 := by
  let els : Array ↥j3P := #[sg 0, sg 1, sg 2]
  have hlaw := tupLawful (ptLab_lawful (Γ := ↥j3P) (n := 6156))
  have hG : ∀ l < (tabs els).size, Good 6156 ((tabs els).getD l #[]) (L (Nat.add 2 l)) := by
    intro l hl
    have hl' : l < 3 := by simpa [tabs_size, els] using hl
    rw [tabs_getD els hl]
    interval_cases l
    · exact good_sg (i := 0) (by norm_num)
    · exact good_sg (i := 1) (by norm_num)
    · exact good_sg (i := 2) (by norm_num)
  have hsz3 : (tabs els).size = 3 := by simp [tabs_size, els]
  have hO : OmegaSpec (tupLab ptLab).act (tabs els) B0 Sb :=
    ot_spec hG (fun x hx => (B0_valid x hx).2) (by rw [hsz3]; exact facts.2.2.2.2.2.2.2.2.2.1)
  have hc := OmegaSpec.card_eq hlaw B0_valid els (tabs_size els).symm (tabs_get els) hO
    (H := S) rfl (fun g hg => by
      rw [stab_B0_eq_one g hg]
      exact S.one_mem)
  have hbot : stab hlaw B0_valid = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact stab_B0_eq_one g hg
  rw [hc, hbot, Subgroup.card_bot, facts.2.2.2.2.2.2.2.2.2.2]

theorem n_card : Nat.card ↥j3P = C.N * 2 ^ C.k := by
  change Nat.card ↥j3P = 392445 * 2 ^ 7
  rw [card_j3P]
  norm_num

theorem delta_valid : PtValid 6156 C.Δ := by
  decide

theorem dc_facts :
    (∀ g : ↥j3P, lab 6156 ptLab C.Δ g = C.Δ ↔ g ∈ S) ∧
    ∀ Z : Subgroup ↥j3P, S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 Y j := by
  have h0 := dcCheck_sound (Γ := ↥j3P) (n := 6156) C rfl D ga gb gen sl rfl hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ [sg 0, sg 1, sg 2]}) = 2 ^ 7
        exact card_S) n_card hsep delta_valid facts.1
  have hlen : D.mw.length = 5 := facts.2.2.2.2.2.2.1
  rw [hlen] at h0
  exact h0

theorem mw_lt {j : ℕ} : ∀ w ∈ CFSG.KD.J3Dc.J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  have h : (CFSG.KD.J3Dc.J.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true :=
    by decide
  intro w hw l hl
  by_cases hj : j < CFSG.KD.J3Dc.J.mw.length
  · rw [List.getD_eq_getElem _ _ hj] at hw
    exact Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h _
      (List.getElem_mem hj)) w hw) l hl)
  · rw [List.getD_eq_default _ _ (by omega)] at hw
    simp at hw

theorem wordElt_nil : wordElt ga gb [] = 1 := evalElt_nil _

theorem gensY_getD (j : ℕ) {l : ℕ} (hl : l < 3 + (CFSG.KD.J3Dc.J.mw.getD j []).length) :
    (gensY j).toArray.getD l 1 = bif Nat.blt l 3 then [sg 0, sg 1, sg 2].getD l 1 else
      wordElt ga gb ((CFSG.KD.J3Dc.J.mw.getD j []).getD (l - 3) []) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  unfold gensY
  by_cases h3 : l < 3
  · have hb : Nat.blt l 3 = true := Nat.blt_eq.mpr h3
    rw [hb, List.getD_append _ _ _ _ (by simpa using h3)]
    rfl
  · have hb : Nat.blt l 3 = false := by
      cases hc : Nat.blt l 3
      · rfl
      · exact absurd (Nat.blt_eq.mp hc) h3
    rw [hb, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_cons, List.length_nil, zero_add, cond_false]
    rw [← wordElt_nil, List.getD_map]

theorem good_Y (j : ℕ) : ∀ l < (tabs (gensY j).toArray).size,
    Good 6156 ((tabs (gensY j).toArray).getD l #[]) (Lm j l) := by
  intro l hl
  have hl' : l < 3 + (CFSG.KD.J3Dc.J.mw.getD j []).length := by
    simp [tabs_size, gensY] at hl
    simp only [List.getD_eq_getElem?_getD]
    omega
  rw [tabs_getD _ hl, gensY_getD j hl']
  by_cases h3 : l < 3
  · have hb : Nat.blt l 3 = true := Nat.blt_eq.mpr h3
    have e : Lm j l = L (Nat.add 2 l) := by
      unfold Lm
      rw [hb]
      rfl
    rw [hb, e]
    simp only [cond_true]
    interval_cases l
    · exact good_sg (i := 0) (by norm_num)
    · exact good_sg (i := 1) (by norm_num)
    · exact good_sg (i := 2) (by norm_num)
  · have hb : Nat.blt l 3 = false := by
      cases hc : Nat.blt l 3
      · rfl
      · exact absurd (Nat.blt_eq.mp hc) h3
    have e : Lm j l = wordF L ((CFSG.KD.J3Dc.J.mw.getD j []).getD (l - 3) []) := by
      unfold Lm
      rw [hb]
      rfl
    rw [hb, e]
    simp only [cond_false]
    have hi : l - 3 < (CFSG.KD.J3Dc.J.mw.getD j []).length := by omega
    have hmem : (CFSG.KD.J3Dc.J.mw.getD j []).getD (l - 3) [] ∈ CFSG.KD.J3Dc.J.mw.getD j [] := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact good_wordElt (mw_lt _ hmem)

theorem S_le_Y (j : ℕ) : S ≤ Y j :=
  Subgroup.closure_mono fun x hx => List.mem_append_left _ hx

theorem card_Y {j : ℕ} (hj : j < 5) : Nat.card (Y j) = (Om j).lbl.size * Nat.card S := by
  have hm := List.all_eq_true.1 facts.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj)
  unfold memOK at hm
  have hsz : (tabs (gensY j).toArray).size = Nat.add 3 (CFSG.KD.J3Dc.J.mw.getD j []).length := by
    simp [tabs_size, gensY, List.getD_eq_getElem?_getD]
    omega
  rw [← hsz] at hm
  have hO := om_spec (good_Y j) (fun p hp => delta_valid.2 p hp) hm
  have hstab : stab (ptLab_lawful (Γ := ↥j3P) (n := 6156)) delta_valid = S := by
    ext g
    exact dc_facts.1 g
  have hc := OmegaSpec.card_eq ptLab_lawful delta_valid (gensY j).toArray
    (tabs_size _).symm (tabs_get _) hO (H := Y j) (by rw [List.toList_toArray]; rfl)
    (by rw [hstab]; exact S_le_Y j)
  rw [hc, hstab]

theorem member_card {j : ℕ} (hj : j < 5) :
    Nat.card (Y j) = #[1, 3, 3, 9, 15][j]! * Nat.card S := by
  rw [card_Y hj]
  have h := facts.2.2.2.2.2.2.2.2.1
  change [(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size, (Om 3).lbl.size,
    (Om 4).lbl.size] = [1, 3, 3, 9, 15] at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  interval_cases j
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem complete : ∀ Z : Subgroup ↥j3P, S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 Y j :=
  dc_facts.2

theorem S_index : S.index = 392445 := by
  have h1 := Subgroup.card_mul_index S
  rw [card_S, card_j3P] at h1
  omega

theorem S_sylow : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 7) card_S, ?_⟩
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S, S_index]
  norm_num

end Checks

end CFSG.QuasithinUnique.Ch1.SporLat.J3K

end
