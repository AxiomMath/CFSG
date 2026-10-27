module

public import Certificates.Data.Kernel.Sp62Syl.Defs
public import CFSG.Certificates.Kernel.U42Syl.Sound
public import CFSG.Certificates.Kernel.Sp62W.Cosets

public section

namespace CFSG.KC.Sp62Syl

open CFSG.KD.Sp62Syl CFSG.KD.U42Syl CFSG.KC.U42Syl CFSG.KD.Sp62W CFSG.KC.Sp62W CFSG.KC.Mat8P
  CFSG.KGroups.Sp6 CFSG.Quasithin.H13 CFSG.AGLEmbedding.KFactProofs.Sp62Local
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem exists_decomp (hW : Nat.card (Hgen gensWD) = 51840) (hc : dcCosetsCheck = true)
    (x : H6) : ∃ w ∈ Hgen gensWD, ∃ k < 28, x = w * tE k := by
  have hnd : ((List.range 28).map fun k => qbits (dcRep k)).Nodup := by
    simp only [dcCosetsCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.2
  let φ : Hgen gensWD × Fin 28 → H6 := fun p => p.1 * tE p.2
  have hinj : Function.Injective φ := by
    rintro ⟨w, k⟩ ⟨w', j⟩ h
    have hq : qbits (dcRep k) = qbits (dcRep j) := by
      have := congrArg qOf h
      simp only [φ, qOf_mul_left hc w.2, qOf_mul_left hc w'.2] at this
      rwa [qOf_eq (rep_tE hc k.2).1, qOf_eq (rep_tE hc j.2).1] at this
    have hkj : k = j := Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 k.2)
      (List.mem_range.2 j.2) hq)
    subst hkj
    exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  have hcard : Nat.card H6 ≤ Nat.card (Hgen gensWD × Fin 28) := by
    rw [Nat.card_prod, hW, card_H6]
    simp
  have hfin : Finite H6 := Nat.finite_of_card_ne_zero (by rw [card_H6]; norm_num)
  obtain ⟨⟨w, k⟩, hx⟩ := (hinj.bijective_of_nat_card_le hcard).2 x
  exact ⟨w, w.2, k, k.2, hx.symm⟩

theorem mul_inv_mem_of_qOf_eq (hW : Nat.card (Hgen gensWD) = 51840) (hc : dcCosetsCheck = true)
    {x y : H6} (h : qOf x = qOf y) : x * y⁻¹ ∈ Hgen gensWD := by
  have hnd : ((List.range 28).map fun k => qbits (dcRep k)).Nodup := by
    simp only [dcCosetsCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.2
  obtain ⟨w, hw, k, hk, rfl⟩ := exists_decomp hW hc x
  obtain ⟨w', hw', j, hj, rfl⟩ := exists_decomp hW hc y
  rw [qOf_mul_left hc hw, qOf_mul_left hc hw', qOf_eq (rep_tE hc hk).1,
    qOf_eq (rep_tE hc hj).1] at h
  obtain rfl := List.inj_on_of_nodup_map hnd (List.mem_range.2 hk) (List.mem_range.2 hj) h
  have e : w * tE k * (w' * tE k)⁻¹ = w * w'⁻¹ := by group
  rw [e]
  exact mul_mem hw (inv_mem hw')

theorem qbits_append {c : List ℕ} (l : List ℕ) (h : c.length = 6) : qbits (c ++ l) = qbits c := by
  unfold qbits
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

theorem qOf_of_repN {g : H6} {X : ℕ} (h : RepN g X) : qOf g = qbits (unpackM X) := by
  obtain ⟨c, hc, hgc, rfl⟩ := h
  rw [qOf_eq hgc, CFSG.KC.Sp62W.unpackM_numC hc, qbits_append _ (CFSG.KC.Sp62W.validB_iff.1 hc).1]

theorem exists_T0_g1_W (hW : Nat.card (Hgen gensWD) = 51840) (hc : dcCosetsCheck = true)
    {QW : List (List ℕ)}
    (hq : (Nat.beq (mulP (numC cG1) (numC cG1)) oneP && qwK (gensT.map numC) (numC cG1) QW) = true)
    {g : H6} (hg : g ∉ Hgen gensWD) :
    ∃ t ∈ Hgen gensT, ∃ w ∈ Hgen gensWD, g = t * elt cG1 * w := by
  rw [Bool.and_eq_true] at hq
  obtain ⟨hg1, hq⟩ := hq
  have hiso1 : isoB cG1 = true := by decide
  have hr1 := repN_elt hiso1
  have h11 : elt cG1 * elt cG1 = 1 := by
    have := hr1.mul hr1
    rw [Nat.eq_of_beq_eq_true hg1] at this
    exact this.eq RepN.one
  have hinv1 : (elt cG1)⁻¹ = elt cG1 := (eq_inv_of_mul_eq_one_left h11).symm
  obtain ⟨w, hw, k, hk, hx⟩ := exists_decomp hW hc g⁻¹
  have hk0 : k ≠ 0 := by
    rintro rfl
    refine hg ?_
    have : g⁻¹ ∈ Hgen gensWD := by
      rw [hx, tE, if_pos rfl, mul_one]
      exact hw
    simpa using this
  simp only [qwK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hq
  obtain ⟨-, hall⟩ := hq
  have hqk := hall (k - 1) (by omega)
  obtain ⟨t, ht, hrt⟩ := wvP_rep (gens_rep gensT_iso) (QW.getD (k - 1) [])
  have hqe : qOf (g⁻¹) = qOf (elt cG1 * t) := by
    rw [qOf_of_repN (hr1.mul hrt), hqk, Nat.sub_add_cancel (by omega : 1 ≤ k), hx,
      qOf_mul_left hc hw, qOf_eq (rep_tE hc hk).1]
  have hm := mul_inv_mem_of_qOf_eq hW hc hqe
  refine ⟨t⁻¹, inv_mem ht, (g⁻¹ * (elt cG1 * t)⁻¹)⁻¹, inv_mem hm, ?_⟩
  have e : (g⁻¹ * (elt cG1 * t)⁻¹)⁻¹ = (elt cG1)⁻¹⁻¹ * t * g := by group
  have e2 : t⁻¹ * elt cG1 * (elt cG1 * t * g) = t⁻¹ * (elt cG1 * elt cG1) * t * g := by group
  rw [e, inv_inv, e2, h11]
  group

theorem ttK_sound {AT : List ℕ} {TP : ℕ} :
    ∀ (L : List (List ℕ)) (i : ℕ), ttK AT TP L i = true →
      ∀ j < L.length, laneP TP (i + j) = wvP AT (L.getD j [])
  | [], _, _, j, hj => absurd hj (by simp)
  | w :: L, i, h, j, hj => by
    have h' : (Nat.beq (laneP TP i) (wvP AT w) && ttK AT TP L (Nat.succ i)) = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero => exact Nat.eq_of_beq_eq_true h'.1
    | succ j =>
      have := ttK_sound L (Nat.succ i) h'.2 j (by simpa using hj)
      rw [List.getD_cons_succ, ← this, Nat.succ_add, Nat.add_succ]

theorem rowsK_sound {AT AW AT2 : List ℕ} {G1 cT cI cD WP : ℕ} :
    ∀ (L : List (List ℕ × List ℕ × List (List ℕ))) (i : ℕ),
      rowsK AT AW AT2 G1 cT cI cD WP L i = true → ∀ j < L.length,
      ∃ r ∈ L, rowB AT AT2 G1 cT cI cD (laneP WP (i + j)) (wvP AW r.1) (wvP AW r.2.1) r.2.2 = true
  | [], _, _, j, hj => absurd hj (by simp)
  | r :: L, i, h, j, hj => by
    have h' : (rowB AT AT2 G1 cT cI cD (laneP WP i) (wvP AW r.1) (wvP AW r.2.1) r.2.2 &&
        rowsK AT AW AT2 G1 cT cI cD WP L (Nat.succ i)) = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero => exact ⟨r, List.mem_cons_self .., h'.1⟩
    | succ j =>
      obtain ⟨r', hr', hb⟩ := rowsK_sound L (Nat.succ i) h'.2 j (by simpa using hj)
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      rwa [Nat.add_succ, ← Nat.succ_add]

theorem gensWD_iso : gensWD.all isoB = true := by decide

theorem row_facts (h11 : elt cG1 * elt cG1 = 1) {Wl U UI : ℕ} {xw : List (List ℕ)}
    {uw uwi : List ℕ} (hU : U = wvP (gensWD.map numC) uw) (hUI : UI = wvP (gensWD.map numC) uwi)
    (h : rowB (gensT.map numC) (gensT.map fun c => numC (mulC c c)) (numC cG1) (numC cTau)
      (numC cIo) (numC cGD) Wl U UI xw = true) :
    ∃ w ∈ Hgen gensWD, RepN w Wl ∧ Hgen gensWD ≤ Hgen gensT ⊔ Subgroup.zpowers (elt cG1 * w) := by
  unfold rowB xwB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hUl, hUU⟩, ⟨hT, hI⟩, hD⟩ := h
  obtain ⟨w, hw, hrw⟩ := wvP_rep (gens_rep gensWD_iso) uw
  obtain ⟨w', -, hrw'⟩ := wvP_rep (gens_rep gensWD_iso) uwi
  rw [← hU] at hrw
  rw [← hUI] at hrw'
  have hww : w * w' = 1 := by
    have := hrw.mul hrw'
    rw [Nat.eq_of_beq_eq_true hUU] at this
    exact this.eq RepN.one
  have hw' : w' = w⁻¹ := eq_inv_of_mul_eq_one_right hww
  subst hw'
  have hr1 := repN_elt (c := cG1) (by decide)
  have hinv1 : (elt cG1)⁻¹ = elt cG1 := (eq_inv_of_mul_eq_one_left h11).symm
  refine ⟨w, hw, (Nat.eq_of_beq_eq_true hUl) ▸ hrw, ?_⟩
  let H := Hgen gensT ⊔ Subgroup.zpowers (elt cG1 * w)
  have hy : elt cG1 * w ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hTH : Hgen gensT ≤ H := le_sup_left
  have hA : ∀ X ∈ gensT.map numC ++ [mulP (numC cG1) U] ++
      (gensT.map fun c => numC (mulC c c)) ++ [mulP UI (numC cG1)], ∃ g ∈ H, RepN g X := by
    intro X hX
    simp only [List.mem_append, List.mem_singleton] at hX
    rcases hX with ((hX | rfl) | hX) | rfl
    · obtain ⟨g, hg, hrg⟩ := gens_rep gensT_iso X hX
      exact ⟨g, hTH hg, hrg⟩
    · exact ⟨_, hy, hr1.mul hrw⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hX
      have hiso : isoB c = true := List.all_eq_true.1 gensT_iso c hc
      have hv : validB c = true := by
        unfold isoB at hiso
        rw [Bool.and_eq_true] at hiso
        exact hiso.1
      refine ⟨elt c * elt c, mul_mem (hTH (elt_mem_Hgen hc)) (hTH (elt_mem_Hgen hc)), ?_⟩
      exact ⟨mulC c c, CFSG.KC.Sp62W.validB_mulC hv hv, (rep_elt hiso).mul (rep_elt hiso), rfl⟩
    · refine ⟨w⁻¹ * elt cG1, ?_, hrw'.mul hr1⟩
      have e : w⁻¹ * elt cG1 = (elt cG1 * w)⁻¹ := by rw [mul_inv_rev, hinv1]
      rw [e]
      exact inv_mem hy
  have hmem : ∀ c ∈ [cTau, cIo, cGD], elt c ∈ H := by
    intro c hc
    have hiso : isoB c = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨g, hg, hrg⟩ := wvP_rep hA (xw.getD 0 [])
      rw [Nat.eq_of_beq_eq_true hT] at hrg
      rwa [← hrg.eq (repN_elt hiso)]
    · obtain ⟨g, hg, hrg⟩ := wvP_rep hA (xw.getD 1 [])
      rw [Nat.eq_of_beq_eq_true hI] at hrg
      rwa [← hrg.eq (repN_elt hiso)]
    · obtain ⟨g, hg, hrg⟩ := wvP_rep hA (xw.getD 2 [])
      rw [Nat.eq_of_beq_eq_true hD] at hrg
      rwa [← hrg.eq (repN_elt hiso)]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have hWD : gensWD = gensT ++ [cTau, cIo, cGD] := rfl
  rw [hWD] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hTH (elt_mem_Hgen hc)
  · exact hmem c hc

theorem recW_append {WP TP : ℕ} {L₂ : List ℕ} {q r : ℕ} (h₂ : recW WP TP L₂ q r = true) :
    ∀ (L₁ : List ℕ) (p : ℕ), recW WP TP L₁ p q = true → recW WP TP (L₁ ++ L₂) p r = true
  | [], p, h => by
    have e : p = q := Nat.eq_of_beq_eq_true h
    subst e
    exact h₂
  | e :: L₁, p, h => by
    have h' : (Nat.blt (Nat.shiftRight e 7) 640 && Nat.blt (Nat.land e 127) 81 &&
        Nat.blt p (xW WP TP e) && recW WP TP L₁ (xW WP TP e) q) = true := h
    rw [Bool.and_eq_true] at h'
    have : (Nat.blt (Nat.shiftRight e 7) 640 && Nat.blt (Nat.land e 127) 81 &&
        Nat.blt p (xW WP TP e) && recW WP TP (L₁ ++ L₂) (xW WP TP e) r) = true := by
      rw [Bool.and_eq_true]
      exact ⟨h'.1, recW_append h₂ L₁ _ h'.2⟩
    exact this

theorem recW_sound {WP TP : ℕ} :
    ∀ (L : List ℕ) (p q : ℕ), recW WP TP L p q = true →
      (∀ e ∈ L, Nat.shiftRight e 7 < 640 ∧ Nat.land e 127 < 81 ∧ p < xW WP TP e) ∧
      (L.map (xW WP TP)).Pairwise (· < ·)
  | [], _, _, _ => ⟨by simp, List.Pairwise.nil⟩
  | e :: L, p, q, h => by
    have h' : (Nat.blt (Nat.shiftRight e 7) 640 && Nat.blt (Nat.land e 127) 81 &&
        Nat.blt p (xW WP TP e) && recW WP TP L (xW WP TP e) q) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨⟨hi, hj⟩, hp⟩, hL⟩ := h'
    obtain ⟨ih1, ih2⟩ := recW_sound L _ q hL
    refine ⟨?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨hi, hj, hp⟩
      · exact ⟨(ih1 e' he').1, (ih1 e' he').2.1, lt_trans hp (ih1 e' he').2.2⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih2⟩
      intro y hy
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
      exact (ih1 e' he').2.2

theorem chunks_walk {WP TP : ℕ} {CH : List (List ℕ)} {KB : List ℕ}
    (hc : ∀ c < CH.length, chunkK WP TP CH KB c = true) (hK : lk 0 KB 0 = 0) :
    ∀ n ≤ CH.length, recW WP TP (CH.take n).flatten 0 (lk 0 KB n) = true
  | 0, _ => by
    rw [hK]
    exact Nat.beq_refl 0
  | n + 1, hn => by
    have ih := chunks_walk hc hK n (by omega)
    have hcn := hc n (by omega)
    unfold chunkK at hcn
    rw [List.getD_eq_getElem _ _ (by omega)] at hcn
    rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.flatten_append, List.flatten_singleton]
    exact recW_append hcn _ _ ih

theorem mem_listing {TW : List (List ℕ)} {WP TP : ℕ} {RW : List (List ℕ × List ℕ × List (List ℕ))}
    {CH : List (List ℕ)} {KB : List ℕ} (hW : Nat.card (Hgen gensWD) = 51840)
    (ht : (TW.length == 81 && ttK (gensT.map numC) TP TW 0) = true)
    (hr : RW.length = 640)
    (hwl : ∀ i < 640, ∃ w ∈ Hgen gensWD, RepN w (laneP WP i))
    (hlen : (CH.map List.length).sum = 51840)
    (hc : ∀ c < CH.length, chunkK WP TP CH KB c = true) (hK : lk 0 KB 0 = 0)
    {w : H6} (hw : w ∈ Hgen gensWD) :
    ∃ e, Nat.shiftRight e 7 < 640 ∧ Nat.land e 127 < 81 ∧ RepN w (xW WP TP e) := by
  rw [Bool.and_eq_true, beq_iff_eq] at ht
  have htl : ∀ j < 81, ∃ s ∈ Hgen gensT, RepN s (laneP TP j) := by
    intro j hj
    have := ttK_sound TW 0 ht.2 j (by omega)
    rw [Nat.zero_add] at this
    rw [this]
    exact wvP_rep (gens_rep gensT_iso) _
  have hTW : Hgen gensT ≤ Hgen gensWD := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have hWD : gensWD = gensT ++ [cTau, cIo, cGD] := rfl
    rw [hWD]
    exact elt_mem_Hgen (List.mem_append_left _ hc)
  have hrec := chunks_walk hc hK CH.length le_rfl
  rw [List.take_length] at hrec
  obtain ⟨hall, hsort⟩ := recW_sound _ 0 _ hrec
  have hrep : ∀ e ∈ CH.flatten, ∃ g ∈ Hgen gensWD, RepN g (xW WP TP e) := by
    intro e he
    obtain ⟨hi, hj, -⟩ := hall e he
    obtain ⟨a, ha, hra⟩ := hwl _ hi
    obtain ⟨s, hs, hrs⟩ := htl _ hj
    exact ⟨a * s, mul_mem ha (hTW hs), hra.mul hrs⟩
  let L := CH.flatten.map fun e => eltN (xW WP TP e)
  have hLW : ∀ g ∈ L, g ∈ Hgen gensWD := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    obtain ⟨a, ha, hra⟩ := hrep e he
    rwa [(repN_eltN hra).eq hra]
  have hnd : L.Nodup := by
    rw [List.Nodup, List.pairwise_map]
    rw [List.pairwise_map] at hsort
    refine hsort.imp_of_mem ?_
    · intro e e' he he' hlt heq
      obtain ⟨a, -, hra⟩ := hrep e he
      obtain ⟨a', -, hra'⟩ := hrep e' he'
      have h1 := repN_eltN hra
      have h2 := repN_eltN hra'
      rw [heq] at h1
      exact absurd (h1.code_eq h2) (Nat.ne_of_lt hlt)
  have hLlen : L.length = 51840 := by
    rw [List.length_map, List.length_flatten, hlen]
  have hfin : (Hgen gensWD : Set H6).Finite := Set.toFinite _
  have hsub : (L.toFinset : Set H6) ⊆ (Hgen gensWD : Set H6) := by
    intro g hg
    exact hLW g (List.mem_toFinset.1 hg)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hLlen, ← hW]
    exact (Nat.card_coe_set_eq _).ge) hfin
  have hwL : w ∈ L := by
    have : w ∈ (L.toFinset : Set H6) := by
      rw [heq]
      exact hw
    exact List.mem_toFinset.1 this
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hwL
  obtain ⟨hi, hj, -⟩ := hall e he
  obtain ⟨a, -, hra⟩ := hrep e he
  exact ⟨e, hi, hj, repN_eltN hra⟩

theorem le_of_not_mem_W {TW QW : List (List ℕ)} {WP TP : ℕ}
    {RW : List (List ℕ × List ℕ × List (List ℕ))} {CH : List (List ℕ)} {KB : List ℕ}
    (hW : Nat.card (Hgen gensWD) = 51840) (hdc : dcCosetsCheck = true)
    (hq : (Nat.beq (mulP (numC cG1) (numC cG1)) oneP && qwK (gensT.map numC) (numC cG1) QW) = true)
    (ht : (TW.length == 81 && ttK (gensT.map numC) TP TW 0) = true)
    (hr : (RW.length == 640 && rowsK (gensT.map numC) (gensWD.map numC)
      (gensT.map fun c => numC (mulC c c)) (numC cG1) (numC cTau) (numC cIo) (numC cGD) WP RW 0) =
      true)
    (hlen : (CH.length == 160 && KB.length == 161 && (CH.map List.length).sum == 51840) = true)
    (hc : ∀ c < 160, chunkK WP TP CH KB c = true) (hK : lk 0 KB 0 = 0)
    {g : H6} (hg : g ∉ Hgen gensWD) : Hgen gensWD ≤ Hgen gensT ⊔ Subgroup.zpowers g := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hr hlen
  have h11 : elt cG1 * elt cG1 = 1 := by
    rw [Bool.and_eq_true] at hq
    have hr1 := repN_elt (c := cG1) (by decide)
    have := hr1.mul hr1
    rw [Nat.eq_of_beq_eq_true hq.1] at this
    exact this.eq RepN.one
  have hrow : ∀ i < 640, ∃ w ∈ Hgen gensWD, RepN w (laneP WP i) ∧
      Hgen gensWD ≤ Hgen gensT ⊔ Subgroup.zpowers (elt cG1 * w) := by
    intro i hi
    obtain ⟨r, -, hb⟩ := rowsK_sound RW 0 hr.2 i (by omega)
    rw [Nat.zero_add] at hb
    exact row_facts h11 rfl rfl hb
  obtain ⟨t, ht0, w, hw, rfl⟩ := exists_T0_g1_W hW hdc hq hg
  obtain ⟨e, hi, hj, hre⟩ := mem_listing hW ht hr.1
    (fun i hi => (hrow i hi).imp fun w h => ⟨h.1, h.2.1⟩) hlen.2
    (fun c hc' => hc c (by omega)) hK hw
  obtain ⟨wi, hwi, hrwi, hle⟩ := hrow _ hi
  rw [Bool.and_eq_true, beq_iff_eq] at ht
  have hs := ttK_sound TW 0 ht.2 (Nat.land e 127) (by omega)
  rw [Nat.zero_add] at hs
  obtain ⟨s, hs0, hrs⟩ := wvP_rep (gens_rep gensT_iso) (TW.getD (Nat.land e 127) [])
  rw [← hs] at hrs
  have hws : w = wi * s := hre.eq (hrwi.mul hrs)
  let H := Hgen gensT ⊔ Subgroup.zpowers (t * elt cG1 * w)
  have hy : elt cG1 * wi ∈ H := by
    have e1 : elt cG1 * wi = t⁻¹ * (t * elt cG1 * w) * s⁻¹ := by rw [hws]; group
    rw [e1]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem ht0))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_left (inv_mem hs0))
  exact hle.trans (sup_le le_sup_left ((Subgroup.zpowers_le).2 hy))

end CFSG.KC.Sp62Syl
