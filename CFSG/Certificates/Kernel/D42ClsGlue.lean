module

public import CFSG.Certificates.Kernel.D42ClsLane
public import CFSG.Certificates.Kernel.D42ClsSound

public section

namespace CFSG.KC.D42Cls

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D4PlaneP Finset

@[expose] def pk (g : trialityGroup8) : Nat :=
  packA (ofMat ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8))

@[expose] def wE (w : List Nat) : trialityGroup8 := ⟨wordGL w, wordGL_mem w⟩

theorem ofMat_mul (M M' : Matrix (Fin 8) (Fin 8) GF8) :
    ofMat (M * M') = mulArr (ofMat M) (ofMat M') :=
  eq_of_toMat_eq (size_ofMat _) (size_mulArr _ _)
    (by rw [toMat_mulArr, toMat_ofMat, toMat_ofMat, toMat_ofMat])

theorem pk_mul (g h : trialityGroup8) : pk (g * h) = mulP (pk g) (pk h) := by
  unfold pk
  rw [Subgroup.coe_mul, Units.val_mul, ofMat_mul, packA_mulArr]

theorem pk_one : pk 1 = oneP := by
  unfold pk
  rw [Subgroup.coe_one, Units.val_one, ← packA_oneArr]
  rfl

theorem pk_inj : Function.Injective pk := by
  intro g h e
  have := packA_inj (size_ofMat _) (size_ofMat _) e
  apply Subtype.ext
  apply Units.ext
  rw [← toMat_ofMat ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8), this, toMat_ofMat]

theorem ofMat_wordGL (w : List Nat) :
    ofMat ((wordGL w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = wordArr w :=
  eq_of_toMat_eq (size_ofMat _) (size_wordArr w) (by rw [toMat_ofMat, coe_wordGL])

theorem pk_wE {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0) (w : List Nat) :
    pk (wE w) = wordP ls w := by
  unfold pk
  change packA (ofMat ((wordGL w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8)) = _
  rw [ofMat_wordGL, packA_wordArr hL]

theorem wordGL_mul_reverse (w : List Nat) : wordGL w * wordGL w.reverse = 1 := by
  have hl : ∀ l, letterGL l * letterGL l = 1 := fun l => Units.ext (letterMat_mul_self l)
  induction w with
  | nil => simp [wordGL]
  | cons l w ih =>
    have h1 : wordGL (l :: w) = letterGL l * wordGL w := by simp [wordGL]
    have h2 : wordGL (l :: w).reverse = wordGL w.reverse * letterGL l := by
      simp [wordGL, List.reverse_cons]
    rw [h1, h2, mul_assoc, ← mul_assoc (wordGL w), ih, one_mul, hl]

theorem wE_reverse (w : List Nat) : wE w.reverse = (wE w)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right (Subtype.ext ?_)).symm
  change wordGL w * wordGL w.reverse = (1 : GL (Fin 8) GF8)
  exact wordGL_mul_reverse w

theorem ofNat'_toNat' (a : GF8) : GF8.ofNat' a.toNat = a := by
  obtain ⟨⟨v, hv⟩⟩ := a
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hv]

theorem exists_letter_of_mem_gens {M : Matrix (Fin 8) (Fin 8) GF8}
    (hM : M ∈ trialityGens8) : ∃ j < 18, M = letterMat j := by
  rcases hM with ⟨a, s, rfl⟩ | ⟨s, rfl⟩
  · have ha : a.toNat < 8 := a.val.isLt
    cases s
    · refine ⟨8 + a.toNat, by omega, ?_⟩
      have h1 : ¬ (8 + a.toNat < 8) := by omega
      have h2 : 8 + a.toNat < 16 := by omega
      rw [letterMat, if_neg h1, if_pos h2, Nat.add_sub_cancel_left, ofNat'_toNat']
    · refine ⟨a.toNat, by omega, ?_⟩
      rw [letterMat, if_pos ha, ofNat'_toNat']
  · cases s
    · exact ⟨17, by norm_num, by simp [letterMat]⟩
    · exact ⟨16, by norm_num, by simp [letterMat]⟩

theorem exists_mem_of_mem_closure {G : Type*} [Group G] {K : Subgroup G} (H : Subgroup K)
    {S : Set G} (hS : ∀ A ∈ S, ∃ hA : A ∈ K, (⟨A, hA⟩ : K) ∈ H) :
    ∀ g ∈ Subgroup.closure S, ∃ hg : g ∈ K, (⟨g, hg⟩ : K) ∈ H := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem A hA => exact hS A hA
  | one => exact ⟨one_mem _, one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨hx', hxH⟩ := ihx
    obtain ⟨hy', hyH⟩ := ihy
    exact ⟨mul_mem hx' hy', mul_mem hxH hyH⟩
  | inv x hx ih =>
    obtain ⟨hx', hxH⟩ := ih
    exact ⟨inv_mem hx', inv_mem hxH⟩

theorem eq_top_of_letters (H : Subgroup trialityGroup8)
    (hl : ∀ j < 18, (⟨letterGL j, letterGL_mem j⟩ : trialityGroup8) ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  refine (exists_mem_of_mem_closure H (S := {A : GL (Fin 8) GF8 |
    (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8}) (fun A hA => ?_) g hg).2
  obtain ⟨j, hj, hjA⟩ := exists_letter_of_mem_gens hA
  have : A = letterGL j := Units.ext hjA
  subst this
  exact ⟨letterGL_mem j, hl j hj⟩

theorem evalW_mem (H : Subgroup trialityGroup8) (sym : List Nat)
    (hs : ∀ s ∈ sym, ∃ h ∈ H, pk h = s) :
    ∀ w : List Nat, (∀ e ∈ w, e < sym.length) → ∃ h ∈ H, pk h = evalW sym w
  | [], _ => ⟨1, H.one_mem, pk_one⟩
  | e :: w, hw => by
    obtain ⟨a, ha, hpa⟩ := evalW_mem H sym hs w (fun e he => hw e (List.mem_cons_of_mem _ he))
    have he : e < sym.length := hw e List.mem_cons_self
    obtain ⟨b, hb, hpb⟩ := hs (sym.getD e oneP) (by
      rw [List.getD_eq_getElem _ _ he]
      exact List.getElem_mem he)
    refine ⟨b * a, H.mul_mem hb ha, ?_⟩
    rw [pk_mul, hpa, hpb]
    rfl

theorem eq_top_of_xyOK {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)
    {gxW gyW : List Nat} {ws : List (List Nat)}
    (h : xyOK ls (wordP ls gxW) (wordP ls gyW) (wordP ls gxW.reverse) (wordP ls gyW.reverse) ws =
      true)
    (H : Subgroup trialityGroup8) (hx : wE gxW ∈ H) (hy : wE gyW ∈ H) : H = ⊤ := by
  unfold xyOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hlen⟩, hw⟩ := h
  refine eq_top_of_letters H fun j hj => ?_
  have hj' : j < ws.length := by omega
  have hmem : (j, ws[j]'hj') ∈ (List.range 18).zip ws := by
    have hl : j < ((List.range 18).zip ws).length := by simp [hlen]; omega
    have := List.getElem_mem hl
    simpa [List.getElem_zip] using this
  obtain ⟨hlt, hev⟩ := hw _ hmem
  have hsym : ∀ s ∈ [wordP ls gxW, wordP ls gyW, wordP ls gxW.reverse, wordP ls gyW.reverse],
      ∃ h ∈ H, pk h = s := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_, hx, pk_wE hL gxW⟩
    · exact ⟨_, hy, pk_wE hL gyW⟩
    · exact ⟨_, by rw [wE_reverse]; exact H.inv_mem hx, pk_wE hL _⟩
    · exact ⟨_, by rw [wE_reverse]; exact H.inv_mem hy, pk_wE hL _⟩
  obtain ⟨g, hg, hpg⟩ := evalW_mem H _ hsym _ (fun e he => by simpa using hlt e he)
  have : g = ⟨letterGL j, letterGL_mem j⟩ := by
    apply pk_inj
    rw [hpg, hev, ← packA_letterArr hL j]
    rfl
  rw [← this]
  exact hg

theorem strictL_lt : ∀ (l : List Nat), strictL l = true → ∀ i j, i < j → j < l.length →
    l.getD i 0 < l.getD j 0
  | [], _, i, j, _, hj => by simp at hj
  | [a], _, i, j, hij, hj => by simp at hj; omega
  | a :: b :: l, h, i, j, hij, hj => by
    simp only [strictL, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictL_lt (b :: l) h.2
    rcases i with _ | i
    · rcases j with _ | _ | j
      · omega
      · simpa using h.1
      · have := ih 0 (j + 1) (by omega) (by simp at hj ⊢; omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at this ⊢
        omega
    · rcases j with _ | j
      · omega
      · have := ih i j (by omega) (by simp at hj ⊢; omega)
        simpa only [List.getD_cons_succ] using this

theorem all_of_chunks {α : Type} (p : α → Bool) (l : List α) (M : Nat)
    (h : ∀ j < M, ((l.drop (16 * j)).take 16).all p = true) (hl : l.length ≤ 16 * M) :
    ∀ i < l.length, ∀ d : α, p (l.getD i d) = true := by
  intro i hi d
  have hc := List.all_eq_true.mp (h (i / 16) (by omega))
  apply hc
  have h1 : i % 16 < ((l.drop (16 * (i / 16))).take 16).length := by simp; omega
  have := List.getElem_mem h1
  simp only [List.getElem_take, List.getElem_drop] at this
  have e : 16 * (i / 16) + i % 16 = i := by omega
  rw [List.getD_eq_getElem _ _ hi]
  simpa only [e] using this

theorem sum_map_eq_range {α : Type} (f : α → Nat) (d : α) : ∀ l : List α,
    (l.map f).sum = ∑ j ∈ range l.length, f (l.getD j d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, sum_range_succ', sum_map_eq_range f d l]
    simp [add_comm]

@[expose] def entArr (y : Nat) : Array GF8 := Array.ofFn (n := 64) fun t => GF8.ofNat' (entP y t)

theorem getD_entArr (y : Nat) {t : Nat} (ht : t < 64) :
    (entArr y).getD t 0 = GF8.ofNat' (entP y t) := getD_ofFn _ _ ht

theorem size_entArr (y : Nat) : (entArr y).size = 64 := by simp [entArr]

theorem bitsE_testBit (b0 b1 b2 : Bool) : (bitsE b0 b1 b2).toNat.testBit 0 = b0 ∧
    (bitsE b0 b1 b2).toNat.testBit 1 = b1 ∧ (bitsE b0 b1 b2).toNat.testBit 2 = b2 := by
  revert b0 b1 b2
  decide

theorem packA_entArr {y : Nat} (hy : y < 2 ^ 192) : packA (entArr y) = y := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_packA, getD_entArr _ (Nat.mod_lt _ (by decide)), ofNat'_entP]
  by_cases hn : n < 192
  · obtain ⟨t, a, ht, ha, rfl⟩ : ∃ t a, t < 64 ∧ a < 3 ∧ n = t + 64 * a :=
      ⟨n % 64, n / 64, by omega, by omega, by omega⟩
    have e1 : (t + 64 * a) % 64 = t := by omega
    have e2 : (t + 64 * a) / 64 = a := by omega
    rw [e1, e2]
    have hb := bitsE_testBit (y.testBit t) (y.testBit (64 + t)) (y.testBit (128 + t))
    interval_cases a
    · rw [hb.1, Nat.mul_zero, Nat.add_zero]
    · rw [hb.2.1]
      try (congr 1; omega)
    · rw [hb.2.2]
      try (congr 1; omega)
  · rw [CFSG.KC.D4PlaneP.testBit_toNat_hi _ _ (by omega),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem fldT_lt (T : List Nat) (c : Nat) : fldT T c < 2 ^ 192 :=
  Nat.and_lt_two_pow _ (by unfold m192; norm_num)

@[expose] def idxC (e : Nat) : Nat := 8 * (e % 8) + e / 8

theorem getD_colsP (x : Nat) {e : Nat} (he : e < 16) : (colsP x).getD e 0 = entP x (idxC e) := by
  unfold colsP idxC
  by_cases h8 : e < 8
  · rw [List.getD_append _ _ _ _ (by simpa using h8), getD_map_range _ _ h8,
      Nat.mod_eq_of_lt h8, Nat.div_eq_of_lt h8, Nat.add_zero]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_range,
      getD_map_range _ _ (by omega : e - 8 < 8)]
    congr 1
    omega

theorem length_colsP (x : Nat) : (colsP x).length = 16 := by simp [colsP]

theorem length_fBoth (CR : List (List N3)) (W1 W2 : List N3) (R : List (List Nat))
    (h : CR.length = 8) : (fBoth CR W1 W2 R).length = 16 := by
  simp [fBoth, fLanes, cLanes, h]

theorem lane_conj {T TW : List Nat} {CR : List (List N3)} {W1 W2 : List N3} {Vm : Nat}
    (hcr : ∀ i < 8, crOK T CR i = true) (hw1 : wOK TW W1 0 = true) (hw2 : wOK TW W2 1 = true)
    (hCR : CR.length = 8) {c : Nat} (hc : c < 64 * T.length) (hc' : c < 64 * TW.length)
    (y ρ : trialityGroup8) (hy : pk y = fldT T c) (hV : mulP (fldT T c) (fldT TW c) = Vm)
    {e : Nat} (he : e < 16) :
    laneE ((fBoth CR W1 W2 (rowsP (pk ρ))).getD e (0, 0, 0)) (64 + c) =
      GF8.ofNat' (entP (mulP (pk (y * ρ * y⁻¹)) Vm) (idxC e)) := by
  set A := ofMat ((y : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) with hAdef
  set B := entArr (fldT TW c) with hBdef
  set R := ofMat ((ρ : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) with hRdef
  have hA : packA A = fldT T c := hy
  have hB : packA B = fldT TW c := packA_entArr (fldT_lt _ _)
  have hVm : packA (mulArr A B) = Vm := by rw [packA_mulArr, hA, hB, hV]
  have hCRs := crOK_spec hcr
  obtain ⟨hW1l, hW1e⟩ := wOK_spec hw1 (by decide)
  obtain ⟨hW2l, hW2e⟩ := wOK_spec hw2 (by decide)
  have hCRe : ∀ i < 8, ∀ j < 8,
      laneE ((CR.getD i []).getD j (0, 0, 0)) (64 + c) = A.getD (8 * i + j) 0 := by
    intro i hi j hj
    rw [(hCRs i hi).2 c hc j hj, ← hA, ofNat'_entP_packA _ (by omega)]
  have hWe : ∀ (W : List N3) (col : Nat), col < 8 →
      (∀ l < 8, laneE (W.getD l (0, 0, 0)) (64 + c) = GF8.ofNat' (entP (fldT TW c) (8 * l + col))) →
      ∀ l < 8, laneE (W.getD l (0, 0, 0)) (64 + c) = B.getD (8 * l + col) 0 := by
    intro W col hcol hW l hl
    rw [hW l hl, getD_entArr _ (by omega)]
  have hmat : mulArr A (mulArr R B) =
      mulArr (ofMat ((y * ρ * y⁻¹ : trialityGroup8) : GL (Fin 8) GF8).val) (mulArr A B) := by
    apply eq_of_toMat_eq (size_mulArr _ _) (size_mulArr _ _)
    have hinv : ((y⁻¹ : trialityGroup8) : GL (Fin 8) GF8).val *
        ((y : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    simp only [hAdef, toMat_mulArr, toMat_ofMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ ((y : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8), hinv,
      Matrix.one_mul, hRdef, toMat_ofMat]
  have hrhs : ∀ t < 64, GF8.ofNat' (entP (mulP (pk (y * ρ * y⁻¹)) Vm) t) =
      (mulArr A (mulArr R B)).getD t 0 := by
    intro t ht
    rw [hmat, ← hVm]
    unfold pk
    rw [← packA_mulArr, ofNat'_entP_packA _ ht]
  have hidx : idxC e < 64 := by unfold idxC; omega
  rw [hrhs _ hidx]
  have hpkρ : pk ρ = packA R := rfl
  rw [hpkρ]
  unfold fBoth
  have hlen1 : (fLanes CR W1 (rowsP (packA R))).length = 8 := by simp [fLanes, cLanes, hCR]
  by_cases h8 : e < 8
  · rw [List.getD_append _ _ _ _ (by omega),
      laneE_fLanes A R B CR W1 0 (64 + c) hCR (fun i hi => (hCRs i hi).1) hCRe hW1l
        (hWe W1 0 (by decide) (fun l hl => hW1e c hc' l hl)) (by decide) h8]
    unfold idxC
    rw [Nat.mod_eq_of_lt h8, Nat.div_eq_of_lt h8]
  · rw [List.getD_append_right _ _ _ _ (by omega), hlen1,
      laneE_fLanes A R B CR W2 1 (64 + c) hCR (fun i hi => (hCRs i hi).1) hCRe hW2l
        (hWe W2 1 (by decide) (fun l hl => hW2e c hc' l hl)) (by decide) (by omega : e - 8 < 8)]
    unfold idxC
    congr 1
    omega

theorem key_eq_of_conj {G : Type*} [Group G] (C : Set G) (hmul : ∀ a ∈ C, ∀ b ∈ C, a * b ∈ C)
    (hinv : ∀ a ∈ C, a⁻¹ ∈ C) (κ : G → Nat) (ri rj : G) (ki kj : Nat)
    (hi : ∃ a ∈ C, κ (a * ri * a⁻¹) = ki) (hi' : ∀ a ∈ C, ki ≤ κ (a * ri * a⁻¹))
    (hj : ∃ a ∈ C, κ (a * rj * a⁻¹) = kj) (hj' : ∀ a ∈ C, kj ≤ κ (a * rj * a⁻¹))
    (c c' : G) (hc : c ∈ C) (hc' : c' ∈ C) (h : c * ri * c⁻¹ = c' * rj * c'⁻¹) : ki = kj := by
  obtain ⟨a, ha, hak⟩ := hj
  obtain ⟨b, hb, hbk⟩ := hi
  have e1 : (a * c'⁻¹ * c) * ri * (a * c'⁻¹ * c)⁻¹ = a * rj * a⁻¹ := by
    calc (a * c'⁻¹ * c) * ri * (a * c'⁻¹ * c)⁻¹ = a * c'⁻¹ * (c * ri * c⁻¹) * c' * a⁻¹ := by group
      _ = a * c'⁻¹ * (c' * rj * c'⁻¹) * c' * a⁻¹ := by rw [h]
      _ = a * rj * a⁻¹ := by group
  have e2 : (b * c⁻¹ * c') * rj * (b * c⁻¹ * c')⁻¹ = b * ri * b⁻¹ := by
    calc (b * c⁻¹ * c') * rj * (b * c⁻¹ * c')⁻¹ = b * c⁻¹ * (c' * rj * c'⁻¹) * c * b⁻¹ := by group
      _ = b * c⁻¹ * (c * ri * c⁻¹) * c * b⁻¹ := by rw [h]
      _ = b * ri * b⁻¹ := by group
  have h1 := hi' _ (hmul _ (hmul _ ha _ (hinv _ hc')) _ hc)
  have h2 := hj' _ (hmul _ (hmul _ hb _ (hinv _ hc)) _ hc')
  rw [e1, hak] at h1
  rw [e2, hbk] at h2
  omega

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (d : α) (d' : β) {i : Nat}
    (hi : i < l.length) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem class_spec {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)
    {N n : Nat} {T TW : List Nat} {DP Vm : Nat} {sW : List (List Nat)} {kW : List Nat}
    {rows : List (List (Nat × Nat × Nat × List Nat))} {CR : List (List N3)} {W1 W2 : List N3}
    {roots : List (List Nat × List Nat × Nat × List Nat × List Nat)} {gxW gyW : List Nat}
    {m M : Nat} (hN : N ≤ 64 * m) (hT : m ≤ T.length) (hTW : m ≤ TW.length) (hCR : CR.length = 8)
    (hM : roots.length ≤ 16 * M)
    (hrows : ∀ j < m, rowsOK N T TW DP Vm (sW.map (wordP ls)) rows j = true)
    (hcr : ∀ i < 8, crOK T CR i = true) (hw1 : wOK TW W1 0 = true) (hw2 : wOK TW W2 1 = true)
    (hroots : ∀ j < M, rootsOK ls (wordP ls kW) Vm N (wordP ls gxW) (wordP ls gyW)
      (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2 roots j = true)
    (hcls : classOK (wordP ls kW) n N (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse)
      roots = true)
    (hxy : ∀ H : Subgroup trialityGroup8, wE gxW ∈ H → wE gyW ∈ H → H = ⊤)
    (hG : Nat.card trialityGroup8 = n * N) :
    (Subgroup.centralizer {wE kW}).index = n ∧
    ∀ H : Subgroup trialityGroup8, Subgroup.centralizer {wE kW} ≤ H →
      (∀ h ∈ H, h * wE kW * h⁻¹ = wE kW ∨ h * wE kW * h⁻¹ = wE kW * wE kW) ∨ H = ⊤ := by
  classical
  have hfin : Fintype trialityGroup8 := Fintype.ofFinite _
  set k := wE kW with hkdef
  set S := sW.map (wordP ls) with hSdef
  have hpk : pk k = wordP ls kW := pk_wE hL kW
  have hSl : S.length = sW.length := by simp [S]
  have hS : ∀ g < S.length, pk (wE (sW.getD g [])) = S.getD g oneP := by
    intro g hg
    rw [pk_wE hL, hSdef, getD_map_lt _ _ [] oneP (by simpa [hSl] using hg)]
  have hR := rowsOK_spec hrows hN
  have hex : ∀ c < N, ∃ y : trialityGroup8, pk y = fldT T c := by
    have : ∀ d, ∀ c < N, byteD DP c ≤ d → ∃ y : trialityGroup8, pk y = fldT T c := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro c hc hd
        by_cases h0 : byteD DP c = 0
        · exact ⟨1, by rw [pk_one, (hR c hc).2.1 h0]⟩
        · obtain ⟨q, hq, g, hg, hqd, hqe⟩ := (hR c hc).2.2.1 h0
          obtain ⟨y, hy⟩ := ih (byteD DP q) (by omega) q hq le_rfl
          exact ⟨y * wE (sW.getD g []), by rw [pk_mul, hy, hS g hg, hqe]⟩
    exact fun c hc => this _ c hc le_rfl
  choose! x hx using hex
  have hind : ∀ Q : trialityGroup8 → Prop, Q 1 →
      (∀ y, Q y → ∀ g < S.length, Q (y * wE (sW.getD g []))) → ∀ c < N, Q (x c) := by
    intro Q h1 hs
    have : ∀ d, ∀ c < N, byteD DP c ≤ d → Q (x c) := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro c hc hd
        by_cases h0 : byteD DP c = 0
        · have e : x c = 1 := pk_inj (by rw [hx c hc, pk_one, (hR c hc).2.1 h0])
          rw [e]
          exact h1
        · obtain ⟨q, hq, g, hg, hqd, hqe⟩ := (hR c hc).2.2.1 h0
          have e : x c = x q * wE (sW.getD g []) :=
            pk_inj (by rw [hx c hc, pk_mul, hx q hq, hS g hg, hqe])
          rw [e]
          exact hs _ (ih (byteD DP q) (by omega) q hq le_rfl) g hg
    exact fun c hc => this _ c hc le_rfl
  have hmono : ∀ a b, a < b → b < N → fldT T a < fldT T b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
      · exact lt_trans (ih h (by omega)) ((hR b (by omega)).1 hb)
      · subst h
        exact (hR a (by omega)).1 hb
  have hxinj : ∀ a < N, ∀ b < N, x a = x b → a = b := by
    intro a ha b hb e
    have e' := congrArg pk e
    rw [hx a ha, hx b hb] at e'
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e' (ne_of_lt (hmono a b h hb))
    · exact h
    · exact absurd e'.symm (ne_of_lt (hmono b a h ha))
  set C : Finset trialityGroup8 := (range N).image x with hCdef
  have hmemC : ∀ y, y ∈ C ↔ ∃ c < N, x c = y := by
    intro y
    simp [C]
  have hcardC : C.card = N := by
    rw [card_image_of_injOn, card_range]
    intro a ha b hb e
    exact hxinj a (by simpa using ha) b (by simpa using hb) e
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.mul_zero] at hG
      exact absurd hG Nat.card_pos.ne'
    · exact h
  have hgen : ∀ y ∈ C, ∀ g < S.length, y * wE (sW.getD g []) ∈ C := by
    intro y hy g hg
    obtain ⟨c, hc, rfl⟩ := (hmemC y).1 hy
    obtain ⟨c', hc', he⟩ := (hR c hc).2.2.2.2 g hg
    refine (hmemC _).2 ⟨c', hc', pk_inj ?_⟩
    rw [hx c' hc', pk_mul, hx c hc, hS g hg, he]
  have hmul : ∀ a ∈ C, ∀ b ∈ C, a * b ∈ C := by
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := (hmemC b).1 hb
    refine hind (fun y => a * y ∈ C) (by simpa using ha) (fun y hy g hg => ?_) c hc
    rw [← mul_assoc]
    exact hgen _ hy g hg
  have hpow : ∀ a ∈ C, ∀ j, a ^ (j + 1) ∈ C := by
    intro a ha j
    induction j with
    | zero => simpa using ha
    | succ j ih =>
      rw [pow_succ]
      exact hmul _ ih a ha
  have hinv : ∀ a ∈ C, a⁻¹ ∈ C := by
    intro a ha
    have ho := orderOf_pos a
    have e : a⁻¹ = a ^ (2 * orderOf a - 2 + 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        (by omega : 2 * orderOf a - 2 + 1 + 1 = orderOf a * 2), pow_mul, pow_orderOf_eq_one,
        one_pow]
    rw [e]
    exact hpow a ha _
  have hCinv : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b ∈ C := fun a ha b hb => hmul _ (hinv a ha) b hb
  have hx0 : x 0 ∈ C := (hmemC _).2 ⟨0, hNpos, rfl⟩
  have h1C : (1 : trialityGroup8) ∈ C := by
    have := hCinv _ hx0 _ hx0
    rwa [inv_mul_cancel] at this
  unfold classOK at hcls
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcls
  obtain ⟨⟨⟨⟨⟨⟨hS3, -⟩, hcomm⟩, -⟩, hkeys⟩, hsum⟩, -⟩ := hcls
  have hkS : ∀ g < S.length, wE (sW.getD g []) * k = k * wE (sW.getD g []) := by
    intro g hg
    have := hcomm (S.getD g oneP) (by rw [List.getD_eq_getElem _ _ hg]; exact List.getElem_mem hg)
    unfold commP at this
    apply pk_inj
    rw [pk_mul, pk_mul, hpk, hS g hg]
    exact (beq_iff_eq.mp this).symm
  have hk : ∀ c ∈ C, c * k = k * c := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (hmemC y).1 hy
    refine hind (fun y => y * k = k * y) (by simp) (fun y hy g hg => ?_) c hc
    calc y * wE (sW.getD g []) * k = y * (wE (sW.getD g []) * k) := by group
      _ = y * k * wE (sW.getD g []) := by rw [hkS g hg]; group
      _ = k * (y * wE (sW.getD g [])) := by rw [hy]; group
  set dflt : List Nat × List Nat × Nat × List Nat × List Nat := ([], [], 0, [], [])
  set rt : ℕ → List Nat × List Nat × Nat × List Nat × List Nat := fun j => roots.getD j dflt
  set d : ℕ → trialityGroup8 := fun j => wE (rt j).1 with hddef
  have hroot : ∀ j < roots.length, rootK ls (wordP ls kW) Vm N (((1 <<< N) - 1) <<< 64)
      (wordP ls gxW) (wordP ls gyW) S (sW.map fun w => wordP ls w.reverse) CR W1 W2 (rt j) =
      true :=
    fun j hj => all_of_chunks _ roots M hroots hM j hj dflt
  have hpr : ∀ j, pk (d j * k * (d j)⁻¹) =
      mulP (mulP (wordP ls (rt j).1) (wordP ls kW)) (wordP ls (rt j).1.reverse) := by
    intro j
    rw [pk_mul, pk_mul, hpk, ← wE_reverse, pk_wE hL, pk_wE hL]
  have hrj : ∀ j < roots.length,
      strictL (rt j).2.1 = true ∧ (∀ p ∈ (rt j).2.1, p < N) ∧
      sweepK (((1 <<< N) - 1) <<< 64) (rt j).2.1 (rt j).2.2.1
        (fBoth CR W1 W2 (rowsP (pk (d j * k * (d j)⁻¹))))
        (colsP (mulP (pk (d j * k * (d j)⁻¹)) Vm)) = true ∧
      (pk (d j * k * (d j)⁻¹) = pk k ∨ pk (d j * k * (d j)⁻¹) = mulP (pk k) (pk k) ∨
        ((∀ e ∈ (rt j).2.2.2.1, e < 8) ∧ (∀ e ∈ (rt j).2.2.2.2, e < 8) ∧
          evalW (S ++ [wordP ls (rt j).1] ++ (sW.map fun w => wordP ls w.reverse) ++
            [wordP ls (rt j).1.reverse]) (rt j).2.2.2.1 = wordP ls gxW ∧
          evalW (S ++ [wordP ls (rt j).1] ++ (sW.map fun w => wordP ls w.reverse) ++
            [wordP ls (rt j).1.reverse]) (rt j).2.2.2.2 = wordP ls gyW)) := by
    intro j hj
    have h := hroot j hj
    unfold rootK rootD rootR at h
    rw [← hpr j, ← hpk] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with (h4 | h4) | ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
    · exact Or.inl h4
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr ⟨ha, hb, hc, hd⟩)
  have hT64 : ∀ c < N, c < 64 * T.length := fun c hc => by omega
  have hTW64 : ∀ c < N, c < 64 * TW.length := fun c hc => by omega
  have hlane : ∀ ρ : trialityGroup8, ∀ c < N, ∀ e < 16,
      laneE ((fBoth CR W1 W2 (rowsP (pk ρ))).getD e (0, 0, 0)) (64 + c) =
        GF8.ofNat' (entP (mulP (pk (x c * ρ * (x c)⁻¹)) Vm) (idxC e)) :=
    fun ρ c hc e he => lane_conj hcr hw1 hw2 hCR (hT64 c hc) (hTW64 c hc) (x c) ρ (hx c hc)
      (hR c hc).2.2.2.1 he
  set κ : trialityGroup8 → Nat := fun z =>
    ((List.range 16).map fun e => (GF8.ofNat' (entP (mulP (pk z) Vm) (idxC e))).toNat).foldl
      (fun acc v => 8 * acc + v) 0 with hκ
  have hkey : ∀ ρ : trialityGroup8, ∀ c < N,
      keyV (fBoth CR W1 W2 (rowsP (pk ρ))) (64 + c) = κ (x c * ρ * (x c)⁻¹) := by
    intro ρ c hc
    unfold keyV
    rw [hκ]
    dsimp only
    rw [← List.foldl_map (f := fun a => (laneE a (64 + c)).toNat) (g := fun acc v => 8 * acc + v)]
    congr 1
    apply List.ext_getElem
    · simp [length_fBoth _ _ _ _ hCR]
    · intro e h1 h2
      have he : e < 16 := by simpa using h2
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      rw [← hlane ρ c hc e he, List.getD_eq_getElem _ _ (by rw [length_fBoth _ _ _ _ hCR]; omega)]
  set s : ℕ → ℕ := fun j => (rt j).2.1.length
  have hsw : ∀ j < roots.length, (∀ c < N, x c * (d j * k * (d j)⁻¹) * (x c)⁻¹ =
      d j * k * (d j)⁻¹ → c ∈ (rt j).2.1) ∧
      (∃ a ∈ (C : Set trialityGroup8), κ (a * (d j * k * (d j)⁻¹) * a⁻¹) = (rt j).2.2.1) ∧
      ∀ a ∈ (C : Set trialityGroup8), (rt j).2.2.1 ≤ κ (a * (d j * k * (d j)⁻¹) * a⁻¹) := by
    intro j hj
    obtain ⟨-, -, hsk, -⟩ := hrj j hj
    have hsp := sweepK_spec hsk (by rw [length_fBoth _ _ _ _ hCR, length_colsP])
    refine ⟨fun c hc hcom => hsp.1 c hc fun e he => ?_, ?_, ?_⟩
    · rw [length_fBoth _ _ _ _ hCR] at he
      rw [hlane _ c hc e he, hcom, getD_colsP _ he]
    · obtain ⟨c, hc, hck⟩ := (hsp.2 hNpos).1
      refine ⟨x c, (hmemC _).2 ⟨c, hc, rfl⟩, ?_⟩
      rw [← hkey _ c hc, hck]
    · intro a ha
      obtain ⟨c, hc, rfl⟩ := (hmemC a).1 ha
      rw [← hkey _ c hc]
      exact (hsp.2 hNpos).2 c hc
  have hstab : ∀ j ∈ range roots.length, (stabs C (d j * k * (d j)⁻¹)).card ≤ s j := by
    intro j hj
    have hj' : j < roots.length := mem_range.mp hj
    have hsub : stabs C (d j * k * (d j)⁻¹) ⊆ (rt j).2.1.toFinset.image x := by
      intro y hy
      rw [mem_stabs] at hy
      obtain ⟨c, hc, rfl⟩ := (hmemC _).1 hy.1
      exact mem_image.mpr ⟨c, List.mem_toFinset.mpr ((hsw j hj').1 c hc hy.2), rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (List.toFinset_card_le _))
  have hdisj : ∀ i ∈ range roots.length, ∀ j ∈ range roots.length, ∀ c ∈ C, ∀ c' ∈ C,
      c * (d i * k * (d i)⁻¹) * c⁻¹ = c' * (d j * k * (d j)⁻¹) * c'⁻¹ → i = j := by
    intro i hi j hj c hc c' hc' h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hke := key_eq_of_conj (C : Set trialityGroup8) hmul hinv κ _ _ _ _ (hsw i hi').2.1
      (hsw i hi').2.2 (hsw j hj').2.1 (hsw j hj').2.2 c c' hc hc' h
    have hlt := strictL_lt _ hkeys
    have hgi : (roots.map fun rt => rt.2.2.1).getD i 0 = (rt i).2.2.1 := getD_map_lt _ _ _ _ hi'
    have hgj : (roots.map fun rt => rt.2.2.1).getD j 0 = (rt j).2.2.1 := getD_map_lt _ _ _ _ hj'
    rcases lt_trichotomy i j with h' | h' | h'
    · have := hlt i j h' (by simpa using hj')
      rw [hgi, hgj] at this
      omega
    · exact h'
    · have := hlt j i h' (by simpa using hi')
      rw [hgi, hgj] at this
      omega
  have hsum' : n ≤ ∑ j ∈ range roots.length, C.card / s j := by
    rw [hcardC, ← hsum, sum_map_eq_range _ dflt]
  have hGC : Fintype.card trialityGroup8 = n * C.card := by
    rw [Fintype.card_eq_nat_card, hG, hcardC]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.zero_mul] at hG
      exact absurd hG Nat.card_pos.ne'
    · exact h
  have hcent := mem_of_commute_of_sweep k C hCinv hmul hk (range roots.length) d s n hstab hdisj
    hsum' hGC hn
  have hcov := exists_of_sweep k C hCinv hmul hk (range roots.length) d s n hstab hdisj hsum' hGC
    hn
  have hcentC : ∀ y, y ∈ Subgroup.centralizer {k} ↔ y ∈ C := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => hcent y h, fun h => hk y h⟩
  refine ⟨?_, fun H hH => ?_⟩
  · have hcard : Nat.card (Subgroup.centralizer {k}) = N := by
      rw [← hcardC, ← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight hcentC)
    have := (Subgroup.centralizer {k}).card_mul_index
    rw [hcard, hG] at this
    exact Nat.eq_of_mul_eq_mul_left hNpos (by rw [this, Nat.mul_comm])
  · have hHC : ∀ y, y * k = k * y → y ∈ H := fun y hy =>
      hH (Subgroup.mem_centralizer_singleton_iff.mpr hy)
    refine overgroup_of_sweep k C hk hcent (range roots.length) d hcov (fun j hj => ?_) H hHC
    have hj' := mem_range.mp hj
    obtain ⟨-, -, -, hw⟩ := hrj j hj'
    rcases hw with hw | hw | ⟨hx1, hy1, hgx, hgy⟩
    · exact Or.inl (pk_inj hw)
    · exact Or.inr (Or.inl (pk_inj (by rw [hw, pk_mul])))
    · refine Or.inr (Or.inr fun K hK hdK => ?_)
      have hSK : ∀ g < S.length, wE (sW.getD g []) ∈ K := fun g hg =>
        hK _ (by simpa using hgen 1 h1C g hg)
      have hsym : ∀ t ∈ S ++ [wordP ls (rt j).1] ++ (sW.map fun w => wordP ls w.reverse) ++
          [wordP ls (rt j).1.reverse], ∃ h ∈ K, pk h = t := by
        intro t ht
        rw [hSdef] at ht
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at ht
        rcases ht with ((⟨w, hw, rfl⟩ | rfl) | ⟨w, hw, rfl⟩) | rfl
        · obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hw
          refine ⟨wE sW[g], ?_, pk_wE hL _⟩
          have := hSK g (by rw [hSl]; exact hg)
          rwa [List.getD_eq_getElem _ _ hg] at this
        · exact ⟨d j, hdK, pk_wE hL _⟩
        · obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hw
          refine ⟨wE sW[g].reverse, ?_, pk_wE hL _⟩
          have := hSK g (by rw [hSl]; exact hg)
          rw [List.getD_eq_getElem _ _ hg] at this
          rw [wE_reverse]
          exact K.inv_mem this
        · exact ⟨(d j)⁻¹, K.inv_mem hdK, by rw [← wE_reverse, pk_wE hL]⟩
      have hlen : (S ++ [wordP ls (rt j).1] ++ (sW.map fun w => wordP ls w.reverse) ++
          [wordP ls (rt j).1.reverse]).length = 2 * sW.length + 2 := by
        simp [S]
        omega
      have hlt : ∀ w : List Nat, (∀ e ∈ w, e < 8) → ∀ e ∈ w, e < (S ++ [wordP ls (rt j).1] ++
          (sW.map fun w => wordP ls w.reverse) ++ [wordP ls (rt j).1.reverse]).length := by
        intro w hw e he
        rw [hlen, ← hSl, hS3]
        exact hw e he
      obtain ⟨a, ha, hpa⟩ := evalW_mem K _ hsym _ (hlt _ hx1)
      obtain ⟨b, hb, hpb⟩ := evalW_mem K _ hsym _ (hlt _ hy1)
      rw [hgx, ← pk_wE hL] at hpa
      rw [hgy, ← pk_wE hL] at hpb
      refine hxy K ?_ ?_
      · rw [← pk_inj hpa]
        exact ha
      · rw [← pk_inj hpb]
        exact hb

end CFSG.KC.D42Cls

end
