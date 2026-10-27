module

public import CFSG.Certificates.Kernel.TwD5ReflKMat

public section

namespace CFSG.KC.TwD5R

open scoped Matrix
open CFSG.StandardType.FrameRoute.FS81

theorem getN_eq (l : List ℕ) (i : ℕ) : getN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [getN]
  | cons x t ih =>
    cases i with
    | zero => simp [getN]
    | succ k =>
      rw [List.getD_cons_succ, ← ih k]
      rfl

theorem getN_mem_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : getN l i ∈ l :=
  getN_mem l i h

theorem exists_getN_of_mem {l : List ℕ} {q : ℕ} (h : q ∈ l) : ∃ i, i < l.length ∧ getN l i = q := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, e⟩ := ih h'
      exact ⟨i + 1, by simp; omega, e⟩

theorem applyL_eq (gens refls : List ℕ) (g x : ℕ) : applyL gens refls g x =
    if g < gens.length then act (getN gens g) x else reflV (getN refls (g - gens.length)) x := by
  change Bool.rec (motive := fun _ => ℕ) (reflV (getN refls (Nat.sub g (lenN gens))) x)
    (act (getN gens g) x) (Nat.blt g (lenN gens)) = _
  rw [lenN_eq]
  have e : Nat.blt g gens.length = decide (g < gens.length) :=
    Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])
  rw [e]
  by_cases hg : g < gens.length
  · rw [decide_eq_true hg, if_pos hg]
  · rw [decide_eq_false hg, if_neg hg]
    rfl

@[expose] noncomputable def letM (gens refls : List ℕ) (g : ℕ) :
    Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  if g < gens.length then hcMat (getN gens g) else reflK (getN refls (g - gens.length))

@[expose] noncomputable def wordM (gens refls : List ℕ) (w : List ℕ) :
    Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  (w.map (letM gens refls)).prod

theorem applyW_spec {fx : Bool} {gens refls : List ℕ} (hg : allL gens (validH fx) = true)
    (w : List ℕ) {x : ℕ} (hx : x < 729) :
    applyW gens refls w x < 729 ∧ decV (applyW gens refls w x) = wordM gens refls w *ᵥ decV x := by
  induction w with
  | nil =>
    refine ⟨hx, ?_⟩
    change decV x = wordM gens refls [] *ᵥ decV x
    simp [wordM]
  | cons g w ih =>
    obtain ⟨h1, h2⟩ := ih
    change applyL gens refls g (applyW gens refls w x) < 729 ∧
      decV (applyL gens refls g (applyW gens refls w x)) = _
    have hw : wordM gens refls (g :: w) = letM gens refls g * wordM gens refls w := by
      simp [wordM]
    rw [hw, ← Matrix.mulVec_mulVec, ← h2, applyL_eq]
    unfold letM
    by_cases hlt : g < gens.length
    · rw [if_pos hlt, if_pos hlt]
      exact act_spec (gens_sound hg _ (getN_mem_of_lt hlt)) _
    · rw [if_neg hlt, if_neg hlt]
      exact ⟨reflV_lt _ _, decV_reflV _ _⟩

theorem wordM_mem {fx : Bool} {gens refls : List ℕ} (hg : allL gens (validH fx) = true)
    {w : List ℕ} (hw : ∀ g ∈ w, g < gens.length + refls.length) :
    wordM gens refls w ∈ Submonoid.closure (HS fx ∪ {X | ∃ r ∈ refls, X = reflK r}) := by
  apply Submonoid.list_prod_mem
  intro M hM
  obtain ⟨g, hgw, rfl⟩ := List.mem_map.mp hM
  apply Submonoid.subset_closure
  unfold letM
  split_ifs with hlt
  · exact Or.inl (hcMat_mem (gens_sound hg _ (getN_mem_of_lt hlt)))
  · exact Or.inr ⟨_, getN_mem_of_lt (by have := hw g hgw; omega), rfl⟩

theorem badW_spec {fx : Bool} {gens refls : List ℕ} {nl : ℕ} {w : List ℕ}
    (hg : allL gens (validH fx) = true) (hnl : nl = gens.length + refls.length)
    (h : badW fx gens refls nl w = true) :
    ∃ M ∈ Submonoid.closure (HS fx ∪ {X | ∃ r ∈ refls, X = reflK r}),
      (∀ i : Fin 6, i ≠ 0 → M i 0 = 0) ∧ M ∉ HS fx := by
  unfold badW at h
  rw [andB_eq_true, andB_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlet : ∀ g ∈ w, g < gens.length + refls.length := by
    intro g hgw
    have := allL_eq_true.mp h1 g hgw
    rw [Nat.blt_eq, hnl] at this
    exact this
  refine ⟨wordM gens refls w, wordM_mem hg hlet, ?_, ?_⟩
  · intro i hi
    have hy : applyW gens refls w 1 < 3 := by
      rw [Nat.blt_eq] at h2
      exact h2
    obtain ⟨-, e⟩ := applyW_spec (refls := refls) hg w (x := 1) (by norm_num)
    have e1 : decV 1 = Pi.single 0 1 := decV_pow3 0
    have e2 := congrFun e i
    rw [e1, mulVec_single_one] at e2
    simp only at e2
    rw [← e2]
    have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have h3i : 3 ≤ 3 ^ i.val := Nat.le_self_pow hi' 3
    unfold decV
    rw [dg_eq, Nat.div_eq_of_lt (by omega), Nat.zero_mod, Nat.cast_zero]
  · intro hM
    have h3p : ∀ j, j < 6 → 3 ^ j < 729 := by
      intro j hj
      interval_cases j <;> norm_num
    have hcols : ∀ j, j < 6 → applyW gens refls w (Nat.pow 3 j) < 729 :=
      fun j hj => (applyW_spec hg w (h3p j hj)).1
    have e : colMat (fun j => applyW gens refls w (Nat.pow 3 j)) = wordM gens refls w := by
      ext i j
      change decV (applyW gens refls w (3 ^ j.val)) i = _
      rw [(applyW_spec hg w (h3p j.val j.isLt)).2, decV_pow3 j, mulVec_single_one]
    have h4 := (inHCols_iff hcols).mpr (by rw [e]; exact hM)
    rw [notB_eq_true] at h3
    change (inHCols fx fun j => applyW gens refls w (Nat.pow 3 j)) = false at h3
    rw [h3] at h4
    cases h4

theorem closure_conj {fx : Bool} {S : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    (hS : ∀ X ∈ S, ∀ g ∈ gensOf fx, ∃ Y ∈ S, hcMat g * X = Y * hcMat g)
    {A : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hA : A ∈ GS fx) : ∀ X ∈ S, ∃ Y ∈ S, A * X = Y * A := by
  induction hA using Submonoid.closure_induction with
  | mem A hA =>
    obtain ⟨g, hg, rfl⟩ := hA
    exact fun X hX => hS X hX g hg
  | one =>
    intro X hX
    exact ⟨X, hX, by rw [one_mul, mul_one]⟩
  | mul A B _ _ hA hB =>
    intro X hX
    obtain ⟨Y, hY, e1⟩ := hB X hX
    obtain ⟨Z, hZ, e2⟩ := hA Y hY
    exact ⟨Z, hZ, by rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc]⟩

theorem conj_back {h h' s R Y : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hh : h' * h = 1)
    (e : h * s = R * h) (e2 : h' * R = Y * h') : s = Y :=
  calc s = (h' * h) * s := by rw [hh, one_mul]
    _ = h' * (h * s) := mul_assoc _ _ _
    _ = h' * (R * h) := by rw [e]
    _ = (h' * R) * h := (mul_assoc _ _ _).symm
    _ = (Y * h') * h := by rw [e2]
    _ = Y * (h' * h) := mul_assoc _ _ _
    _ = Y := by rw [hh, mul_one]

theorem conj_fwd {h h' s R : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hh : h * h' = 1)
    (e : h * s = R * h) : R = h * s * h' :=
  calc R = R * (h * h') := by rw [hh, mul_one]
    _ = (R * h) * h' := (mul_assoc _ _ _).symm
    _ = h * s * h' := by rw [e]

@[expose] noncomputable def keysSet (l : List (ℕ × ℕ)) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  {X | ∃ k ∈ l.map Prod.fst, X = reflK k}

theorem keys_closed {fx : Bool} {l : List (ℕ × ℕ)} (hg : allL (gensOf fx) (validH fx) = true)
    (hc : ∀ e ∈ l, ∀ g ∈ gensOf fx,
      canonKey (act g (e.1 / 729)) (act g (e.1 % 729)) ∈ l.map Prod.fst) :
    ∀ X ∈ keysSet l, ∀ g ∈ gensOf fx, ∃ Y ∈ keysSet l, hcMat g * X = Y * hcMat g := by
  rintro _ ⟨k, hk, rfl⟩ g hgm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
  exact ⟨_, ⟨_, hc e he g hgm, rfl⟩, hcMat_conj (gens_sound hg g hgm) e.1⟩

theorem mem_keys_of_conj {fx : Bool} {l : List (ℕ × ℕ)} (hg : allL (gensOf fx) (validH fx) = true)
    (hc : ∀ e ∈ l, ∀ g ∈ gensOf fx,
      canonKey (act g (e.1 / 729)) (act g (e.1 % 729)) ∈ l.map Prod.fst)
    {h s : Matrix (Fin 6) (Fin 6) (ZMod 3)} {q : ℕ} (hh : h ∈ HS fx) (hq : q ∈ l.map Prod.fst)
    (e : h * s = reflK q * h) : s ∈ keysSet l := by
  obtain ⟨h', hh', h1, -⟩ := HS_inv hh
  obtain ⟨Y, hY, e2⟩ := closure_conj (keys_closed hg hc) (HS_le_GS hh') _ ⟨q, hq, rfl⟩
  rw [conj_back h1 e e2]
  exact hY

@[expose] def K1Prop (fx : Bool) (repTab nrep : ℕ) : Prop :=
  ∀ v f, v < 729 → canon v = true → f < 729 → dot v f = 1 →
    ∃ r hc, r < nrep ∧ validH fx hc = true ∧ canonKey (act hc v) (act hc f) = repAt repTab r

theorem k1Prop_of {fx : Bool} {repTab nrep : ℕ} (Ks : ℕ → List ℕ)
    (h : ∀ i, i < 27 → k1OK fx repTab nrep (27 * i) 27 (Ks i) = true) :
    K1Prop fx repTab nrep := by
  intro v f hv hc hf hd
  exact k1OK_sound (h (v / 27) (by omega)) (by omega) (by omega) hc hf hd

theorem k1_class {fx : Bool} {goods reps repsH : List ℕ} {repsB : List (ℕ × List ℕ)}
    {repTab nrep : ℕ} (hK1 : K1Prop fx repTab nrep) (htab : tabOK reps repTab nrep = true)
    (hreps : repsOK goods reps repsH repsB = true) {k : ℕ} (hk : keyOK k = true) :
    ∃ q hc, validH fx hc = true ∧ q ∈ goods ++ (repsH ++ repsB.map Prod.fst) ∧
      hcMat hc * reflK k = reflK q * hcMat hc := by
  obtain ⟨hk1, hcv, hd⟩ := keyOK_iff.mp hk
  obtain ⟨r, hc, hr, hv, he⟩ :=
    hK1 (k / 729) (k % 729) (by omega) hcv (Nat.mod_lt _ (by norm_num)) hd
  obtain ⟨hn, hat⟩ := tabOK_sound htab
  refine ⟨repAt repTab r, hc, hv, ?_, ?_⟩
  · rw [← repsOK_sound hreps, hat r hr, ← getN_eq]
    exact getN_mem_of_lt (by rw [← hn]; exact hr)
  · rw [hcMat_conj hv k, he]

theorem not_mem_of_repNOK {fx : Bool} {goods : List ℕ} {repsB : List (ℕ × List ℕ)}
    (hrepN : repNOK fx (List.append goods (fstL repsB)) = true) :
    ∀ q ∈ goods ++ repsB.map Prod.fst, reflK q ∉ HS fx := by
  intro q hq hH
  have e : List.append goods (fstL repsB) = goods ++ repsB.map Prod.fst := by
    rw [fstL_eq]
    rfl
  have h1 := (repNOK_sound hrepN q (by rw [e]; exact hq)).2
  rw [reflInH_iff.mpr hH] at h1
  cases h1

theorem cover_of {fx : Bool} {m : ℕ} {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    {goods reps repsH : List ℕ} {repsB : List (ℕ × List ℕ)} {repTab nrep : ℕ}
    {LH : List (ℕ × ℕ)} (hm : goods.length = m)
    (hgood : ∀ c : Fin m, reflK (getN goods c) = good c)
    (hg : allL (gensOf fx) (validH fx) = true) (hK1 : K1Prop fx repTab nrep)
    (htab : tabOK reps repTab nrep = true) (hreps : repsOK goods reps repsH repsB = true)
    (hbad : badOK fx (gensOf fx) repsB = true) (hlh : lhOK fx (gensOf fx) repsH LH = true) :
    ReflCover (HS fx) good := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := exists_key_of_isRefl hs
  obtain ⟨q, hc, hv, hq, e⟩ := k1_class hK1 htab hreps hk
  have hh := hcMat_mem hv
  rcases List.mem_append.mp hq with hq | hq
  · right
    right
    obtain ⟨i, hi, rfl⟩ := exists_getN_of_mem hq
    refine ⟨⟨i, by rw [← hm]; exact hi⟩, hcMat hc, hh, ?_⟩
    rw [← hgood]
    exact e
  rcases List.mem_append.mp hq with hq | hq
  · left
    obtain ⟨-, hlR, hlE⟩ := lhOK_sound hlh
    obtain ⟨k', hk', e'⟩ := mem_keys_of_conj hg (fun e he => (hlE e he).2.2) hh (hlR q hq) e
    rw [e']
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp hk'
    exact reflInH_iff.mp (hlE e0 he0).2.1
  · right
    left
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    obtain ⟨M, hM, hM0, hMn⟩ :=
      badW_spec hg (by simp [lenN_eq]) (badOK_sound hbad b hb)
    refine ⟨M, (Submonoid.closure_le.mpr ?_) hM, hM0, hMn⟩
    obtain ⟨h', hh', -, h1⟩ := HS_inv hh
    rintro X (hX | ⟨r, hr', rfl⟩)
    · exact Submonoid.subset_closure (Or.inl hX)
    · rw [List.mem_singleton.mp hr', conj_fwd h1 e]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.subset_closure (Or.inl hh))
        (Submonoid.subset_closure (Or.inr rfl))) (Submonoid.subset_closure (Or.inl hh'))

theorem mix_of {fx : Bool} {m : ℕ} {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    {goods : List ℕ} {ws : List (List ℕ)} (hm : goods.length = m)
    (hgood : ∀ c : Fin m, reflK (getN goods c) = good c)
    (hg : allL (gensOf fx) (validH fx) = true) (hk12 : k12OK fx (gensOf fx) goods ws = true) :
    ReflMix (HS fx) good := by
  rintro c c' hne Q ⟨h, hh, e⟩
  obtain ⟨w, -, hw⟩ := k12OK_sound hk12 (c := c.val) (c' := c'.val)
    (by rw [hm]; exact c.isLt) (by rw [hm]; exact c'.isLt) (fun h => hne (Fin.ext h))
  obtain ⟨M, hM, hM0, hMn⟩ := badW_spec hg (by simp [lenN_eq]) hw
  refine ⟨M, (Submonoid.closure_le.mpr ?_) hM, hM0, hMn⟩
  obtain ⟨h', hh', -, h1⟩ := HS_inv hh
  rintro X (hX | ⟨r, hr, rfl⟩)
  · exact Submonoid.subset_closure (Or.inl hX)
  · rcases List.mem_cons.mp hr with rfl | hr
    · rw [hgood c, conj_fwd h1 e]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.subset_closure (Or.inl hh))
        (Submonoid.subset_closure (Or.inr (Or.inl rfl)))) (Submonoid.subset_closure (Or.inl hh'))
    · rw [List.mem_singleton.mp hr, hgood c']
      exact Submonoid.subset_closure (Or.inr (Or.inr rfl))

theorem lines_of {fx : Bool} {m : ℕ} {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    {goods reps repsH : List ℕ} {repsB : List (ℕ × List ℕ)} {repTab nrep : ℕ}
    {LH : List (ℕ × ℕ)} {LG : Fin m → List (ℕ × ℕ)} {OW : Fin m → List (ℕ × (ℕ × ℕ))}
    (hm : goods.length = m) (hgood : ∀ c : Fin m, reflK (getN goods c) = good c)
    (hg : allL (gensOf fx) (validH fx) = true) (hK1 : K1Prop fx repTab nrep)
    (htab : tabOK reps repTab nrep = true) (hreps : repsOK goods reps repsH repsB = true)
    (hrepN : repNOK fx (List.append goods (fstL repsB)) = true)
    (hlh : lhOK fx (gensOf fx) repsH LH = true)
    (hlg : ∀ c : Fin m, lgOK fx (gensOf fx) (getN goods c) (LG c) = true)
    (hk3 : ∀ c : Fin m, k3OK (gensOf fx) (getN goods c) LH (LG c) (OW c) = true) :
    ReflLines (HS fx) good := by
  intro c x hx hcnt
  obtain ⟨hlP, hlR, hlE⟩ := lhOK_sound hlh
  obtain ⟨hgP, hgM, hgE⟩ := lgOK_sound (hlg c)
  have hnot := not_mem_of_repNOK hrepN
  have hgoodN : good c ∉ HS fx := by
    rw [← hgood c]
    exact hnot _ (List.mem_append_left _ (getN_mem_of_lt (by rw [hm]; exact c.isLt)))
  have hRS : ∀ s, s ∈ ReflSet (HS fx) (good c) ↔
      ∃ k ∈ (LH ++ LG c).map Prod.fst, s = reflK k := by
    intro s
    constructor
    · rintro ⟨hs, hH | ⟨h, hh, e⟩⟩
      · obtain ⟨k, hk, rfl⟩ := exists_key_of_isRefl hs
        obtain ⟨q, hc, hv, hq, e⟩ := k1_class hK1 htab hreps hk
        have hh := hcMat_mem hv
        obtain ⟨h', hh', -, h1⟩ := HS_inv hh
        have hqH : reflK q ∈ HS fx := by
          rw [conj_fwd h1 e]
          exact HS_mul (HS_mul hh hH) hh'
        have hq' : q ∈ repsH := by
          rcases List.mem_append.mp hq with hq | hq
          · exact absurd hqH (hnot q (List.mem_append_left _ hq))
          rcases List.mem_append.mp hq with hq | hq
          · exact hq
          · exact absurd hqH (hnot q (List.mem_append_right _ hq))
        obtain ⟨k', hk', e'⟩ := mem_keys_of_conj hg (fun e he => (hlE e he).2.2) hh (hlR q hq') e
        exact ⟨k', by rw [List.map_append]; exact List.mem_append_left _ hk', e'⟩
      · rw [← hgood c] at e
        obtain ⟨k', hk', e'⟩ := mem_keys_of_conj hg (fun e he => (hgE e he).2.2) hh hgM e
        exact ⟨k', by rw [List.map_append]; exact List.mem_append_right _ hk', e'⟩
    · rintro ⟨k, hk, rfl⟩
      rw [List.map_append] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        exact ⟨isRefl_reflK (hlE e he).1, Or.inl (reflInH_iff.mp (hlE e he).2.1)⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        obtain ⟨hc, hv, hce⟩ := (hgE e he).2.1
        refine ⟨isRefl_reflK (hgE e he).1, Or.inr ⟨hcMat hc, hcMat_mem hv, ?_⟩⟩
        rw [hcMat_conj hv, hce, hgood c]
  have hok : ∀ k ∈ (LH ++ LG c).map Prod.fst, keyOK k = true := by
    intro k hk
    rw [List.map_append] at hk
    rcases List.mem_append.mp hk with hk | hk <;> obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    · exact (hlE e he).1
    · exact (hgE e he).1
  have dj : ∀ a, a ∈ LH.map Prod.fst → a ∈ (LG c).map Prod.fst → False := by
    intro a ha hb
    obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e2, he2, h12⟩ := List.mem_map.mp hb
    have hH := reflInH_iff.mp (hlE e1 he1).2.1
    obtain ⟨hc, hv, hce⟩ := (hgE e2 he2).2.1
    have hh := hcMat_mem hv
    obtain ⟨h', hh', -, h1⟩ := HS_inv hh
    have e := hcMat_conj hv e2.1
    rw [hce, h12] at e
    apply hgoodN
    rw [← hgood c, conj_fwd h1 e]
    exact HS_mul (HS_mul hh hH) hh'
  have hnd : ((LH ++ LG c).map Prod.fst).Nodup := by
    rw [List.map_append]
    first
      | exact List.nodup_append.mpr ⟨hlP.imp ne_of_lt, hgP.imp ne_of_lt,
          fun a ha b hb hab => dj a ha (hab ▸ hb)⟩
      | exact List.nodup_append.mpr ⟨hlP.imp ne_of_lt, hgP.imp ne_of_lt,
          fun a ha hb => dj a ha hb⟩
  have hcard : ∀ y : Fin 6 → ZMod 3,
      {s | s ∈ ReflSet (HS fx) (good c) ∧ s *ᵥ y = y}.ncard =
        ((LH ++ LG c).filter fun e => dot (encV y) (e.1 % 729) == 0).length := by
    intro y
    have hset : {s | s ∈ ReflSet (HS fx) (good c) ∧ s *ᵥ y = y} =
        reflK '' ↑((((LH ++ LG c).map Prod.fst).filter
          fun k => dot (encV y) (k % 729) == 0).toFinset) := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset,
        List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨hs, hfix⟩
        obtain ⟨k, hk, rfl⟩ := (hRS s).mp hs
        exact ⟨k, ⟨hk, (reflK_fix_iff (hok k hk) y).mp hfix⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hd⟩, rfl⟩
        exact ⟨(hRS _).mpr ⟨k, hk, rfl⟩, (reflK_fix_iff (hok k hk) y).mpr hd⟩
    have hinj : Set.InjOn reflK ↑((((LH ++ LG c).map Prod.fst).filter
        fun k => dot (encV y) (k % 729) == 0).toFinset) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter] at ha hb
      exact reflK_inj (hok a ha.1) (hok b hb.1) hab
    rw [hset, hinj.ncard_image, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (hnd.filter _), List.filter_map, List.length_map]
    rfl
  rw [hcard, hcard] at hcnt
  have he0 : encV (Pi.single 0 1) = 1 := by decide
  rw [he0] at hcnt
  have hx0 : 0 < encV x := by
    rcases Nat.eq_zero_or_pos (encV x) with h0 | h0
    · exfalso
      apply hx
      rw [← decV_encV x, h0]
      funext j
      simp [decV, dg_eq]
    · exact h0
  obtain ⟨w, hw, hwx⟩ := k3OK_sound (gens_sound hg) (hk3 c) hx0 (encV_lt x) hcnt
  obtain ⟨-, ew⟩ := applyW_spec (refls := [getN goods c]) hg w (x := 1) (by norm_num)
  refine ⟨wordM (gensOf fx) [getN goods c] w, ?_, ?_⟩
  · refine (Submonoid.closure_mono ?_) (wordM_mem hg (fun g hgw => ?_))
    · rintro X (hX | ⟨r, hr, rfl⟩)
      · exact Or.inl hX
      · rw [List.mem_singleton.mp hr]
        exact Or.inr (hgood c)
    · have := hw g hgw
      rw [lenN_eq] at this
      simp only [List.length_singleton]
      omega
  · have e1 : (Pi.single 0 1 : Fin 6 → ZMod 3) = decV 1 := (decV_pow3 0).symm
    rw [e1, ← ew]
    rcases hwx with h | h
    · left
      rw [h, decV_encV]
    · right
      rw [h, decV_negV, decV_encV]

theorem refl_of_checks {fx : Bool} {m : ℕ} {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    {goods reps repsH : List ℕ} {repsB : List (ℕ × List ℕ)} {repTab nrep : ℕ}
    {ws : List (List ℕ)} {LH : List (ℕ × ℕ)} {LG : Fin m → List (ℕ × ℕ)}
    {OW : Fin m → List (ℕ × (ℕ × ℕ))}
    (hm : goods.length = m) (hgood : ∀ c : Fin m, reflK (getN goods c) = good c)
    (hg : allL (gensOf fx) (validH fx) = true) (hK1 : K1Prop fx repTab nrep)
    (htab : tabOK reps repTab nrep = true) (hreps : repsOK goods reps repsH repsB = true)
    (hrepN : repNOK fx (List.append goods (fstL repsB)) = true)
    (hbad : badOK fx (gensOf fx) repsB = true) (hk12 : k12OK fx (gensOf fx) goods ws = true)
    (hlh : lhOK fx (gensOf fx) repsH LH = true)
    (hlg : ∀ c : Fin m, lgOK fx (gensOf fx) (getN goods c) (LG c) = true)
    (hk3 : ∀ c : Fin m, k3OK (gensOf fx) (getN goods c) LH (LG c) (OW c) = true) :
    ReflCover (HS fx) good ∧ ReflMix (HS fx) good ∧ ReflLines (HS fx) good :=
  ⟨cover_of hm hgood hg hK1 htab hreps hbad hlh, mix_of hm hgood hg hk12,
    lines_of (OW := OW) hm hgood hg hK1 htab hreps hrepN hlh hlg hk3⟩

end CFSG.KC.TwD5R

end
