module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSL4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParAbs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix CFSG.Fischer

@[expose] def gens16M (z l : ℕ) : Mat16 := toMat 16 16 (gens16Bits z l)

theorem toMat_foldl_bmul {α : Type*} (g : α → Array ℕ) (w : List α) (acc : Array ℕ) :
    toMat 16 16 (w.foldl (fun acc l => bmul 16 16 acc (g l)) acc) =
      toMat 16 16 acc * (w.map fun l => toMat 16 16 (g l)).prod := by
  induction w generalizing acc with
  | nil => simp
  | cons l w ih => rw [List.foldl_cons, ih, toMat_bmul, List.map_cons, List.prod_cons, mul_assoc]

theorem toMat_id16' : toMat 16 16 id16 = 1 := by
  ext r c
  rw [toMat_apply, id16, getD_ofFn, Nat.testBit_two_pow, one_apply]
  by_cases h : r = c
  · subst h; simp
  · have : (r : ℕ) ≠ c := Fin.val_ne_of_ne h
    simp [h, this]

theorem toMat_word16Bits (z : ℕ) (w : List ℕ) :
    toMat 16 16 (word16Bits z w) = (w.map (gens16M z)).prod := by
  rw [word16Bits, toMat_foldl_bmul, toMat_id16', one_mul]
  rfl

noncomputable abbrev trSL (t : ℕ × ℕ × ℕ) : SL4 :=
  st4 (Fin.ofNat 4 t.1) (Fin.ofNat 4 t.2.1) ⟨Fin.ofNat 4 t.2.2⟩

noncomputable abbrev trProdSL (w : List (ℕ × ℕ × ℕ)) : SL4 := (w.map trSL).prod

theorem trCode_self (a : Fin 4) (k : ℕ) : trCode a a k = fun i j => if i = j then 1 else 0 := by
  funext i j
  by_cases h : i = j
  · subst h; simp only [trCode, ↓reduceIte]
  · have h' : ¬ (i = a ∧ j = a) := fun h'' => h (h''.1.trans h''.2.symm)
    simp only [trCode, h, h', ↓reduceIte]

theorem toMat_reBits_one : toMat 8 8 (reBits fun i j => if i = j then 1 else 0) = 1 := by
  decide

theorem rhoL_trSL (z : ℕ) (t : ℕ × ℕ × ℕ) (ht : t.2.2 < 4) :
    rhoL z (trSL t) = toMat 16 16 (rhoTrBits z (Fin.ofNat 4 t.1) (Fin.ofNat 4 t.2.1) t.2.2) := by
  have hk : (((⟨Fin.ofNat 4 t.2.2⟩ : F4).code : ℕ)) = t.2.2 := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt ht]
  by_cases hab : Fin.ofNat 4 t.1 = Fin.ofNat 4 t.2.1
  · rw [trSL, hab, st4, stT_diag, map_one, rhoTrBits, trCode_self, trCode_self,
      toMat_lineConjBits, toMat_reBits_one, bdiag_one, Matrix.mul_one, lineM_mul_lineInvM]
  · rw [trSL, rhoL_st4 z hab, hk]

theorem rhoL_trProdSL (z : ℕ) (w : List (ℕ × ℕ × ℕ)) (hw : ∀ t ∈ w, t.2.2 < 4) :
    rhoL z (trProdSL w) = toMat 16 16 (trProdBits z w) := by
  rw [trProdBits, toMat_foldl_bmul, toMat_id16', one_mul]
  induction w with
  | nil => simp [trProdSL]
  | cons t w ih =>
    have ht := hw t (by simp)
    have hw' : ∀ t ∈ w, t.2.2 < 4 := fun t' h => hw t' (by simp [h])
    rw [trProdSL, List.map_cons, List.prod_cons, map_mul, ← trProdSL, ih hw', rhoL_trSL z t ht,
      List.map_cons, List.prod_cons]

theorem lKW_code (s : ℕ) : ∀ t ∈ lKW s, t.2.2 < 4 := by
  rcases Nat.lt_or_ge s 3 with hs | hs
  · interval_cases s <;> decide
  · have : lKW s = lKW 2 := by
      match s, hs with
      | n + 3, _ => rfl
    rw [this]; decide

theorem lDW_code {z : ℕ} (hz : z = 1 ∨ z = 2) {k : ℕ} (hk : k < 8) : ∀ t ∈ lDW z k, t.2.2 < 4 := by
  rcases hz with rfl | rfl <;> interval_cases k <;> decide

theorem lGWList_lt : ∀ w ∈ lGWList, ∀ l ∈ w, l < 11 := by decide

theorem lGW_lt (z a b k : ℕ) : ∀ l ∈ lGW z a b k, l < 11 := by
  intro l hl
  rw [lGW, List.getD_eq_getElem?_getD] at hl
  rcases h : lGWList[lIdx z a b k]? with _ | w
  · rw [h] at hl; simp at hl
  · rw [h] at hl
    exact lGWList_lt w (List.mem_of_getElem? h) l hl

section Linear


theorem lCheck_spec {z : ℕ} (hz : z = 1 ∨ z = 2) :
    (∀ s < 3, trProdBits z (lKW s) = rho16 (genBits (Fin.ofNat 3 s))) ∧
      (∀ k < 8, trProdBits z (lDW z k) = dGen z k) ∧
      ∀ a < 4, ∀ b < 4, a ≠ b → ∀ k ∈ [1, 2, 3],
        rhoTrBits z (Fin.ofNat 4 a) (Fin.ofNat 4 b) k = word16Bits z (lGW z a b k) := by
  have h := lCheck_eq_true
  simp only [lCheck, List.all_eq_true, Bool.and_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  have hz' := h z (by rcases hz with rfl | rfl <;> simp)
  refine ⟨hz'.1.1, hz'.1.2, fun a ha b hb hab k hk => ?_⟩
  rcases hz'.2 a ha b hb with h1 | h1
  · exact absurd h1 hab
  · exact h1 k (by simpa using hk)

theorem rhoL_lKW {z : ℕ} (hz : z = 1 ∨ z = 2) (s : Fin 3) :
    rhoL z (trProdSL (lKW s)) = rhoM (genMat s) := by
  rw [rhoL_trProdSL z _ (lKW_code s), (lCheck_spec hz).1 s s.isLt, Fin.ofNat_val_eq_self,
    toMat_rho16]
  rfl

theorem rhoL_lDW {z : ℕ} (hz : z = 1 ∨ z = 2) {k : ℕ} (hk : k < 8) :
    rhoL z (trProdSL (lDW z k)) = toMat 16 16 (dGen z k) := by
  rw [rhoL_trProdSL z _ (lDW_code hz hk), (lCheck_spec hz).2.1 k hk]

theorem exists_word_rhoL_st4 {z : ℕ} (hz : z = 1 ∨ z = 2) (a b : Fin 4) (c : F4) :
    ∃ w : List ℕ, (∀ l ∈ w, l < 11) ∧ rhoL z (st4 a b c) = (w.map (gens16M z)).prod := by
  by_cases hab : a = b
  · subst hab; exact ⟨[], by simp, by rw [st4, stT_diag, map_one]; rfl⟩
  by_cases hc : (c.code : ℕ) = 0
  · have hc0 : c = 0 := f4_ext (Fin.ext hc)
    refine ⟨[], by simp, ?_⟩
    rw [hc0, st4, stT_zero, map_one]; rfl
  refine ⟨lGW z a b c.code, lGW_lt z a b c.code, ?_⟩
  have hk : (c.code : ℕ) ∈ [1, 2, 3] := by
    have := c.code.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h := (lCheck_spec hz).2.2 a a.isLt b b.isLt (fun h => hab (Fin.ext h)) c.code hk
  rw [Fin.ofNat_val_eq_self, Fin.ofNat_val_eq_self] at h
  rw [rhoL_st4 z hab, h, toMat_word16Bits]


theorem tCheck_spec :
    (∀ z ∈ [1, 2], ∀ a < 4, ∀ b < 4, a ≠ b → ∀ k ∈ [1, 2, 3],
      bmul 16 16 (bmul 16 16 tBits16 (rhoTrBits z (Fin.ofNat 4 a) (Fin.ofNat 4 b) k)) tBits16 =
        rhoTrBits z (piJ (Fin.ofNat 4 b)) (piJ (Fin.ofNat 4 a)) (frobCode k)) ∧
    ∀ z ∈ [0, 3], ∀ s < 3,
      bmul 16 16 (bmul 16 16 tBits16 (lineConjBits z (genBits (Fin.ofNat 3 s)) id8)) tBits16 =
        lineConjBits z id8 (genBits (Fin.ofNat 3 s)) := by
  have h := tCheck_eq_true
  simp only [tCheck, List.all_eq_true, Bool.and_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true] at h
  refine ⟨fun z hz a ha b hb hab k hk => ?_, h.2⟩
  rcases h.1 z hz a ha b hb with h1 | h1
  · exact absurd h1 hab
  · exact h1 k hk

theorem tM16_rhoL {z : ℕ} (hz : z = 1 ∨ z = 2) (g : SL4) :
    tM16 * rhoL z g * tM16 = rhoL z (sigmaSL g) := by
  let φ₁ : SL4 →* Mat16 :=
    { toFun := fun g => tM16 * rhoL z g * tM16
      map_one' := by rw [map_one, Matrix.mul_one, tM16_mul_tM16]
      map_mul' := fun g h => by
        rw [map_mul]
        calc tM16 * (rhoL z g * rhoL z h) * tM16
            = tM16 * rhoL z g * (tM16 * tM16) * rhoL z h * tM16 := by
              rw [tM16_mul_tM16, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have key : φ₁ = (rhoL z).comp sigmaSL := by
    refine MonoidHom.eq_of_eqOn_dense (closure_stT (F := F4) (m := 3) (by norm_num)) ?_
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    change tM16 * rhoL z (st4 a b c) * tM16 = rhoL z (sigmaSL (st4 a b c))
    rw [sigmaSL_st4]
    by_cases hab : a = b
    · subst hab
      rw [st4, st4, stT_diag, stT_diag, map_one, Matrix.mul_one, tM16_mul_tM16]
    by_cases hc : (c.code : ℕ) = 0
    · have hc0 : c = 0 := f4_ext (Fin.ext hc)
      rw [hc0, map_zero, st4, st4, stT_zero, stT_zero, map_one, Matrix.mul_one, tM16_mul_tM16]
    have hk : (c.code : ℕ) ∈ [1, 2, 3] := by
      have := c.code.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have h := (tCheck_spec).1 z (by rcases hz with rfl | rfl <;> simp) a a.isLt b b.isLt
      (fun h => hab (Fin.ext h)) c.code hk
    rw [Fin.ofNat_val_eq_self, Fin.ofNat_val_eq_self] at h
    rw [rhoL_st4 z hab, rhoL_st4 z (piJ_ne hab), code_frobF4, ← h, toMat_bmul, toMat_bmul,
      toMat_tBits16]
  have := DFunLike.congr_fun key g
  simpa only [φ₁, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply] using this

end Linear

section Unitary


@[expose] noncomputable def rhoU (z : ℕ) : SU42b × SU42b →* Mat16 where
  toFun p := lineM z * bdiag ((p.1 : GL (Fin 8) (ZMod 2)) : Mat8)
    ((p.2 : GL (Fin 8) (ZMod 2)) : Mat8) * lineInvM z
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, Units.val_one, bdiag_one,
      Matrix.mul_one, lineM_mul_lineInvM]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, ← bdiag_mul]
    calc lineM z * (bdiag ((p.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((p.2 : GL (Fin 8) (ZMod 2)) : Mat8) *
          bdiag ((q.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((q.2 : GL (Fin 8) (ZMod 2)) : Mat8)) *
          lineInvM z
        = lineM z * bdiag ((p.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((p.2 : GL (Fin 8) (ZMod 2)) : Mat8) *
            (lineInvM z * lineM z) *
            bdiag ((q.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((q.2 : GL (Fin 8) (ZMod 2)) : Mat8) *
            lineInvM z := by
          rw [lineInvM_mul_lineM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem rhoU_apply (z : ℕ) (p : SU42b × SU42b) :
    rhoU z p = lineM z * bdiag ((p.1 : GL (Fin 8) (ZMod 2)) : Mat8)
      ((p.2 : GL (Fin 8) (ZMod 2)) : Mat8) * lineInvM z := rfl

theorem rhoU_injective (z : ℕ) : Function.Injective (rhoU z) := by
  intro p q hpq
  have h1 : bdiag ((p.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((p.2 : GL (Fin 8) (ZMod 2)) : Mat8) =
      bdiag ((q.1 : GL (Fin 8) (ZMod 2)) : Mat8) ((q.2 : GL (Fin 8) (ZMod 2)) : Mat8) := by
    have := congrArg (fun X => lineInvM z * X * lineM z) hpq
    simp only [rhoU_apply, ← Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.mul_one] using this
  exact Prod.ext (Subtype.ext (Units.ext (bdiag_injective_left h1)))
    (Subtype.ext (Units.ext (bdiag_injective_right h1)))

end Unitary

theorem closure_inl_union_inr {G H : Type*} [Group G] [Group H] {S : Set G} {T : Set H}
    (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤) :
    Subgroup.closure ((fun x => (x, (1 : H))) '' S ∪ (fun y => ((1 : G), y)) '' T) = ⊤ := by
  set C := Subgroup.closure ((fun x => (x, (1 : H))) '' S ∪ (fun y => ((1 : G), y)) '' T)
  have h1 : ∀ x : G, (x, (1 : H)) ∈ C := by
    intro x
    have hx : x ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction (p := fun x _ => (x, (1 : H)) ∈ C) ?_ ?_ ?_ ?_ hx
    · intro s hs; exact Subgroup.subset_closure (Or.inl ⟨s, hs, rfl⟩)
    · exact C.one_mem
    · intro a b _ _ ha hb
      have := C.mul_mem ha hb
      simpa using this
    · intro a _ ha
      have := C.inv_mem ha
      simpa using this
  have h2 : ∀ y : H, ((1 : G), y) ∈ C := by
    intro y
    have hy : y ∈ Subgroup.closure T := hT ▸ Subgroup.mem_top y
    refine Subgroup.closure_induction (p := fun y _ => ((1 : G), y) ∈ C) ?_ ?_ ?_ ?_ hy
    · intro t ht; exact Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
    · exact C.one_mem
    · intro a b _ _ ha hb
      have := C.mul_mem ha hb
      simpa using this
    · intro a _ ha
      have := C.inv_mem ha
      simpa using this
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have := C.mul_mem (h1 x) (h2 y)
  simpa using this

section UnitaryChecks


theorem uCheck_spec {z : ℕ} (hz : z = 0 ∨ z = 3) :
    (∀ k < 11, lineConjBits z (wordBits (uXW z k)) (wordBits (uYW z k)) = gens16Bits z k) ∧
      ∀ s < 2, word16Bits z (uTW z 0 s) = lineConjBits z (genBits (Fin.ofNat 3 s)) id8 ∧
        word16Bits z (uTW z 1 s) = lineConjBits z id8 (genBits (Fin.ofNat 3 s)) := by
  have h := uCheck_eq_true
  simp only [uCheck, List.all_eq_true, Bool.and_eq_true, List.mem_range, beq_iff_eq,
    List.mem_cons, List.not_mem_nil, or_false] at h
  exact h z (by rcases hz with rfl | rfl <;> simp)

theorem gens16M_eq_rhoU {z : ℕ} (hz : z = 0 ∨ z = 3) {k : ℕ} (hk : k < 11) :
    gens16M z k = rhoU z (⟨wordGL (uXW z k), wordGL_mem _⟩, ⟨wordGL (uYW z k), wordGL_mem _⟩) := by
  rw [gens16M, ← (uCheck_spec hz).1 k hk, toMat_lineConjBits, rhoU_apply]
  simp only [coe_wordGL]

theorem rhoU_genSU_one {z : ℕ} (s : Fin 3) :
    rhoU z (genSU s, 1) = toMat 16 16 (lineConjBits z (genBits s) id8) := by
  rw [toMat_lineConjBits, rhoU_apply, toMat_id8]
  simp only [genSU, coe_genGL, OneMemClass.coe_one, Units.val_one]
  rfl

theorem rhoU_one_genSU {z : ℕ} (s : Fin 3) :
    rhoU z (1, genSU s) = toMat 16 16 (lineConjBits z id8 (genBits s)) := by
  rw [toMat_lineConjBits, rhoU_apply, toMat_id8]
  simp only [genSU, coe_genGL, OneMemClass.coe_one, Units.val_one]
  rfl

theorem rhoU_eq_word {z : ℕ} (hz : z = 0 ∨ z = 3) {s : ℕ} (hs : s < 2) :
    rhoU z (genSU (Fin.ofNat 3 s), 1) = ((uTW z 0 s).map (gens16M z)).prod ∧
      rhoU z (1, genSU (Fin.ofNat 3 s)) = ((uTW z 1 s).map (gens16M z)).prod := by
  obtain ⟨h0, h1⟩ := (uCheck_spec hz).2 s hs
  rw [rhoU_genSU_one, rhoU_one_genSU, ← h0, ← h1, toMat_word16Bits, toMat_word16Bits]
  exact ⟨rfl, rfl⟩

theorem tM16_rhoU {z : ℕ} (hz : z = 0 ∨ z = 3) (p : SU42b × SU42b) :
    tM16 * rhoU z p * tM16 = rhoU z p.swap := by
  let φ₁ : SU42b × SU42b →* Mat16 :=
    { toFun := fun p => tM16 * rhoU z p * tM16
      map_one' := by rw [map_one, Matrix.mul_one, tM16_mul_tM16]
      map_mul' := fun g h => by
        rw [map_mul]
        calc tM16 * (rhoU z g * rhoU z h) * tM16
            = tM16 * rhoU z g * (tM16 * tM16) * rhoU z h * tM16 := by
              rw [tM16_mul_tM16, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hT : ∀ s : Fin 3, tM16 * rhoU z (genSU s, 1) * tM16 = rhoU z (1, genSU s) := by
    intro s
    have h := (tCheck_spec).2 z (by rcases hz with rfl | rfl <;> simp) s s.isLt
    rw [Fin.ofNat_val_eq_self] at h
    rw [rhoU_genSU_one, rhoU_one_genSU, ← h, toMat_bmul, toMat_bmul, toMat_tBits16]
  have key : φ₁ = (rhoU z).comp (MulEquiv.prodComm (M := SU42b) (N := SU42b)).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense (closure_inl_union_inr SU42b_eq_closure.symm
      SU42b_eq_closure.symm) ?_
    rintro _ (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · rcases hg with rfl | rfl
      · exact hT 0
      · exact hT 1
    · change tM16 * rhoU z (1, g) * tM16 = rhoU z (g, 1)
      have hg' : ∃ s : Fin 3, g = genSU s := by
        rcases hg with rfl | rfl
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
      obtain ⟨s, rfl⟩ := hg'
      rw [← hT s]
      calc tM16 * (tM16 * rhoU z (genSU s, 1) * tM16) * tM16
          = (tM16 * tM16) * rhoU z (genSU s, 1) * (tM16 * tM16) := by
            simp only [Matrix.mul_assoc]
        _ = rhoU z (genSU s, 1) := by rw [tM16_mul_tM16, Matrix.one_mul, Matrix.mul_one]
  have := DFunLike.congr_fun key p
  simp only [φ₁, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] at this
  exact this

end UnitaryChecks

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
