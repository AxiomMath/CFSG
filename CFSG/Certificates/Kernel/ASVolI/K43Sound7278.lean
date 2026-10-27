module

public import Certificates.Data.Kernel.ASVolI.K43K7278
public import CFSG.Certificates.Kernel.ASVolI.K43Sound
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code CFSG.KC.Enum CFSG.KS

theorem k78fL_eq : ∀ (l : List ℕ) (k : List ℕ → Bool), k78fL l k = k l
  | [], _ => rfl
  | x :: xs, k => by
    rw [k78fL, PF.strictB_eqP, k78fL_eq xs]

theorem k78pairs_flatMap {α : Type} (f g : α → ℕ) : ∀ l : List α,
    k78pairs (l.flatMap fun c => [f c, g c]) = l.map fun c => (f c, g c)
  | [] => rfl
  | c :: l => by
    rw [List.flatMap_cons, List.map_cons, ← k78pairs_flatMap f g l]
    rfl

theorem k78_all_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem k78_any_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem k78_range_filter_map (l : List ℕ) (f : ℕ → Bool) :
    ((List.range l.length).filter fun p => f (l.getD p 0)).map (fun p => l.getD p 0) =
      l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.getD_eq_getElem?_getD] at ih
    cases hx : f x <;>
      simp [List.range_succ_eq_map, List.filter_cons, hx, List.filter_map, Function.comp_def,
        List.map_map, ih]

theorem k78_getD_mem {E : List ℕ} {p : ℕ} (hp : p < E.length) : E.getD p 0 ∈ E := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.getElem_mem hp

theorem k78_idx_contains {E : List ℕ} {f : ℕ → Bool} {p : ℕ} (hp : p < E.length) :
    ((List.range E.length).filter fun q => f (E.getD q 0)).contains p = f (E.getD p 0) := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

theorem k78_arrMul (p : ℕ) {q : ℕ} (hq : vpK q = true) :
    arrMul (unpk p) (unpk q) = unpk (pc24 p q) := by
  apply Array.ext (by simp [arrMul, size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa [size_unpk] using h2
  rw [← getElem!_pos (unpk (pc24 p q)) i h2, unpk_get _ hi, pg_pc24 p q hi]
  simp only [arrMul, Array.getElem_ofFn]
  rw [unpk_get q hi, unpk_get p ((vpK_spec hq).2 i hi)]

theorem k78_idArr : idArr = unpk k78id := by
  apply Array.ext (by simp [idArr, size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa [size_unpk] using h2
  rw [← getElem!_pos (unpk k78id) i h2, unpk_get _ hi, k78id, pg_id hi]
  simp [idArr]

theorem k78_vid : vpK k78id = true := vpK_id

theorem k78_beq {x y : ℕ} (hx : vpK x = true) (hy : vpK y = true) :
    (unpk x == unpk y) = (x == y) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨unpk_inj hx hy, fun h => h ▸ rfl⟩

theorem k78_contains {L : List ℕ} (hL : ∀ e ∈ L, vpK e = true) {x : ℕ} (hx : vpK x = true) :
    (L.map unpk).contains (unpk x) = L.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨e, he, h⟩ => unpk_inj (hL e he) hx h ▸ he, fun h => ⟨x, h, rfl⟩⟩

theorem k78_pkOK {a : Array ℕ} (h : k78pkOK a = true) :
    unpk (k78pk a) = a ∧ vpK (k78pk a) = true := by
  simp only [k78pkOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem k78_tree_mem : ∀ (l : List ℕ) (t : KT) (x : ℕ),
    (l.foldl KT.ins t).mem x = (l.contains x || t.mem x)
  | [], t, x => by simp
  | a :: l, t, x => by
    rw [List.foldl_cons, k78_tree_mem l, KT.mem_ins, List.contains_cons]
    cases l.contains x <;> cases (x == a) <;> cases t.mem x <;> rfl

theorem k78tree_mem (E : List ℕ) (x : ℕ) : (k78tree E).mem x = E.contains x := by
  rw [k78tree, k78_tree_mem]
  cases E.contains x <;> rfl

theorem k78_act (e : ℕ) : actC11 (unpk e) = k78act e :=
  funext fun m => actM_unpk κCCols liftCCols e m

theorem k78_actC11_cols (a : Array ℕ) (m : ℕ) : actC11 a m = actM (matOf 11 (actC11 a)) m := by
  have hl : liftCCols.length = 11 := by decide
  have e1 : actC11 a m = actC11 a (m % 2 ^ 11) := by
    unfold actC11
    rw [← hl, actM_mod]
  have e2 := actM_mod (matOf 11 (actC11 a)) m
  rw [length_matOf] at e2
  rw [e1, ← actM_matOf (xorLin_actC11 a) 11 _ (Nat.mod_lt _ (by norm_num)), e2]

theorem k78_z0c : actC11 z0Arr = actM k78z0c := funext (k78_actC11_cols z0Arr)

theorem k78_colsE (e : ℕ) : actC11 (unpk e) = actM (k78cols e) := by
  funext m
  rw [k78_actC11_cols, k78_act]
  rfl

theorem k78_actM_zero : ∀ (cs : List ℕ), (∀ c ∈ cs, c = 0) → ∀ m, actM cs m = 0
  | [], _, _ => rfl
  | c :: cs, h, m => by
    rw [actM, h c List.mem_cons_self,
      k78_actM_zero cs (fun d hd => h d (List.mem_cons_of_mem c hd))]
    split <;> simp

theorem k78_xor_eq_zero {x y : ℕ} : x ^^^ y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h, Nat.xor_self]⟩
  have := congrArg (· ^^^ y) h
  simpa [Nat.xor_assoc, Nat.xor_self] using this

theorem k78_xl_sub {f : ℕ → ℕ} (hf : XorLin f) : XorLin fun m => f m ^^^ m := fun a b => by
  change f (a ^^^ b) ^^^ (a ^^^ b) = (f a ^^^ a) ^^^ (f b ^^^ b)
  rw [hf a b]
  ac_rfl

theorem k78_basis {F : ℕ → ℕ} (hF : XorLin F) :
    (∀ m < 2 ^ 11, F m = 0) ↔ ∀ j < 11, F (2 ^ j) = 0 := by
  refine ⟨fun h j hj => h _ (Nat.pow_lt_pow_right (by norm_num) hj), fun h m hm => ?_⟩
  rw [← actM_matOf hF 11 m hm]
  refine k78_actM_zero _ (fun c hc => ?_) m
  simp only [matOf, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact h j hj

theorem k78_quad_iff {fa fb : ℕ → ℕ} (ha : XorLin fa) (hb : XorLin fb) :
    ((List.range 2048).all fun m =>
      let w := fb m ^^^ m
      fa w == w) = k78quad fa fb := by
  have hF : XorLin fun m => fa (fb m ^^^ m) ^^^ (fb m ^^^ m) :=
    (k78_xl_sub ha).comp (k78_xl_sub hb)
  have key := k78_basis hF
  simp only [k78_xor_eq_zero] at key
  apply Bool.eq_iff_iff.2
  simp only [k78quad, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact key

theorem k78_quadPair (a b : Array ℕ) : quadPair a b = k78quad (actC11 a) (actC11 b) := by
  unfold quadPair
  exact k78_quad_iff (xorLin_actC11 a) (xorLin_actC11 b)

theorem k78_fix_combos {f : ℕ → ℕ} (hf : XorLin f) :
    ∀ {l : List ℕ}, (∀ a ∈ l, f a = a) → ∀ x ∈ combos l, f x = x
  | [], _, x, hx => by
    simp only [combos, List.mem_singleton] at hx
    rw [hx, hf.map_zero]
  | a :: l, h, x, hx => by
    rw [combos, List.mem_append, List.mem_map] at hx
    have ih := k78_fix_combos hf (l := l) fun b hb => h b (List.mem_cons_of_mem a hb)
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · rw [hf, ih y hy, h a List.mem_cons_self]

theorem k78_xl_act (e : ℕ) : XorLin (k78act e) := by
  rw [← k78_act]
  exact xorLin_actC11 _

theorem k78_inD_span {vz vb : List ℕ} (hs : k78span vz vb = true) (e : ℕ) :
    k78inD vz e = k78inD vb e := by
  simp only [k78span, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hs
  apply Bool.eq_iff_iff.2
  simp only [k78inD, List.all_eq_true, beq_iff_eq]
  exact ⟨fun h m hm => h m (hs.1 m hm), fun h m hm => k78_fix_combos (k78_xl_act e) h m (hs.2 m hm)⟩

theorem k78_octPts_lt : ∀ i ∈ octPts, i < 24 := by decide

theorem k78_fixOct (e : ℕ) : fixesOct (unpk e) = k78fixOct e := by
  unfold fixesOct k78fixOct
  exact k78_all_congr fun i hi => by rw [unpk_get e (k78_octPts_lt i hi)]

variable {E : List ℕ} [Fact (T24s2.check = true)]

theorem k78_n (H : Packed T24s2 E) : T24s2.n = E.length := n_eq H

theorem k78_tArr (H : Packed T24s2 E) {p : ℕ} (hp : p < E.length) :
    tArr p = unpk (E.getD p 0) :=
  elems_get H hp

theorem k78_kIdx (H : Packed T24s2 E) :
    kIdx () = (List.range E.length).filter fun p => k78fixOct (E.getD p 0) := by
  unfold kIdx
  rw [k78_n H]
  refine List.filter_congr fun p hp => ?_
  rw [k78_tArr H (List.mem_range.1 hp), k78_fixOct]

theorem k78_dzIdx (H : Packed T24s2 E) :
    dzIdx () = (List.range E.length).filter fun p => k78inD (vzMasks ()) (E.getD p 0) := by
  unfold dzIdx
  dsimp only
  rw [k78_n H]
  refine List.filter_congr fun p hp => ?_
  rw [k78_tArr H (List.mem_range.1 hp), k78_act]
  rfl

theorem k78_idx_map (H : Packed T24s2 E) (f : ℕ → Bool) :
    ((List.range E.length).filter fun p => f (E.getD p 0)).map tArr = (E.filter f).map unpk := by
  rw [← k78_range_filter_map E f, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  rw [List.mem_filter, List.mem_range] at hp
  exact k78_tArr H hp.1

theorem k78_vpF (H : Packed T24s2 E) {f : ℕ → Bool} {e : ℕ} (he : e ∈ E.filter f) :
    vpK e = true :=
  H.vp e (List.mem_filter.1 he).1

theorem k78_elems_contains (H : Packed T24s2 E) {q : ℕ} (hq : vpK q = true) :
    T24s2.elems.contains (unpk q) = (k78tree E).mem q := by
  rw [k78tree_mem, ← k78_contains H.vp hq]
  apply Bool.eq_iff_iff.2
  rw [Array.contains_iff_mem, H.elems, List.mem_toArray, List.contains_iff_mem]

theorem sylOK_of_K (H : Packed T24s2 E) (h : sylK E = true) : sylOK () = true := by
  unfold sylK at h
  simp only [k78fL_eq, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hs, hE⟩ := h
  rw [← funext (k78_inD_span hs)] at hE
  have hc': ∀ c ∈ sylConj, (unpk (k78pk c) = c ∧ vpK (k78pk c) = true) ∧
      (unpk (k78pk (invArr c)) = invArr c ∧ vpK (k78pk (invArr c)) = true) := fun c hcm =>
    ⟨k78_pkOK (hc c hcm).1.2, k78_pkOK (hc c hcm).2⟩
  unfold sylOK
  dsimp only
  rw [k78_kIdx H, k78_dzIdx H, k78_idx_map H, k78_idx_map H, k78_n H]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun c hcm => ⟨by rw [inAutOK_eq_inAutK]; exact (hc c hcm).1.1.1,
    (hc c hcm).1.1.2⟩, fun p hp => ?_⟩
  have hp' := List.mem_range.1 hp
  have hm := k78_getD_mem hp'
  have he := hE _ hm
  rw [k78_tArr H hp']
  generalize E.getD p 0 = e at he hm ⊢
  have hev := H.vp e hm
  simp only [k78pairs_flatMap, List.all_map, Function.comp_def] at he
  have hA : (sylConj.all fun c => T24s2.elems.contains (arrMul (arrMul (invArr c) (unpk e)) c)) =
      sylConj.all fun c => (k78tree E).mem (pc24 (pc24 (k78pk (invArr c)) e) (k78pk c)) :=
    k78_all_congr fun c hcm => by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc' c hcm
      have e1 : arrMul (arrMul (unpk (k78pk (invArr c))) (unpk e)) (unpk (k78pk c)) =
          unpk (pc24 (pc24 (k78pk (invArr c)) e) (k78pk c)) := by
        rw [k78_arrMul _ hev, k78_arrMul _ h2]
      rw [h3, h1] at e1
      rw [e1, k78_elems_contains H (vpK_pc24 (vpK_pc24 h4 hev) h2)]
  have hB : (((E.filter k78fixOct).map unpk).any fun k =>
        ((E.filter (k78inD (vzMasks ()))).map unpk).any fun d => arrMul k d == unpk e) =
      (E.filter k78fixOct).any fun k => (E.filter (k78inD (vzMasks ()))).any fun d =>
        pc24 k d == e := by
    simp only [List.any_map, Function.comp_def]
    refine k78_any_congr fun k hk => k78_any_congr fun d hd => ?_
    rw [k78_arrMul _ (k78_vpF H hd), k78_beq (vpK_pc24 (k78_vpF H hk) (k78_vpF H hd)) hev]
  rw [hA, hB]
  exact he

theorem classOK_of_K (H : Packed T24s2 E) (h : classK E = true) : classOK () = true := by
  unfold classK at h
  simp only [k78fL_eq, PF.strictB_eqP, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hz, hw⟩, hs, ⟨hlen, hE⟩, hx⟩ := h
  rw [← funext (k78_inD_span hs)] at hE hlen hx
  have hz' : unpk k78z0 = z0Arr ∧ vpK k78z0 = true := k78_pkOK hz
  unfold classOK
  dsimp only
  rw [k78_dzIdx H, inAutOK_eq_inAutK]
  have hxs : (((List.range E.length).filter fun p => k78inD (vzMasks ()) (E.getD p 0)).filter
        fun p => tArr p != idArr && tArr p != z0Arr).map tArr =
      ((E.filter (k78inD (vzMasks ()))).filter fun e => e != k78id && e != k78z0).map unpk := by
    rw [List.filter_filter]
    have e1 : ((List.range E.length).filter fun p =>
          (tArr p != idArr && tArr p != z0Arr) && k78inD (vzMasks ()) (E.getD p 0)) =
        (List.range E.length).filter fun p =>
          (fun e => (e != k78id && e != k78z0) && k78inD (vzMasks ()) e) (E.getD p 0) :=
      List.filter_congr fun p hp => by
        have hp' := List.mem_range.1 hp
        have hv := H.vp _ (k78_getD_mem hp')
        rw [k78_tArr H hp', k78_idArr, ← hz'.1]
        simp only [bne, k78_beq hv k78_vid, k78_beq hv hz'.2]
    rw [e1, k78_idx_map H (fun e => (e != k78id && e != k78z0) && k78inD (vzMasks ()) e),
      List.filter_filter]
  have hl := congrArg List.length hxs
  rw [List.length_map, List.length_map] at hl
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨by rw [hl]; exact hlen, fun p hp => ?_⟩, fun xg hxg => (hw xg hxg).1⟩, fun p hp => ?_⟩
  · rw [k78_n H] at hp
    have hp' := List.mem_range.1 hp
    have hm := k78_getD_mem hp'
    rw [k78_tArr H hp', k78_idx_contains hp']
    have he := hE _ hm
    generalize E.getD p 0 = e at he hm ⊢
    have hv := H.vp e hm
    rw [k78_quadPair, k78_z0c, k78_act, k78_arrMul _ hv, k78_idArr, ← hz'.1]
    simp only [bne, k78_beq (vpK_pc24 hv hv) k78_vid, k78_beq hv k78_vid, k78_beq hv hz'.2] at he ⊢
    exact he
  · have hmem : tArr p ∈ (((E.filter (k78inD (vzMasks ()))).filter
        fun e => e != k78id && e != k78z0).map unpk) := by
      rw [← hxs]
      exact List.mem_map_of_mem hp
    obtain ⟨e, he, hpe⟩ := List.mem_map.1 hmem
    have hc := hx e he
    rw [List.contains_iff_mem, List.mem_map] at hc
    obtain ⟨xg, hxg, hxe⟩ := hc
    rw [List.any_eq_true]
    refine ⟨xg, hxg, ?_⟩
    rw [beq_iff_eq, ← hpe, ← hxe, (k78_pkOK (hw xg hxg).2).1]

theorem k78_modOKx_def (ax : Array ℕ) (dz : List (Array ℕ)) : modOKx ax dz =
    ((dz.filter fun p => quadPair p ax).all [idArr, ax, z0Arr, arrMul ax z0Arr].contains &&
    [idArr, ax, z0Arr, arrMul ax z0Arr].all (dz.filter fun p => quadPair p ax).contains &&
    ((List.range 2048).filter fun m => actC11 ax m == m && actC11 z0Arr m == m).length == 64 &&
    ((List.range 2048).all fun m => [ax, z0Arr, arrMul ax z0Arr].all fun y =>
      let w := actC11 y m ^^^ m
      actC11 ax w == w && actC11 z0Arr w == w) &&
    indep6 (dmasks ax ++ dmasks z0Arr) && indep6 (vzMasks () ++ dmasks ax)) := rfl

theorem k78_quadL (ax az : Array ℕ) (L : List (Array ℕ)) :
    ((List.range 2048).all fun m => L.all fun y =>
      let w := actC11 y m ^^^ m
      actC11 ax w == w && actC11 az w == w) = L.all fun y => quadPair ax y && quadPair az y := by
  apply Bool.eq_iff_iff.2
  simp only [quadPair, List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h y hy => ⟨fun m hm => (h m hm y hy).1, fun m hm => (h m hm y hy).2⟩,
    fun h m hm y hy => ⟨(h y hy).1 m hm, (h y hy).2 m hm⟩⟩

theorem k78_indep6 {c : List ℕ} (h : k78indep6 c = true) : indep6 c = true := by
  simp only [k78indep6, indep6, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, decide_eq_true (CFSG.Decide.nodup_of_bitsetNodup_nat h.1.2)⟩, h.2⟩

theorem k78_dmasks (a : Array ℕ) : dmasks a = k78dm (actC11 a) := rfl

theorem k78_modOKx {D : List ℕ} (hD : ∀ d ∈ D, vpK d = true) {e : ℕ} (he : vpK e = true)
    (hz : unpk k78z0 = z0Arr) (hzv : vpK k78z0 = true)
    (h : modxK (vzMasks ()) k78z0c ((List.range 2048).filter fun m => actM k78z0c m == m) D
      k78id k78z0 e = true) :
    modOKx (unpk e) (D.map unpk) = true := by
  unfold modxK at h
  simp only [k78fL_eq, PF.strictB_eqP, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have haxz : arrMul (unpk e) z0Arr = unpk (pc24 e k78z0) := by rw [← hz, k78_arrMul _ hzv]
  have hfour : [idArr, unpk e, z0Arr, unpk (pc24 e k78z0)] =
      [k78id, e, k78z0, pc24 e k78z0].map unpk := by
    rw [k78_idArr, ← hz]
    rfl
  have hv4 : ∀ x ∈ [k78id, e, k78z0, pc24 e k78z0], vpK x = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    exacts [k78_vid, he, hzv, vpK_pc24 he hzv]
  have hstab : (D.map unpk).filter (fun p => quadPair p (unpk e)) =
      (D.filter fun p => k78quad (actM (k78cols p)) (actM (k78cols e))).map unpk := by
    rw [List.filter_map]
    refine congrArg (List.map unpk) (List.filter_congr fun p _ => ?_)
    rw [Function.comp_apply, k78_quadPair, k78_colsE, k78_colsE]
  have hvS : ∀ x ∈ D.filter (fun p => k78quad (actM (k78cols p)) (actM (k78cols e))),
      vpK x = true := fun x hx => hD x (List.mem_filter.1 hx).1
  rw [k78_modOKx_def, haxz, hfour, hstab, k78_quadL]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, k78_indep6 ?_⟩, k78_indep6 ?_⟩
  · simp only [List.all_map, Function.comp_def]
    rw [k78_all_congr fun x hx => k78_contains hv4 (hvS x hx)]
    exact h1
  · simp only [List.all_map, Function.comp_def]
    rw [k78_all_congr fun x hx => k78_contains hvS (hv4 x hx)]
    exact h2
  · rw [k78_colsE, k78_z0c]
    rw [List.filter_filter] at h3
    exact h3
  · simp only [List.all_cons, List.all_nil, Bool.and_true] at h4 ⊢
    rw [k78_quadPair, k78_quadPair, k78_quadPair, k78_quadPair, k78_quadPair, k78_quadPair,
      k78_colsE e, k78_act (pc24 e k78z0), k78_z0c]
    exact h4
  · rw [k78_dmasks, k78_dmasks, k78_colsE, k78_z0c]
    exact h5
  · rw [k78_dmasks, k78_colsE]
    exact h6

theorem modOK_of_K (H : Packed T24s2 E) (h : modK E = true) : modOK () = true := by
  unfold modK at h
  simp only [k78fL_eq, PF.strictB_eqP, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hz, hs, ⟨h1, h2⟩, h3⟩ := h
  rw [← funext (k78_inD_span hs)] at h3
  have hz' : unpk k78z0 = z0Arr ∧ vpK k78z0 = true := k78_pkOK hz
  unfold modOK
  dsimp only
  rw [k78_dzIdx H, k78_idx_map H]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun ax hax => ?_⟩
  · rw [k78_dmasks, k78_z0c]
    exact h1 m hm
  · rw [k78_z0c]
    exact h2 m hm
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hax
    have hev := k78_vpF H he
    have h4 := h3 e he
    rw [k78_idArr, ← hz'.1, k78_beq hev k78_vid, k78_beq hev hz'.2]
    simp only [Bool.or_eq_true] at h4 ⊢
    rcases h4 with (h4 | h4) | h4
    · exact Or.inl (Or.inl h4)
    · exact Or.inl (Or.inr h4)
    · exact Or.inr (k78_modOKx (fun d hd => k78_vpF H hd) hev hz'.1 hz'.2 h4)

end CFSG.KS.ASVolI

end
