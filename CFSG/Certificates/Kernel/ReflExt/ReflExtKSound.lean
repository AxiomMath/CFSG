module

public import Certificates.Data.Kernel.ReflExt.ReflExtKCan
public import Certificates.Data.CFSGNative.ReflExt.Check
public import CFSG.Certificates.Kernel.TwoNodeSmall.PosBKOK

public section

namespace CFSG.ReflExt.RXK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.LaneSound
  CFSG.TwoNodeSmall.PosBK CFSG.TwoNodeSmall.PosBK.OKS CFSG.ReflExt

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Snd

theorem lanes_succ (D x : Nat) : lanes (D + 1) x = x % 65536 :: lanes D (x / 65536) := rfl

theorem lanes_enc : ∀ l : List Nat, (∀ x ∈ l, x < 65536) → lanes l.length (enc l) = l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.length_cons, lanes_succ, enc_cons]
    have hx := h x (by simp)
    have e1 : (x + 65536 * enc l) % 65536 = x := by omega
    have e2 : (x + 65536 * enc l) / 65536 = enc l := by omega
    rw [e1, e2, lanes_enc l (fun y hy => h y (by simp [hy]))]

theorem lanes_pk (D : Nat) (v : Vec) : lanes D (pk D v) = (List.range D).map (ln v) := by
  have h := lanes_enc ((List.range D).map (ln v)) (by
    simp only [List.mem_map]
    rintro _ ⟨i, -, rfl⟩
    exact ln_lt v i)
  rw [List.length_map, List.length_range] at h
  rw [pk_eq]
  exact h

theorem lanes_pkr (D : Nat) (f : Vec) :
    (lanes D (pkr D f)).reverse = (List.range D).map (ln f) := by
  have h := lanes_enc ((List.range D).reverse.map (ln f)) (by
    simp only [List.mem_map]
    rintro _ ⟨i, -, rfl⟩
    exact ln_lt f i)
  rw [List.length_map, List.length_reverse, List.length_range] at h
  rw [pkr_eq]
  unfold rv
  rw [h, List.map_reverse, List.reverse_reverse]

theorem ln_map (D : Nat) (v : Vec) {i : Nat} (hi : i < D) :
    ln ((List.range D).map (ln v)) i = ln v i := by
  simp [ln, List.getD_eq_getElem?_getD, hi]

theorem pk_map_ln (D : Nat) (v : Vec) : pk D ((List.range D).map (ln v)) = pk D v := by
  rw [pk_eq, pk_eq]
  unfold fw
  apply enc_map_congr
  intro i hi
  exact ln_map D v (List.mem_range.mp hi)

theorem pkr_map_ln (D : Nat) (v : Vec) : pkr D ((List.range D).map (ln v)) = pkr D v := by
  rw [pkr_eq, pkr_eq]
  unfold rv
  apply enc_map_congr
  intro i hi
  exact ln_map D v (List.mem_range.mp (List.mem_reverse.mp hi))

theorem map_ln_self {D : Nat} {v : Vec} (hl : v.length = D) (h3 : ∀ x ∈ v, x < 3) :
    (List.range D).map (ln v) = v := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, ln, List.getD_eq_getElem _ _ h2]
  exact Nat.mod_eq_of_lt (h3 _ (List.getElem_mem h2))

@[expose] noncomputable def decR (D : Nat) (a : Nat × Nat) : Refl :=
  ⟨(lanes D a.2).reverse, lanes D a.1⟩

theorem packR3 {P : Pt} (hp : P.p = 3) (r : Refl) : packR P r = (pk P.D r.h, pkr P.D r.f) := by
  unfold packR
  rw [hp]
  rfl

theorem canP_iff {D : Nat} {a : Nat × Nat} (h : canP D a = true) :
    pk D (decR D a).h = a.1 ∧ pkr D (decR D a).f = a.2 := by
  unfold canP at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem packR_decR {P : Pt} (hp : P.p = 3) {a : Nat × Nat} (h : canP P.D a = true) :
    packR P (decR P.D a) = a := by
  rw [packR3 hp, (canP_iff h).1, (canP_iff h).2]

theorem decR_packR_h {P : Pt} (hp : P.p = 3) (r : Refl) :
    (decR P.D (packR P r)).h = (List.range P.D).map (ln r.h) := by
  rw [packR3 hp]
  exact lanes_pk _ _

theorem decR_packR_f {P : Pt} (hp : P.p = 3) (r : Refl) :
    (decR P.D (packR P r)).f = (List.range P.D).map (ln r.f) := by
  rw [packR3 hp]
  exact lanes_pkr _ _

theorem canP_packR {P : Pt} (hp : P.p = 3) (r : Refl) : canP P.D (packR P r) = true := by
  unfold canP
  simp only [Bool.and_eq_true, Nat.beq_eq]
  have e1 := decR_packR_h hp r
  have e2 := decR_packR_f hp r
  simp only [decR] at e1 e2
  rw [e1, e2, packR3 hp, pk_map_ln, pkr_map_ln]
  exact ⟨rfl, rfl⟩

theorem decR_packR_self {P : Pt} (hp : P.p = 3) {r : Refl} (hf : r.f.length = P.D)
    (hh : r.h.length = P.D) (hf3 : ∀ x ∈ r.f, x < 3) (hh3 : ∀ x ∈ r.h, x < 3) :
    decR P.D (packR P r) = r := by
  have e1 := decR_packR_h hp r
  have e2 := decR_packR_f hp r
  rw [map_ln_self hh hh3] at e1
  rw [map_ln_self hf hf3] at e2
  have e3 : decR P.D (packR P r) = ⟨(decR P.D (packR P r)).f, (decR P.D (packR P r)).h⟩ := rfl
  rw [e3, e1, e2]

@[expose] def dig (D : Nat) (k : Nat) : Vec :=
  Nat.rec (motive := fun _ => Nat → Vec) (fun _ => []) (fun _ ih k => k % 3 :: ih (k / 3)) D k

theorem dig_succ (D k : Nat) : dig (D + 1) k = k % 3 :: dig D (k / 3) := rfl

theorem dig_length : ∀ D k, (dig D k).length = D
  | 0, _ => rfl
  | D + 1, k => by rw [dig_succ, List.length_cons, dig_length D]

theorem dig_lt : ∀ D k, ∀ x ∈ dig D k, x < 3
  | 0, _, x, hx => by simp [dig] at hx
  | D + 1, k, x, hx => by
    rw [dig_succ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by norm_num)
    · exact dig_lt D _ x hx

theorem pkC_dig : ∀ D k, pkC D k = pk D (dig D k)
  | 0, _ => rfl
  | D + 1, k => by
    change Nat.add (Nat.mod k 3) (Nat.mul 65536 (pkC D (Nat.div k 3))) =
      Nat.add (Nat.mod (k % 3) 3) (Nat.mul 65536 (pk D (dig D (k / 3))))
    rw [pkC_dig D]
    change k % 3 + 65536 * _ = (k % 3) % 3 + 65536 * _
    rw [Nat.mod_mod]
    rfl

theorem pkrC_go : ∀ D k acc,
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun _ ih c acc => ih (Nat.div c 3) (Nat.add (Nat.mul acc 65536) (Nat.mod c 3))) D k acc =
    Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3))) D
      (dig D k) acc
  | 0, _, _ => rfl
  | D + 1, k, acc => by
    change _ = Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3))) D
      (dig D (k / 3)) (Nat.add (Nat.mul acc 65536) (Nat.mod (k % 3) 3))
    rw [← pkrC_go D]
    change _ = Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun _ ih c acc => ih (Nat.div c 3) (Nat.add (Nat.mul acc 65536) (Nat.mod c 3))) D (k / 3)
      (acc * 65536 + (k % 3) % 3)
    rw [Nat.mod_mod]
    rfl

theorem pkrC_dig (D k : Nat) : pkrC D k = pkr D (dig D k) := pkrC_go D k 0

theorem mem_allVecsP : ∀ D, ∀ v ∈ allVecsP 3 D, ∃ k < 3 ^ D, dig D k = v
  | 0, v, hv => ⟨0, by norm_num, by simp [allVecsP] at hv; rw [hv]; rfl⟩
  | D + 1, v, hv => by
    simp only [allVecsP, List.mem_flatMap, List.mem_map, List.mem_range] at hv
    obtain ⟨w, hw, i, hi, rfl⟩ := hv
    obtain ⟨k, hk, rfl⟩ := mem_allVecsP D w hw
    refine ⟨i + 3 * k, by rw [pow_succ]; omega, ?_⟩
    rw [dig_succ]
    have e1 : (i + 3 * k) % 3 = i := by omega
    have e2 : (i + 3 * k) / 3 = k := by omega
    rw [e1, e2]

theorem allVecsP_length : ∀ D, ∀ v ∈ allVecsP 3 D, v.length = D ∧ ∀ x ∈ v, x < 3 := by
  intro D v hv
  obtain ⟨k, -, rfl⟩ := mem_allVecsP D v hv
  exact ⟨dig_length D k, dig_lt D k⟩

theorem vec_map_ln {P : Pt} (hp : P.p = 3) (v : Vec) :
    P.vec ((List.range P.D).map (ln v)) = P.vec v := by
  funext i
  simp only [Pt.vec]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  have e : ln v i = v.getD i 0 % P.p := by rw [hp]; rfl
  rw [e, ZMod.natCast_mod]

theorem vec_decR {P : Pt} (hp : P.p = 3) (r : Refl) :
    P.vec (decR P.D (packR P r)).f = P.vec r.f ∧ P.vec (decR P.D (packR P r)).h = P.vec r.h := by
  rw [decR_packR_f hp, decR_packR_h hp, vec_map_ln hp, vec_map_ln hp]
  exact ⟨rfl, rfl⟩

theorem packR_inj {P : Pt} (hp : P.p = 3) {r s : Refl} (h : packR P r = packR P s) :
    P.vec r.f = P.vec s.f ∧ P.vec r.h = P.vec s.h := by
  rw [packR3 hp, packR3 hp, Prod.ext_iff] at h
  exact ⟨vec_of_vecEq P ((pkr_inj hp _ _).mp h.2), vec_of_vecEq P ((pk_inj hp _ _).mp h.1)⟩

@[expose] def negRf (D : Nat) (r : Refl) : Refl := ⟨negV D r.f, negV D r.h⟩

theorem negP_packR {P : Pt} (hp : P.p = 3) (r : Refl) :
    negP (fdB 3 P.D) P.D (packR P r) = packR P (negRf P.D r) := by
  rw [packR3 hp, packR3 hp]
  unfold negP
  rw [neg_pk, neg_pkr]
  rfl

theorem vec_negV {P : Pt} (hp : P.p = 3) [Fact P.p.Prime] (v : Vec) :
    P.vec (negV P.D v) = -P.vec v := by
  funext i
  simp only [Pt.vec, Pi.neg_apply, negV]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  have e : (3 - v.getD i 0 % 3) % 3 = (0 + (P.p - v.getD i 0 % P.p)) % P.p := by rw [hp, Nat.zero_add]
  rw [e, cast_refl _ _ _ (Fact.out : P.p.Prime).pos]
  simp

variable {P : Pt}

theorem sem_wf [Fact P.p.Prime] (hwf : P.WF) {x : CE} (hx : Sem P x) :
    P.dot (P.vec x.1.f) (P.vec x.1.h) = 2 := by
  obtain ⟨hw, hk, hh, hf⟩ := hx
  rw [hh, hf]
  have hwr : P.wordOK x.2.1.reverse = true := by simpa [Pt.wordOK] using hw
  have := word_rev hwf x.2.1.reverse hwr (gk P x).h
  rw [List.reverse_reverse] at this
  rw [this]
  unfold gk
  rw [List.getD_eq_getElem _ _ hk]
  exact hwf _ (List.getElem_mem hk)

theorem real_of_sem [Fact P.p.Prime] (hwf : P.WF) {x : CE} (hx : Sem P x) (r : Refl)
    (ε : ZMod P.p) (hε : ε * ε = 1) (hf : P.vec r.f = ε • P.vec x.1.f)
    (hh : P.vec r.h = ε • P.vec x.1.h) : realizes P (sw x) r = true := by
  unfold realizes
  rw [Bool.and_eq_true]
  refine ⟨sw_ok hx, ?_⟩
  rw [List.all_eq_true]
  intro i _
  apply vecEq_of_vec
  rw [sw_act hwf hx, vec_refl, vec_refl, hf, hh, smul_dot, smul_smul]
  have e : ε * P.dot (P.vec x.1.f) (P.vec (P.unit i)) * ε =
      P.dot (P.vec x.1.f) (P.vec (P.unit i)) * (ε * ε) := by ring
  rw [e, hε, mul_one]

theorem real_pos [Fact P.p.Prime] (hwf : P.WF) {x : CE} (hx : Sem P x) (r : Refl)
    (hf : P.vec r.f = P.vec x.1.f) (hh : P.vec r.h = P.vec x.1.h) : realizes P (sw x) r = true :=
  real_of_sem hwf hx r 1 (mul_one 1) (by rw [hf, one_smul]) (by rw [hh, one_smul])

theorem real_neg [Fact P.p.Prime] (hwf : P.WF) {x : CE} (hx : Sem P x) (r : Refl)
    (hf : P.vec r.f = -P.vec x.1.f) (hh : P.vec r.h = -P.vec x.1.h) :
    realizes P (sw x) r = true :=
  real_of_sem hwf hx r (-1) (by ring) (by rw [hf, neg_one_smul]) (by rw [hh, neg_one_smul])

@[expose] def cwD (P : Pt) (e : Refl) : List Nat → Refl
  | [] => e
  | l :: u => OKS.conjR P (P.gens.getD l ⟨[], []⟩) (cwD P e u)

theorem sem_cw [Fact P.p.Prime] (e : Refl) {k : Nat} (hk : k < P.gens.length)
    (he : P.gens.getD k ⟨[], []⟩ = e) :
    ∀ u : List Nat, (∀ l ∈ u, l < P.gens.length) → Sem P (cwD P e u, u, k)
  | [], _ => by
    refine ⟨rfl, hk, ?_, fun v => ?_⟩
    · change P.vec e.h = P.vec (P.gens.getD k ⟨[], []⟩).h
      rw [he]
    · change P.dot (P.vec e.f) (P.vec v) = P.dot (P.vec (P.gens.getD k ⟨[], []⟩).f) (P.vec v)
      rw [he]
  | l :: u, hu => sem_step (x := (cwD P e u, u, k))
      (sem_cw e hk he u (fun l' hl' => hu l' (by simp [hl']))) (hu l (by simp))

theorem cw_pack {F : Fd} (hL : LaneOK F P) (e : Refl) (G : List (Nat × Nat))
    (hG : ∀ l < G.length, nthK (0, 0) G l = packR P (P.gens.getD l ⟨[], []⟩)) :
    ∀ u : List Nat, (∀ l ∈ u, l < G.length) → cw F G u (packR P e) = packR P (cwD P e u)
  | [], _ => rfl
  | l :: u, hu => by
    change conjK F (nthK (0, 0) G l) (cw F G u (packR P e)) = _
    rw [hG l (hu l (by simp)), cw_pack hL e G hG u (fun l' hl' => hu l' (by simp [hl']))]
    exact conj_pack hL _ _

theorem ltAll_spec (n : Nat) : ∀ u : List Nat, ltAll n u = true → ∀ l ∈ u, l < n
  | [], _, l, hl => by simp at hl
  | j :: u, h, l, hl => by
    change (Nat.blt j n && ltAll n u) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h.1
    · exact ltAll_spec n u h.2 l hl

theorem wf_extra {P : Pt} (hwf : P.WF) {e : Refl} (he : P.dot (P.vec e.f) (P.vec e.h) = 2) :
    (withExtra P [e]).WF := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hwf r hr
  · rw [List.mem_singleton.mp hr]
    exact he

theorem wfCheck_of_WF {P : Pt} (hp : P.p = 3) [Fact P.p.Prime] (hwf : P.WF) : wfCheck P = true := by
  unfold wfCheck
  rw [List.all_eq_true]
  intro r hr
  rw [beq_iff_eq]
  have h1 := hwf r hr
  rw [← Pt.dotv_spec] at h1
  have h2 : ((2 % P.p : Nat) : ZMod P.p) = 2 := by rw [ZMod.natCast_mod]; rfl
  rw [← h2, ZMod.natCast_eq_natCast_iff'] at h1
  rw [Nat.mod_eq_of_lt (dotv_lt' P (by rw [hp]; norm_num) _ _)] at h1
  rw [h1, Nat.mod_mod]

theorem WF_of_dotv {P : Pt} [Fact P.p.Prime] {r : Refl} (h : P.dotv r.f r.h = 2) :
    P.dot (P.vec r.f) (P.vec r.h) = 2 := by
  rw [← Pt.dotv_spec, h]
  rfl

theorem conj_real {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (hwf : P.WF) (e r : Refl)
    (he : P.dotv e.f e.h = 2) (u : List Nat) (hu : ltAll P.gens.length u = true)
    (h : eqPM (fdB 3 P.D) P.D (cw (fdB 3 P.D) (P.gens.map (packR P)) u (packR P e))
      (packR P r) = true) :
    realizes (withExtra P [e]) (u ++ [P.gens.length] ++ u.reverse) r = true := by
  have hfact : Fact (withExtra P [e]).p.Prime := ⟨by change P.p.Prime; rw [hp]; norm_num⟩
  have hfact0 : Fact P.p.Prime := hfact
  have hwf' := wf_extra hwf (WF_of_dotv he)
  have hL : LaneOK (fdB 3 P.D) (withExtra P [e]) := laneOK_three (P := withExtra P [e]) hp hD
  have hu' := ltAll_spec _ u hu
  have hk : P.gens.length < (withExtra P [e]).gens.length := by simp
  have hke : (withExtra P [e]).gens.getD P.gens.length ⟨[], []⟩ = e := by simp
  have hsem := sem_cw (P := withExtra P [e]) e hk hke u (fun l hl => by
    have := hu' l hl
    simp only [List.length_append, List.length_singleton]
    omega)
  have hG : ∀ l < (P.gens.map (packR P)).length, nthK (0, 0) (P.gens.map (packR P)) l =
      packR (withExtra P [e]) ((withExtra P [e]).gens.getD l ⟨[], []⟩) := by
    intro l hl
    rw [List.length_map] at hl
    rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
    change _ = packR P ((P.gens ++ [e]).getD l ⟨[], []⟩)
    rw [getD_append_left _ _ _ hl, List.getD_eq_getElem _ _ hl]
  have hcw := cw_pack hL e (P.gens.map (packR P)) hG u (by simpa using hu')
  change cw (fdB 3 P.D) (P.gens.map (packR P)) u (packR P e) =
    packR P (cwD (withExtra P [e]) e u) at hcw
  rw [hcw] at h
  unfold eqPM eqP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  change realizes (withExtra P [e]) (sw (cwD (withExtra P [e]) e u, u, P.gens.length)) r = true
  rcases h with h | h
  · have h' : packR P (cwD (withExtra P [e]) e u) = packR P r := Prod.ext h.1 h.2
    obtain ⟨hf, hh⟩ := packR_inj hp h'
    exact real_pos hwf' hsem r hf.symm hh.symm
  · have h' : packR P (cwD (withExtra P [e]) e u) = negP (fdB 3 P.D) P.D (packR P r) :=
      Prod.ext h.1 h.2
    rw [negP_packR hp] at h'
    obtain ⟨hf, hh⟩ := packR_inj hp h'
    change P.vec _ = P.vec (negV P.D r.f) at hf
    change P.vec _ = P.vec (negV P.D r.h) at hh
    rw [vec_negV hp] at hf hh
    refine real_neg hwf' hsem r ?_ ?_
    · change P.vec r.f = -P.vec (cwD (withExtra P [e]) e u).f
      rw [hf, neg_neg]
    · change P.vec r.h = -P.vec (cwD (withExtra P [e]) e u).h
      rw [hh, neg_neg]

theorem allK_spec {α : Type} (p : α → Bool) : ∀ l : List α, allK p l = true ↔ ∀ x ∈ l, p x = true
  | [] => by simp [allK]
  | x :: l => by
    change (p x && allK p l) = true ↔ _
    rw [Bool.and_eq_true, allK_spec p l]
    simp

theorem all2_spec {α β : Type} (f : α → β → Bool) : ∀ (l1 : List α) (l2 : List β),
    all2 f l1 l2 = true → l1.length = l2.length ∧
      ∀ k (h1 : k < l1.length) (h2 : k < l2.length), f l1[k] l2[k] = true
  | [], l2, h => by
    have e : all2 f [] l2 = l2.isEmpty := rfl
    rw [e, List.isEmpty_iff] at h
    subst h
    exact ⟨rfl, fun k h1 => absurd h1 (Nat.not_lt_zero _)⟩
  | x :: xs, [], h => absurd h (by change ¬ false = true; simp)
  | x :: xs, y :: ys, h => by
    change (f x y && all2 f xs ys) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := all2_spec f xs ys h.2
    refine ⟨by simp [hl], fun k h1 h2 => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k => exact hk k (by simpa using h1) (by simpa using h2)

theorem all3_spec {α β γ : Type} (f : α → β → γ → Bool) : ∀ (l1 : List α) (l2 : List β)
    (l3 : List γ), all3 f l1 l2 l3 = true → l1.length = l2.length ∧ l1.length = l3.length ∧
      ∀ k (h1 : k < l1.length) (h2 : k < l2.length) (h3 : k < l3.length),
        f l1[k] l2[k] l3[k] = true
  | [], l2, l3, h => by
    have e : all3 f [] l2 l3 = (l2.isEmpty && l3.isEmpty) := rfl
    rw [e, Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun k h1 => absurd h1 (Nat.not_lt_zero _)⟩
  | x :: xs, [], l3, h => absurd h (by change ¬ false = true; simp)
  | x :: xs, y :: ys, [], h => absurd h (by change ¬ false = true; simp)
  | x :: xs, y :: ys, z :: zs, h => by
    change (f x y z && all3 f xs ys zs) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hl, hl', hk⟩ := all3_spec f xs ys zs h.2
    refine ⟨by simp [hl], by simp [hl'], fun k h1 h2 h3 => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k => exact hk k (by simpa using h1) (by simpa using h2) (by simpa using h3)

@[expose] def Inv (N : Nat) (st : Nat × Nat × Bool) (L : List Nat) : Prop :=
  st.2.2 = true →
    (∀ k, st.1.testBit k = true ↔ k ∈ L) ∧ L.Nodup ∧ (∀ k ∈ L, k < N) ∧ st.2.1 = L.length

theorem inv_init (N : Nat) : Inv N (0, 0, true) [] :=
  fun _ => ⟨by simp, List.nodup_nil, by simp, rfl⟩

theorem addC_inv (N : Nat) : ∀ (cs : List Nat) (st : Nat × Nat × Bool) (L : List Nat),
    Inv N st L → Inv N (addC N cs st) (L ++ cs)
  | [], st, L, h => by
    rw [List.append_nil]
    exact h
  | c :: cs, st, L, h => by
    have e : addC N (c :: cs) st = addC N cs (Nat.lor st.1 (Nat.shiftLeft 1 c), Nat.succ st.2.1,
      st.2.2 && Nat.blt c N && clearB st.1 c) := rfl
    rw [e]
    have := addC_inv N cs (Nat.lor st.1 (Nat.shiftLeft 1 c), Nat.succ st.2.1,
      st.2.2 && Nat.blt c N && clearB st.1 c) (L ++ [c]) (by
      intro hf
      change (st.2.2 && Nat.blt c N && clearB st.1 c) = true at hf
      simp only [Bool.and_eq_true, Nat.blt_eq] at hf
      obtain ⟨⟨hf0, hcN⟩, hcl⟩ := hf
      obtain ⟨hb, hnd, hlt, hcnt⟩ := h hf0
      have hcL : c ∉ L := fun hc => by
        have := (hb c).mpr hc
        rw [clearB_spec hcl] at this
        exact Bool.false_ne_true this
      refine ⟨fun k => ?_, ?_, ?_, ?_⟩
      · change (Nat.lor st.1 (Nat.shiftLeft 1 c)).testBit k = true ↔ _
        rw [testBit_lor_one, Bool.or_eq_true, hb, decide_eq_true_iff, List.mem_append,
          List.mem_singleton]
        exact or_congr_right eq_comm
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton c, ?_⟩
        intro a ha b hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        exact fun hab => hcL (hab ▸ ha)
      · intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact hlt k hk
        · rw [List.mem_singleton.mp hk]
          exact hcN
      · change Nat.succ st.2.1 = (L ++ [c]).length
        rw [List.length_append, List.length_singleton, hcnt])
    rwa [List.append_assoc, List.singleton_append] at this

theorem cover {N : Nat} {L : List Nat} (hnd : L.Nodup) (hlt : ∀ k ∈ L, k < N) (hl : L.length = N) :
    ∀ k < N, k ∈ L := by
  intro k hk
  by_contra hkL
  have hsub : L.toFinset ⊆ (Finset.range N).erase k := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨fun e => hkL (e ▸ hx), hlt x hx⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (Finset.mem_range.mpr hk),
    Finset.card_range] at this
  omega

theorem bkK_spec (F : Fd) (D N : Nat) (R : List (Nat × Nat)) :
    ∀ (bk : List (Nat × List Nat × List Nat)) (prev : Nat) (sf sh : Nat × Nat × Bool)
      (LF LH : List Nat), bkK F D N R bk prev sf sh = true → Inv N sf LF → Inv N sh LH →
      bk.Pairwise (fun a b => a.1 < b.1) ∧ (∀ b ∈ bk, prev ≤ b.1) ∧
      (∀ b ∈ bk, ∀ k ∈ b.2.1, mskF F R (pkrC D k) = b.1) ∧
      (∀ b ∈ bk, ∀ k ∈ b.2.2, mskH F R (pkC D k) = b.1) ∧
      (∀ k < N, k ∈ LF ∨ ∃ b ∈ bk, k ∈ b.2.1) ∧ (∀ k < N, k ∈ LH ∨ ∃ b ∈ bk, k ∈ b.2.2)
  | [], prev, sf, sh, LF, LH, h, hF, hH => by
    change (sf.2.2 && sh.2.2 && Nat.beq sf.2.1 N && Nat.beq sh.2.1 N) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨-, hnF, hlF, hcF⟩ := hF h1
    obtain ⟨-, hnH, hlH, hcH⟩ := hH h2
    refine ⟨List.Pairwise.nil, by simp, by simp, by simp, fun k hk => Or.inl ?_,
      fun k hk => Or.inl ?_⟩
    · exact cover hnF hlF (by omega) k hk
    · exact cover hnH hlH (by omega) k hk
  | b :: bk, prev, sf, sh, LF, LH, h, hF, hH => by
    change (Nat.ble prev b.1 && allK (fun k => Nat.beq (mskF F R (pkrC D k)) b.1) b.2.1 &&
      allK (fun k => Nat.beq (mskH F R (pkC D k)) b.1) b.2.2 &&
      bkK F D N R bk (Nat.succ b.1) (addC N b.2.1 sf) (addC N b.2.2 sh)) = true at h
    simp only [Bool.and_eq_true, Nat.ble_eq, allK_spec, Nat.beq_eq] at h
    obtain ⟨⟨⟨hp, hmF⟩, hmH⟩, hr⟩ := h
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ := bkK_spec F D N R bk _ _ _ _ _ hr
      (addC_inv N _ _ _ hF) (addC_inv N _ _ _ hH)
    refine ⟨List.pairwise_cons.mpr ⟨fun b' hb' => by have := ih2 b' hb'; omega, ih1⟩, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hp
      · have := ih2 b' hb'
        omega
    · intro b' hb' k hk
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hmF k hk
      · exact ih3 b' hb' k hk
    · intro b' hb' k hk
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hmH k hk
      · exact ih4 b' hb' k hk
    · intro k hk
      rcases ih5 k hk with h | ⟨b', hb', hk'⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨b, by simp, h⟩
      · exact Or.inr ⟨b', by simp [hb'], hk'⟩
    · intro k hk
      rcases ih6 k hk with h | ⟨b', hb', hk'⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨b, by simp, h⟩
      · exact Or.inr ⟨b', by simp [hb'], hk'⟩

theorem pw_unique : ∀ {bk : List (Nat × List Nat × List Nat)},
    bk.Pairwise (fun a b => a.1 < b.1) → ∀ {a b}, a ∈ bk → b ∈ bk → a.1 = b.1 → a = b
  | [], _, a, b, ha, _, _ => by simp at ha
  | x :: l, hp, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · rw [h1] at hab
      have := hp.1 b h2
      omega
    · rw [h2] at hab
      have := hp.1 a h1
      omega
    · exact pw_unique hp.2 h1 h2 hab

theorem msk_eq (F : Fd) (f v : Nat) : ∀ R : List (Nat × Nat),
    (∀ r ∈ R, Nat.beq (dotK F f r.1) 0 = Nat.beq (dotK F r.2 v) 0) → mskF F R f = mskH F R v
  | [], _ => rfl
  | r :: R, h => by
    change Nat.add (bif Nat.beq (dotK F f r.1) 0 then 1 else 0) (Nat.mul 2 (mskF F R f)) =
      Nat.add (bif Nat.beq (dotK F r.2 v) 0 then 1 else 0) (Nat.mul 2 (mskH F R v))
    rw [h r (by simp), msk_eq F f v R (fun r' hr' => h r' (by simp [hr']))]

@[expose] noncomputable def prodH (F : Fd) (D f : Nat) (hs : List Nat) : List (Nat × Nat) :=
  (hs.filter fun h => Nat.beq (dotK F f (pkC D h)) 2).map fun h => (pkC D h, f)

theorem matchH_spec (F : Fd) (D f : Nat) : ∀ (hs : List Nat) (st : List (Nat × Nat) × Bool),
    (matchH F D f hs st).2 = true → st.2 = true ∧ st.1 = prodH F D f hs ++ (matchH F D f hs st).1
  | [], st, h => ⟨h, rfl⟩
  | x :: hs, st, h => by
    have hm : matchH F D f (x :: hs) st = bif Nat.beq (dotK F f (pkC D x)) 2 then
        matchH F D f hs (List.rec (motive := fun _ => List (Nat × Nat) × Bool) ([], false)
          (fun e es _ => (es, st.2 && Nat.beq e.1 (pkC D x) && Nat.beq e.2 f)) st.1)
        else matchH F D f hs st := rfl
    rw [hm] at h ⊢
    clear hm
    cases hb : Nat.beq (dotK F f (pkC D x)) 2
    · simp only [hb, cond_false] at h ⊢
      have hp : prodH F D f (x :: hs) = prodH F D f hs := by simp [prodH, hb]
      rw [hp]
      exact matchH_spec F D f hs st h
    · simp only [hb, cond_true] at h ⊢
      have hp : prodH F D f (x :: hs) = (pkC D x, f) :: prodH F D f hs := by simp [prodH, hb]
      rw [hp]
      obtain ⟨l, fl⟩ := st
      cases l with
      | nil =>
        change (matchH F D f hs ([], false)).2 = true at h
        exact absurd (matchH_spec F D f hs _ h).1 (by simp)
      | cons e es =>
        change (matchH F D f hs (es, fl && Nat.beq e.1 (pkC D x) && Nat.beq e.2 f)).2 = true at h
        obtain ⟨h1, h2⟩ := matchH_spec F D f hs _ h
        change (fl && Nat.beq e.1 (pkC D x) && Nat.beq e.2 f) = true at h1
        simp only [Bool.and_eq_true, Nat.beq_eq] at h1
        obtain ⟨⟨hfl, he1⟩, he2⟩ := h1
        refine ⟨hfl, ?_⟩
        change e :: es = (pkC D x, f) :: (prodH F D f hs ++
          (matchH F D f hs (es, fl && Nat.beq e.1 (pkC D x) && Nat.beq e.2 f)).1)
        have hee : e = (pkC D x, f) := Prod.ext he1 he2
        rw [← h2, hee]

@[expose] noncomputable def prodF (F : Fd) (D : Nat) (hs fs : List Nat) : List (Nat × Nat) :=
  fs.flatMap fun k => prodH F D (pkrC D k) hs

theorem matchF_spec (F : Fd) (D : Nat) (hs : List Nat) : ∀ (fs : List Nat)
    (st : List (Nat × Nat) × Bool), (matchF F D hs fs st).2 = true →
      st.2 = true ∧ st.1 = prodF F D hs fs ++ (matchF F D hs fs st).1
  | [], st, h => ⟨h, rfl⟩
  | k :: fs, st, h => by
    change (matchF F D hs fs (matchH F D (pkrC D k) hs st)).2 = true at h
    obtain ⟨h1, h2⟩ := matchF_spec F D hs fs _ h
    obtain ⟨h3, h4⟩ := matchH_spec F D (pkrC D k) hs st h1
    refine ⟨h3, ?_⟩
    change st.1 = prodF F D hs (k :: fs) ++ (matchF F D hs fs (matchH F D (pkrC D k) hs st)).1
    rw [h4, h2]
    simp [prodF, List.flatMap_cons, List.append_assoc]

@[expose] noncomputable def bfold (F : Fd) (D : Nat) (bk : List (Nat × List Nat × List Nat)) :
    List (Nat × Nat) × Bool → List (Nat × Nat) × Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) × Bool → List (Nat × Nat) × Bool)
    (fun st => st) (fun b _ ih st => ih (matchF F D b.2.2 b.2.1 st)) bk

@[expose] noncomputable def prodB (F : Fd) (D : Nat) (bk : List (Nat × List Nat × List Nat)) :
    List (Nat × Nat) :=
  bk.flatMap fun b => prodF F D b.2.2 b.2.1

theorem bfold_spec (F : Fd) (D : Nat) : ∀ (bk : List (Nat × List Nat × List Nat))
    (st : List (Nat × Nat) × Bool), (bfold F D bk st).2 = true →
      st.2 = true ∧ st.1 = prodB F D bk ++ (bfold F D bk st).1
  | [], st, h => ⟨h, rfl⟩
  | b :: bk, st, h => by
    change (bfold F D bk (matchF F D b.2.2 b.2.1 st)).2 = true at h
    obtain ⟨h1, h2⟩ := bfold_spec F D bk _ h
    obtain ⟨h3, h4⟩ := matchF_spec F D b.2.2 b.2.1 st h1
    refine ⟨h3, ?_⟩
    change st.1 = prodB F D (b :: bk) ++ (bfold F D bk (matchF F D b.2.2 b.2.1 st)).1
    rw [h4, h2]
    simp [prodB, List.flatMap_cons, List.append_assoc]

theorem candOK_spec {F : Fd} {D : Nat} {bk : List (Nat × List Nat × List Nat)}
    {cd : List (Nat × Nat)} (h : candOK F D bk cd = true) : cd = prodB F D bk := by
  have e : candOK F D bk cd =
      ((bfold F D bk (cd, true)).2 && (bfold F D bk (cd, true)).1.isEmpty) := rfl
  rw [e, Bool.and_eq_true, List.isEmpty_iff] at h
  have := (bfold_spec F D bk (cd, true) h.1).2
  rw [h.2, List.append_nil] at this
  exact this

theorem mem_prodB_of {F : Fd} {D : Nat} {bk : List (Nat × List Nat × List Nat)}
    {b : Nat × List Nat × List Nat} {kf kh : Nat} (hb : b ∈ bk) (hkf : kf ∈ b.2.1)
    (hkh : kh ∈ b.2.2) (hd : Nat.beq (dotK F (pkrC D kf) (pkC D kh)) 2 = true) :
    (pkC D kh, pkrC D kf) ∈ prodB F D bk :=
  List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨kf, hkf,
    List.mem_map.mpr ⟨kh, List.mem_filter.mpr ⟨hkh, hd⟩, rfl⟩⟩⟩

theorem of_mem_prodB {F : Fd} {D : Nat} {bk : List (Nat × List Nat × List Nat)}
    {x : Nat × Nat} (hx : x ∈ prodB F D bk) :
    ∃ kf kh, Nat.beq (dotK F (pkrC D kf) (pkC D kh)) 2 = true ∧ x = (pkC D kh, pkrC D kf) := by
  obtain ⟨b, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨kf, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨kh, hkh, rfl⟩ := List.mem_map.mp hx
  exact ⟨kf, kh, (List.mem_filter.mp hkh).2, rfl⟩

theorem clo_spec [Fact P.p.Prime] {F : Fd} (hL : LaneOK F P) (clo : List (Nat × Nat × Nat × Nat))
    (h : cloP F P.gens.length (P.gens.map (packR P)) clo P.gens.length 0
      (P.gens.map (packR P) ++ clo.map ent) = true) :
    (cloD P (baseD P) clo).map (fun x => packR P x.1) = P.gens.map (packR P) ++ clo.map ent ∧
      ∀ x ∈ cloD P (baseD P) clo, Sem P x := by
  have e1 : (baseD P).length = P.gens.length := by simp [baseD]
  have hclo' : cloP F P.gens.length (P.gens.map (packR P)) clo (baseD P).length 0
      ((P.gens.map (packR P) ++ clo.map ent).drop 0) = true := by
    rw [e1, List.drop_zero]
    exact h
  have hacc : (baseD P).map (fun x => packR P x.1) =
      (P.gens.map (packR P) ++ clo.map ent).take (baseD P).length := by
    rw [e1, List.take_left' (by simp)]
    apply List.ext_getElem (by simp [baseD])
    intro i h1 h2
    simp only [baseD, List.length_map, List.length_range] at h1
    simp [baseD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hdrop : (P.gens.map (packR P) ++ clo.map ent).drop (baseD P).length =
      clo.map ent ++ [] := by
    rw [e1, List.append_nil, List.drop_left' (by simp)]
  obtain ⟨hDl, hsem⟩ := cloP_spec hL _ clo (baseD P) 0 [] hclo' (Nat.zero_le _) hacc hdrop
    sem_base
  refine ⟨?_, hsem⟩
  rw [hDl, List.take_of_length_le]
  simp [e1]

theorem gensK_eq {P : Pt} (hp : P.p = 3) : gensK P = P.gens.map (packR P) := by
  unfold gensK
  apply List.map_congr_left
  intro g _
  rw [packR3 hp]

theorem cand_mem {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) {ys : List Refl}
    {bk : List (Nat × List Nat × List Nat)} {cd : List (Nat × Nat)}
    (hbk : bkK (fdB 3 P.D) P.D (Nat.pow 3 P.D) (ys.map (packR P)) bk 0 (0, 0, true)
      (0, 0, true) = true)
    (hcd : candOK (fdB 3 P.D) P.D bk cd = true) {c : Refl} (hc : c ∈ candList P ys) :
    decR P.D (packR P c) = c ∧ packR P c ∈ cd := by
  unfold candList at hc
  simp only [List.mem_flatMap, List.mem_map, List.mem_filterMap] at hc
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := hc
  split at hab
  case isFalse => exact absurd hab (by simp)
  case isTrue hcond =>
  obtain rfl := Option.some.inj hab
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨hm, hd2⟩ := hcond
  rw [hp] at hd2
  rw [hp] at ha hb
  obtain ⟨ka, hka, rfl⟩ := mem_allVecsP _ a ha
  obtain ⟨kb, hkb, rfl⟩ := mem_allVecsP _ b hb
  obtain ⟨hpw, -, hmF, hmH, hcF, hcH⟩ := bkK_spec _ _ _ _ bk 0 _ _ [] [] hbk (inv_init _)
    (inv_init _)
  obtain ⟨b1, hb1, hk1⟩ := (hcF ka hka).resolve_left (by simp)
  obtain ⟨b2, hb2, hk2⟩ := (hcH kb hkb).resolve_left (by simp)
  have e1 := hmF b1 hb1 ka hk1
  have e2 := hmH b2 hb2 kb hk2
  have e3 : mskF (fdB 3 P.D) (ys.map (packR P)) (pkrC P.D ka) =
      mskH (fdB 3 P.D) (ys.map (packR P)) (pkC P.D kb) := by
    apply msk_eq
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hρ
    have := congrArg (fun l => l.getD i false) hm
    simp only [maskF, maskH, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at this
    rw [packR3 hp, pkrC_dig, pkC_dig]
    simp only [dotK_pk hp hD]
    rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq, ← beq_iff_eq, this, beq_iff_eq]
  have hb12 : b1 = b2 := pw_unique hpw hb1 hb2 (by rw [← e1, ← e2, e3])
  subst hb12
  refine ⟨decR_packR_self hp (dig_length _ _) (dig_length _ _) (dig_lt _ _) (dig_lt _ _), ?_⟩
  rw [candOK_spec hcd]
  have hmem := mem_prodB_of (F := fdB 3 P.D) (D := P.D) hb1 hk1 hk2 (by
    rw [pkrC_dig, pkC_dig, dotK_pk hp hD, hd2]
    rfl)
  rw [pkC_dig, pkrC_dig] at hmem
  rw [packR3 hp]
  exact hmem

theorem cd_entry {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) {bk : List (Nat × List Nat × List Nat)}
    {cd : List (Nat × Nat)} (hcd : candOK (fdB 3 P.D) P.D bk cd = true) {x : Nat × Nat}
    (hx : x ∈ cd) : packR P (decR P.D x) = x ∧ P.dotv (decR P.D x).f (decR P.D x).h = 2 := by
  rw [candOK_spec hcd] at hx
  obtain ⟨kf, kh, hd, rfl⟩ := of_mem_prodB hx
  have e : (pkC P.D kh, pkrC P.D kf) = packR P ⟨dig P.D kf, dig P.D kh⟩ := by
    rw [packR3 hp, pkC_dig, pkrC_dig]
  rw [e, decR_packR_self hp (dig_length _ _) (dig_length _ _) (dig_lt _ _) (dig_lt _ _)]
  refine ⟨rfl, ?_⟩
  rw [pkrC_dig, pkC_dig, dotK_pk hp hD, Nat.beq_eq] at hd
  exact hd

@[expose] noncomputable def rt (P : Pt) (x : CE) : Root := ⟨decR P.D (packR P x.1), sw x⟩

@[expose] noncomputable def rtN (P : Pt) (x : CE) : Root :=
  ⟨decR P.D (packR P (negRf P.D x.1)), sw x⟩

@[expose] noncomputable def ob1 (D : Nat) (cd : List (Nat × Nat)) (tg : List (List Nat)) :
    List OEnt :=
  (cd.zip tg).flatMap fun ct => match ct.2 with
    | [] => []
    | j :: u => [⟨decR D ct.1, u, j⟩]

@[expose] noncomputable def ob2 (D : Nat) (cd : List (Nat × Nat))
    (tg : List (Nat × Nat × List Nat)) : List OEnt :=
  (cd.zip tg).flatMap fun ct => bif Nat.beq ct.2.1 2 then [⟨decR D ct.1, ct.2.2.2, ct.2.2.1⟩] else []

open Classical in
@[expose] noncomputable def kd (P : Pt) (bnd t : Nat) : RKind :=
  if t = 0 then (if h : ∃ w, verifyO P w bnd = true then .bad (Classical.choose h) else .bad ⟨[]⟩)
  else (if h : ∃ c, verifyWPos P c = true then .good (Classical.choose h) else .bad ⟨[]⟩)

open Classical in
@[expose] noncomputable def ow (P : Pt) (bnd : Nat) : OWit :=
  if h : ∃ w, verifyO P w bnd = true then Classical.choose h else ⟨[]⟩

@[expose] noncomputable def mkRep (P : Pt) (cd : List (Nat × Nat)) (rp : RXK.Rep) :
    ReflExt.Rep :=
  { r := decR P.D rp.1
    kind := kd (withExtra P [decR P.D rp.1]) P.bound rp.2.1.2.1
    maximal := Nat.beq rp.2.2.1 1
    roots := (cloD (withExtra P [decR P.D rp.1]) (baseD (withExtra P [decR P.D rp.1]))
      rp.2.2.2.1).flatMap fun x => [rt (withExtra P [decR P.D rp.1]) x,
        rtN (withExtra P [decR P.D rp.1]) x]
    reps2 := rp.2.2.2.2.1.map fun q =>
      ⟨decR P.D q.1, ow (withExtra P [decR P.D rp.1, decR P.D q.1]) P.bound⟩
    orb2 := ob2 P.D cd rp.2.2.2.2.2 }

theorem kd_bad {P : Pt} {bnd t : Nat} (ht : t = 0) (h : ∃ w, verifyO P w bnd = true) :
    ∃ w, kd P bnd t = .bad w ∧ verifyO P w bnd = true := by
  unfold kd
  rw [if_pos ht, dif_pos h]
  exact ⟨_, rfl, Classical.choose_spec h⟩

theorem kd_good {P : Pt} {bnd t : Nat} (ht : t ≠ 0) (h : ∃ c, verifyWPos P c = true) :
    ∃ c, kd P bnd t = .good c ∧ verifyWPos P c = true := by
  unfold kd
  rw [if_neg ht, dif_pos h]
  exact ⟨_, rfl, Classical.choose_spec h⟩

theorem ow_spec {P : Pt} {bnd : Nat} (h : ∃ w, verifyO P w bnd = true) :
    verifyO P (ow P bnd) bnd = true := by
  unfold ow
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem mem_ob1 {D : Nat} {cd : List (Nat × Nat)} {tg : List (List Nat)} {i : Nat}
    (h1 : i < cd.length) (h2 : i < tg.length) {j : Nat} {u : List Nat} (ht : tg[i] = j :: u) :
    (⟨decR D cd[i], u, j⟩ : OEnt) ∈ ob1 D cd tg := by
  unfold ob1
  refine List.mem_flatMap.mpr ⟨(cd[i], tg[i]), List.mem_iff_getElem.mpr
    ⟨i, by simp [h1, h2], by simp⟩, ?_⟩
  simp only [ht]
  simp

theorem of_mem_ob1 {D : Nat} {cd : List (Nat × Nat)} {tg : List (List Nat)} {e : OEnt}
    (he : e ∈ ob1 D cd tg) : ∃ i, ∃ (h1 : i < cd.length) (h2 : i < tg.length), ∃ j u,
      tg[i] = j :: u ∧ e = ⟨decR D cd[i], u, j⟩ := by
  unfold ob1 at he
  obtain ⟨ct, hct, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hct
  rw [List.length_zip] at hi
  have h1 : i < cd.length := by omega
  have h2 : i < tg.length := by omega
  refine ⟨i, h1, h2, ?_⟩
  simp only [List.getElem_zip] at he
  rcases ht : tg[i] with _ | ⟨j, u⟩
  · rw [ht] at he
    simp at he
  · rw [ht] at he
    exact ⟨j, u, rfl, List.mem_singleton.mp he⟩

theorem mem_ob2 {D : Nat} {cd : List (Nat × Nat)} {tg : List (Nat × Nat × List Nat)} {i : Nat}
    (h1 : i < cd.length) (h2 : i < tg.length) {k : Nat} {w : List Nat}
    (ht : tg[i] = (2, k, w)) : (⟨decR D cd[i], w, k⟩ : OEnt) ∈ ob2 D cd tg := by
  unfold ob2
  refine List.mem_flatMap.mpr ⟨(cd[i], tg[i]), List.mem_iff_getElem.mpr
    ⟨i, by simp [h1, h2], by simp⟩, ?_⟩
  simp only [ht]
  simp

theorem of_mem_ob2 {D : Nat} {cd : List (Nat × Nat)} {tg : List (Nat × Nat × List Nat)}
    {e : OEnt} (he : e ∈ ob2 D cd tg) : ∃ i, ∃ (h1 : i < cd.length) (h2 : i < tg.length), ∃ k w,
      tg[i] = (2, k, w) ∧ e = ⟨decR D cd[i], w, k⟩ := by
  unfold ob2 at he
  obtain ⟨ct, hct, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hct
  rw [List.length_zip] at hi
  have h1 : i < cd.length := by omega
  have h2 : i < tg.length := by omega
  refine ⟨i, h1, h2, ?_⟩
  simp only [List.getElem_zip] at he
  rcases ht : tg[i] with ⟨t0, k, w⟩
  rw [ht] at he
  cases hb : Nat.beq t0 2
  · simp [hb] at he
  · simp only [hb, cond_true, List.mem_singleton] at he
    rw [Nat.eq_of_beq_eq_true hb]
    exact ⟨k, w, rfl, he⟩

theorem reqb_self (c : Refl) : reqb c c = true := by
  unfold reqb
  simp

theorem withExtra_two (P : Pt) (x y : Refl) : withExtra (withExtra P [x]) [y] = withExtra P [x, y] := by
  simp only [withExtra, List.append_assoc, List.singleton_append]

theorem wfR_of_dotv {P : Pt} (hp : P.p = 3) {r : Refl} (h : P.dotv r.f r.h = 2) :
    wfR P r = true := by
  unfold wfR
  rw [h, hp]
  rfl

theorem wfR_of_dot {P : Pt} (hp : P.p = 3) [Fact P.p.Prime] {r : Refl}
    (h : P.dot (P.vec r.f) (P.vec r.h) = 2) : wfR P r = true := by
  have := wfCheck_of_WF (P := { P with gens := [r] }) hp (by
    intro s hs
    rw [List.mem_singleton.mp hs]
    exact h)
  unfold wfCheck at this
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at this
  have h2 : P.dotv r.f r.h = 2 % P.p := this
  unfold wfR
  rw [h2]
  simp

theorem rep_facts {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) [Fact P.p.Prime] (hWF : P.WF)
    {a : Nat × Nat} {o : ORec} (hca : canP P.D a = true) (hrf : reflOK (fdB 3 P.D) a = true)
    (hok : oK (fdB 3 P.D) P.D P.bound (P.gens.map (packR P) ++ [a]) o = true) :
    packR P (decR P.D a) = a ∧ P.dotv (decR P.D a).f (decR P.D a).h = 2 ∧
      (withExtra P [decR P.D a]).WF ∧
      (o.2.1 = 0 → ∃ w, verifyO (withExtra P [decR P.D a]) w P.bound = true) ∧
      (o.2.1 ≠ 0 → ∃ c, verifyWPos (withExtra P [decR P.D a]) c = true) := by
  have hr := packR_decR hp hca
  have hd : P.dotv (decR P.D a).f (decR P.D a).h = 2 := by
    rw [← hr, packR3 hp, reflOK_pk hp hD] at hrf
    exact hrf
  have hWF1 := wf_extra hWF (WF_of_dotv hd)
  have hfact : Fact (withExtra P [decR P.D a]).p.Prime := inferInstanceAs (Fact P.p.Prime)
  have hwf1 := wfCheck_of_WF (P := withExtra P [decR P.D a]) hp hWF1
  have hL := laneOK_three (P := withExtra P [decR P.D a]) hp hD
  have hg : ((withExtra P [decR P.D a]).gens.map fun g =>
      (pkP (withExtra P [decR P.D a]).p (withExtra P [decR P.D a]).D g.h,
        pkrP (withExtra P [decR P.D a]).p (withExtra P [decR P.D a]).D g.f)) =
      P.gens.map (packR P) ++ [a] := by
    change (P.gens ++ [decR P.D a]).map (packR P) = _
    rw [List.map_append, List.map_singleton, hr]
  have := oK_verify (P := withExtra P [decR P.D a]) (bnd := P.bound) (o := o)
    (by change P.p.Prime; rw [hp]; norm_num) (by change 3 ≤ P.p; omega)
    (by change P.p < 65536; omega) hL hwf1 (by rw [hg]; exact hok)
  exact ⟨hr, hd, hWF1, this⟩

theorem tag1_cons {F : Fd} {D n X : Nat} {G : List (Nat × Nat)} {R1 : List RXK.Rep}
    {c : Nat × Nat} {j : Nat} {u : List Nat} (h : tag1 F D n X G R1 c (j :: u) = true) :
    j < R1.length ∧ ltAll n u = true ∧ eqPM F D (cw F G u c) (nthK rep0 R1 j).1 = true := by
  unfold tag1 at h
  cases hb : Nat.beq (dotK F c.2 X) 0
  · simp only [hb, cond_false] at h
    change (Nat.blt j R1.length && ltAll n u && eqPM F D (cw F G u c) (nthK rep0 R1 j).1) = true
      at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · simp only [hb, cond_true] at h
    simp at h

theorem tag1_moving {F : Fd} {D n X : Nat} {G : List (Nat × Nat)} {R1 : List RXK.Rep}
    {c : Nat × Nat} {t : List Nat} (h : tag1 F D n X G R1 c t = true) (hm : dotK F c.2 X ≠ 0) :
    ∃ j u, t = j :: u := by
  unfold tag1 at h
  have hb : Nat.beq (dotK F c.2 X) 0 = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hm (Nat.eq_of_beq_eq_true h')
  simp only [hb, cond_false] at h
  cases t with
  | nil => exact absurd h Bool.false_ne_true
  | cons j u => exact ⟨j, u, rfl⟩

theorem tag2_cases {F : Fd} {D n1 nC2 mx : Nat} {G1 C2 : List (Nat × Nat)}
    {Q : List ((Nat × Nat) × ORec)} {R1 : List RXK.Rep} {c : Nat × Nat} {t1 : List Nat}
    {t0 k : Nat} {w : List Nat} (h : tag2 F D n1 nC2 mx G1 C2 Q R1 c t1 (t0, k, w) = true) :
    (t0 = 0 ∧ k < nC2 ∧ eqPM F D c (nthK (0, 0) C2 k) = true) ∨
    (t0 = 1 ∧ k < nC2 ∧ bne (Nat.beq (dotK F c.2 (nthK (0, 0) C2 k).1) 0)
      (Nat.beq (dotK F (nthK (0, 0) C2 k).2 c.1) 0) = true) ∨
    (t0 = 2 ∧ k < Q.length ∧ ltAll n1 w = true ∧
      eqPM F D (cw F G1 w c) (nthK ((0, 0), ([], 0, 0, [], [], [], [])) Q k).1 = true) ∨
    (t0 = 3 ∧ mx = 0 ∧ ∃ j u, t1 = j :: u ∧ j < R1.length ∧ goodMax (nthK rep0 R1 j) = true) := by
  match t0, h with
  | 0, h =>
    have h' : (Nat.blt k nC2 && eqPM F D c (nthK (0, 0) C2 k)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inl ⟨rfl, h'⟩
  | 1, h =>
    have h' : (Nat.blt k nC2 && bne (Nat.beq (dotK F c.2 (nthK (0, 0) C2 k).1) 0)
        (Nat.beq (dotK F (nthK (0, 0) C2 k).2 c.1) 0)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inr (Or.inl ⟨rfl, h'⟩)
  | 2, h =>
    have h' : (Nat.blt k Q.length && ltAll n1 w && eqPM F D (cw F G1 w c)
        (nthK ((0, 0), ([], 0, 0, [], [], [], [])) Q k).1) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inr (Or.inr (Or.inl ⟨rfl, h'.1.1, h'.1.2, h'.2⟩))
  | 3, h =>
    have h' : (Nat.beq 3 3 && Nat.beq mx 0 && List.rec (motive := fun _ => Bool) false
        (fun j _ _ => Nat.blt j R1.length && goodMax (nthK rep0 R1 j)) t1) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    refine Or.inr (Or.inr (Or.inr ⟨rfl, h'.1.2, ?_⟩))
    cases t1 with
    | nil => exact absurd h'.2 Bool.false_ne_true
    | cons j u =>
      have h2 : (Nat.blt j R1.length && goodMax (nthK rep0 R1 j)) = true := h'.2
      simp only [Bool.and_eq_true, Nat.blt_eq] at h2
      exact ⟨j, u, rfl, h2⟩
  | t0 + 4, h =>
    have h' : (Nat.beq (t0 + 4) 3 && Nat.beq mx 0 && List.rec (motive := fun _ => Bool) false
        (fun j _ _ => Nat.blt j R1.length && goodMax (nthK rep0 R1 j)) t1) = true := h
    have e : Nat.beq (t0 + 4) 3 = false := by
      rw [Bool.eq_false_iff]
      intro e
      have := Nat.eq_of_beq_eq_true e
      omega
    rw [e] at h'
    exact absurd h' (by simp)

theorem nthK_map {α β : Type} (d : β) (f : α → β) {l : List α} {k : Nat} (hk : k < l.length) :
    nthK d (l.map f) k = f l[k] := by
  rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem dot_neg_neg {P : Pt} (a b : P.V) : P.dot (-a) (-b) = P.dot a b := by
  simp [Pt.dot]

theorem nbeq (x y : Nat) : Nat.beq x y = (x == y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

end Snd

open Snd (decR) in
theorem frameK_verify (P : Pt) (d : FD) (h : frameK P d = true) (hc : canK P d = true) :
    ∃ T, verifyAll P T = true := by
  obtain ⟨rows, bk, cd, tg1, R1⟩ := d
  unfold frameK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb, hcd⟩, ht1⟩, hrep⟩, hs2⟩ := h
  unfold baseK ptF at hb
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hp, -⟩, hD7⟩, hrefl⟩, hclo⟩, hX⟩, hbk⟩ := hb
  have hD : P.D ≤ 10 := by omega
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  change candOK (fdB 3 P.D) P.D bk cd = true at hcd
  change all2 (tag1 (fdB 3 P.D) P.D (gensK P).length (pk P.D P.x) (gensK P) R1) cd tg1 = true
    at ht1
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
    oK (fdB 3 P.D) P.D P.bound (gensK P ++ [rp.1]) rp.2.1) R1 = true at hrep
  change allK (s2 (fdB 3 P.D) P.D P.bound (gensK P) cd tg1 R1) R1 = true at hs2
  change allK (fun rp => canP P.D rp.1 && allK (fun q => canP P.D q.1) rp.2.2.2.2.1) R1 = true
    at hc
  rw [Snd.gensK_eq hp] at hrefl hclo hX hbk ht1 hrep hs2
  have hrefl' := (Snd.allK_spec _ _).mp hrefl
  have hWF : P.WF := by
    intro g hg
    have := hrefl' (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [Snd.packR3 hp, reflOK_pk hp hD] at this
    exact Snd.WF_of_dotv this
  have hwfP := Snd.wfCheck_of_WF hp hWF
  have hL := laneOK_three hp hD
  rw [List.length_map] at hclo
  obtain ⟨hDl, hsem⟩ := Snd.clo_spec hL rows hclo
  have hC : (P.gens.map (packR P) ++ rows.map fun e => (e.2.2.1, e.2.2.2)) =
      ((cloD P (baseD P) rows).map fun x => decR P.D (packR P x.1)).map (packR P) := by
    refine hDl.symm.trans ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact (Snd.packR_decR hp (Snd.canP_packR hp x.1)).symm
  rw [hC] at hX hbk
  set Dl := cloD P (baseD P) rows with hDl_def
  set ys := Dl.map fun x => decR P.D (packR P x.1) with hys
  set T : Tables := ⟨Dl.map (Snd.rt P), Snd.ob1 P.D cd tg1, R1.map (Snd.mkRep P cd)⟩ with hT
  have eRr : T.roots.map (·.r) = ys := by
    change (Dl.map (Snd.rt P)).map (·.r) = ys
    rw [List.map_map]
    rfl
  have hcandL : ∀ c ∈ candOf P T, decR P.D (packR P c) = c ∧ packR P c ∈ cd := by
    intro c hc'
    unfold candOf at hc'
    rw [eRr] at hc'
    exact Snd.cand_mem hp hD hbk hcd hc'
  have hcdE : ∀ x ∈ cd, packR P (decR P.D x) = x ∧ P.dotv (decR P.D x).f (decR P.D x).h = 2 :=
    fun x hx => Snd.cd_entry hp hD hcd hx
  obtain ⟨hl1, ht1i⟩ := Snd.all2_spec _ cd tg1 ht1
  have hcanR : ∀ rp ∈ R1, canP P.D rp.1 = true ∧ ∀ q ∈ rp.2.2.2.2.1, canP P.D q.1 = true := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp hc rp hrp
    rw [Bool.and_eq_true, Snd.allK_spec] at this
    exact this
  have hrepR : ∀ rp ∈ R1, reflOK (fdB 3 P.D) rp.1 = true ∧
      oK (fdB 3 P.D) P.D P.bound (P.gens.map (packR P) ++ [rp.1]) rp.2.1 = true := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp hrep rp hrp
    simpa only [Bool.and_eq_true] using this
  have hfacts := fun rp (hrp : rp ∈ R1) =>
    Snd.rep_facts hp hD hWF (hcanR rp hrp).1 (hrepR rp hrp).1 (hrepR rp hrp).2
  have hTr : ∀ j (hj : j < R1.length), T.reps[j]? = some (Snd.mkRep P cd R1[j]) := by
    intro j hj
    change (R1.map (Snd.mkRep P cd))[j]? = _
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl
  have hTrl : T.reps.length = R1.length := by
    change (R1.map (Snd.mkRep P cd)).length = _
    rw [List.length_map]
  have hgm : ∀ j (hj : j < R1.length), goodMax (nthK rep0 R1 j) = true →
      (Snd.mkRep P cd R1[j]).isGoodMax = true := by
    intro j hj hg
    rw [nthK_eq', List.getD_eq_getElem _ _ hj] at hg
    unfold goodMax at hg
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hg
    obtain ⟨-, -, -, -, hokG⟩ := hfacts _ (List.getElem_mem hj)
    obtain ⟨c, hkc, -⟩ := Snd.kd_good (t := R1[j].2.1.2.1) (by omega) (hokG (by omega))
    unfold CFSG.ReflExt.Rep.isGoodMax
    have hk : (Snd.mkRep P cd R1[j]).kind = .good c := hkc
    rw [hk]
    change Nat.beq R1[j].2.2.1 1 = true
    rw [hg.2]
    rfl
  have hv1 : vRoots P T = true := by
    unfold vRoots
    rw [List.all_eq_true]
    intro ρ hρ
    have hρ' : ρ ∈ Dl.map (Snd.rt P) := hρ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hρ'
    obtain ⟨hf, hh⟩ := Snd.vec_decR hp x.1
    have h2 := Snd.sem_wf hWF (hsem x hx)
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨Snd.wfR_of_dot hp ?_, Snd.real_pos hWF (hsem x hx) _ hf hh⟩, ?_⟩
    · change P.dot (P.vec (decR P.D (packR P x.1)).f) (P.vec (decR P.D (packR P x.1)).h) = 2
      rw [hf, hh]
      exact h2
    · have := (Snd.allK_spec _ _).mp hX (packR P (decR P.D (packR P x.1)))
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
      change P.dotv (decR P.D (packR P x.1)).f P.x = 0
      generalize decR P.D (packR P x.1) = y at this ⊢
      rw [Snd.packR3 hp, Nat.beq_eq] at this
      exact (dotK_pk hp hD y.f P.x).symm.trans this
  have hv2 : vCover P T (candOf P T) = true := by
    unfold vCover movingOf
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hmv⟩ := hc'
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    have hi' : i < tg1.length := by omega
    have ht := ht1i i hi hi'
    rw [hci] at ht
    obtain ⟨j, u, hju⟩ := Snd.tag1_moving ht (by
      simp only [Snd.packR3 hp, dotK_pk hp hD]
      simpa using hmv)
    rw [List.any_eq_true]
    refine ⟨⟨decR P.D cd[i], u, j⟩, Snd.mem_ob1 hi hi' hju, ?_⟩
    change reqb (decR P.D cd[i]) c = true
    rw [hci, hdc]
    exact Snd.reqb_self c
  have hv3 : T.orb1.all (entryOK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ Snd.ob1 P.D cd tg1 := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := Snd.of_mem_ob1 he'
    have ht := ht1i i hi hi'
    rw [hju] at ht
    obtain ⟨hj, hu, heq⟩ := Snd.tag1_cons ht
    obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
    obtain ⟨hpr, -⟩ := hfacts _ (List.getElem_mem hj)
    unfold entryOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨Snd.wfR_of_dotv hp hde, by rw [hTrl]; exact hj⟩, ?_⟩
    rw [hTr j hj]
    change realizes (withExtra P [decR P.D cd[i]]) (u ++ [P.gens.length] ++ u.reverse)
      (decR P.D R1[j].1) = true
    apply Snd.conj_real hp hD hWF _ _ hde u (by simpa using hu)
    rw [hpe, hpr]
    rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
    exact heq
  have hv4 : T.reps.all (verifyRep P T (candOf P T)) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ R1.map (Snd.mkRep P cd) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hca, hcaQ⟩ := hcanR rp hrp
    obtain ⟨hr, hd2, hWF1, hokB, hokG⟩ := hfacts rp hrp
    have hs2r := (Snd.allK_spec _ _).mp hs2 rp hrp
    obtain ⟨a, o, mx, ro, Qs, tg2⟩ := rp
    dsimp only at hca hcaQ hr hd2 hWF1 hokB hokG hs2r
    have hfact1 : Fact (withExtra P [decR P.D a]).p.Prime := hfact
    have hwf1 := Snd.wfCheck_of_WF (P := withExtra P [decR P.D a]) hp hWF1
    unfold verifyRep
    simp only [Bool.and_eq_true]
    refine ⟨⟨Snd.wfR_of_dotv hp hd2, hwf1⟩, ?_⟩
    by_cases ht : o.2.1 = 0
    · obtain ⟨w, hkw, hw⟩ := Snd.kd_bad ht (hokB ht)
      have hk : (Snd.mkRep P cd (a, o, mx, ro, Qs, tg2)).kind = .bad w := hkw
      rw [hk]
      exact hw
    obtain ⟨c, hkc, hcw⟩ := Snd.kd_good ht (hokG ht)
    have hk : (Snd.mkRep P cd (a, o, mx, ro, Qs, tg2)).kind = .good c := hkc
    rw [hk]
    change (verifyWPos (withExtra P [decR P.D a]) c &&
      verifyStage2 P T (candOf P T) (Snd.mkRep P cd (a, o, mx, ro, Qs, tg2))) = true
    rw [hcw, Bool.true_and]
    unfold s2 at hs2r
    have hb0 : Nat.beq o.2.1 0 = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact ht (Nat.eq_of_beq_eq_true h')
    simp only [hb0, cond_false, Bool.and_eq_true, Nat.ble_eq] at hs2r
    obtain ⟨⟨⟨-, hclo2⟩, hQ⟩, hall3⟩ := hs2r
    have hG1 : (withExtra P [decR P.D a]).gens.map (packR (withExtra P [decR P.D a])) =
        P.gens.map (packR P) ++ [a] := by
      change (P.gens ++ [decR P.D a]).map (packR P) = _
      rw [List.map_append, List.map_singleton, hr]
    rw [← hG1] at hclo2 hQ hall3
    rw [List.length_map] at hclo2
    have hL1 := laneOK_three (P := withExtra P [decR P.D a]) hp hD
    obtain ⟨hDl2, hsem2⟩ := Snd.clo_spec hL1 ro hclo2
    set P1 := withExtra P [decR P.D a] with hP1
    set Dl2 := cloD P1 (baseD P1) ro with hDl2_def
    have hC2 : (P1.gens.map (packR P1) ++ ro.map fun e => (e.2.2.1, e.2.2.2)) =
        Dl2.map (fun x => packR P1 x.1) := hDl2.symm
    rw [hC2] at hall3
    have hlen2 : Nat.add (P1.gens.map (packR P1)).length ro.length = Dl2.length := by
      have := congrArg List.length hDl2
      simp only [List.length_map, List.length_append] at this
      rw [List.length_map]
      exact this.symm
    rw [hlen2] at hall3
    obtain ⟨hl12, hl13, hall⟩ := Snd.all3_spec _ cd tg1 tg2 hall3
    unfold verifyStage2
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    ·
      unfold s2Roots
      rw [List.all_eq_true]
      intro ρ hρ
      have hρ' : ρ ∈ Dl2.flatMap (fun x => [Snd.rt P1 x, Snd.rtN P1 x]) := hρ
      obtain ⟨x, hx, hρ⟩ := List.mem_flatMap.mp hρ'
      have hs := hsem2 x hx
      have h2 := Snd.sem_wf hWF1 hs
      rw [Bool.and_eq_true]
      rcases List.mem_cons.mp hρ with rfl | hρ
      · obtain ⟨hf, hh⟩ := Snd.vec_decR (P := P1) hp x.1
        refine ⟨Snd.wfR_of_dot (P := P1) hp ?_, Snd.real_pos hWF1 hs _ hf hh⟩
        change P1.dot (P1.vec (decR P1.D (packR P1 x.1)).f)
          (P1.vec (decR P1.D (packR P1 x.1)).h) = 2
        rw [hf, hh]
        exact h2
      · rw [List.mem_singleton] at hρ
        subst hρ
        obtain ⟨hf, hh⟩ := Snd.vec_decR (P := P1) hp (Snd.negRf P1.D x.1)
        have hf' : P1.vec (decR P1.D (packR P1 (Snd.negRf P1.D x.1))).f = -P1.vec x.1.f := by
          rw [hf]
          exact Snd.vec_negV (P := P1) hp x.1.f
        have hh' : P1.vec (decR P1.D (packR P1 (Snd.negRf P1.D x.1))).h = -P1.vec x.1.h := by
          rw [hh]
          exact Snd.vec_negV (P := P1) hp x.1.h
        refine ⟨Snd.wfR_of_dot (P := P1) hp ?_, Snd.real_neg hWF1 hs _ hf' hh'⟩
        change P1.dot (P1.vec (decR P1.D (packR P1 (Snd.negRf P1.D x.1))).f)
          (P1.vec (decR P1.D (packR P1 (Snd.negRf P1.D x.1))).h) = 2
        rw [hf', hh', Snd.dot_neg_neg]
        exact h2
    ·
      unfold s2Reps
      rw [List.all_eq_true]
      intro q' hq'
      have hq'' : q' ∈ Qs.map (fun q => (⟨decR P.D q.1,
          Snd.ow (withExtra P [decR P.D a, decR P.D q.1]) P.bound⟩ : Rep2)) := hq'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq''
      have hq1 := (Snd.allK_spec _ _).mp hQ q hq
      simp only [Bool.and_eq_true, Nat.beq_eq] at hq1
      obtain ⟨⟨hqr, hq0⟩, hqo⟩ := hq1
      obtain ⟨-, hqd, hWF2, hqB, -⟩ :=
        Snd.rep_facts (P := P1) hp hD hWF1 (hcaQ q hq) hqr hqo
      rw [Snd.withExtra_two] at hWF2 hqB
      simp only [Bool.and_eq_true]
      have : Fact (withExtra P [decR P.D a, decR P.D q.1]).p.Prime := hfact
      exact ⟨⟨Snd.wfR_of_dotv hp hqd, Snd.wfCheck_of_WF hp hWF2⟩, Snd.ow_spec (hqB hq0)⟩
    ·
      unfold s2Orb
      rw [List.all_eq_true]
      intro x hx
      have hx' : x ∈ Snd.ob2 P.D cd tg2 := hx
      obtain ⟨i, hi, hi2, k, w, htg, rfl⟩ := Snd.of_mem_ob2 hx'
      have hi1 : i < tg1.length := by omega
      have ht2 := hall i hi hi1 hi2
      rw [htg] at ht2
      rcases Snd.tag2_cases ht2 with h | h | ⟨-, hk, hw, heq⟩ | h
      all_goals first | exact absurd h.1 (by norm_num) | skip
      obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      have hqk : Qs[k] ∈ Qs := List.getElem_mem hk
      have hq1 := (Snd.allK_spec _ _).mp hQ _ hqk
      simp only [Bool.and_eq_true, Nat.beq_eq] at hq1
      obtain ⟨⟨hqr, -⟩, hqo⟩ := hq1
      obtain ⟨hqp, -, -, -, -⟩ := Snd.rep_facts (P := P1) hp hD hWF1 (hcaQ _ hqk) hqr hqo
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, ?_⟩, ?_⟩
      · change k < (Qs.map _).length
        rw [List.length_map]
        exact hk
      have hr2 : (Snd.mkRep P cd (a, o, mx, ro, Qs, tg2)).reps2[k]? = some ⟨decR P.D Qs[k].1,
          Snd.ow (withExtra P [decR P.D a, decR P.D Qs[k].1]) P.bound⟩ := by
        change (Qs.map _)[k]? = _
        rw [List.getElem?_map, List.getElem?_eq_getElem hk]
        rfl
      rw [hr2]
      change realizes (withExtra P [decR P.D a, decR P.D cd[i]])
        (w ++ [P.gens.length + 1] ++ w.reverse) (decR P.D Qs[k].1) = true
      rw [← Snd.withExtra_two]
      have hlen : P.gens.length + 1 = P1.gens.length := by simp [hP1]
      rw [hlen]
      apply Snd.conj_real (P := P1) hp hD hWF1 _ _ hde w (by simpa using hw)
      have hpe1 : packR P1 (decR P1.D cd[i]) = cd[i] := hpe
      rw [hpe1, hqp]
      rw [nthK_eq', List.getD_eq_getElem _ _ hk] at heq
      exact heq
    ·
      rw [List.all_eq_true]
      intro c hc'
      obtain ⟨hdc, hcm⟩ := hcandL c hc'
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
      have hi1 : i < tg1.length := by omega
      have hi2 : i < tg2.length := by omega
      have ht2 := hall i hi hi1 hi2
      rcases htg : tg2[i] with ⟨t0, k, w⟩
      rw [htg, hci] at ht2
      unfold s2Cand asymAny
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true']
      rcases Snd.tag2_cases ht2 with ⟨-, hk, heq⟩ | ⟨-, hk, has⟩ | ⟨h2, -, -, -⟩ |
        ⟨-, hmx0, j, u, ht1j, hj, hg⟩
      ·
        simp only [Snd.nthK_map _ _ hk] at heq
        unfold eqPM eqP at heq
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at heq
        refine Or.inl (Or.inl (Or.inl ?_))
        rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have he : packR P c = packR P1 Dl2[k].1 := Prod.ext e1 e2
          refine ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
            ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
          change reqb c (decR P.D (packR P1 Dl2[k].1)) = true
          rw [← he, hdc]
          exact Snd.reqb_self c
        · have he : packR P c = packR P1 (Snd.negRf P1.D Dl2[k].1) :=
            (Prod.ext e1 e2).trans (Snd.negP_packR (P := P1) hp _)
          refine ⟨(Snd.rtN P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
            ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
          change reqb c (decR P.D (packR P1 (Snd.negRf P1.D Dl2[k].1))) = true
          rw [← he, hdc]
          exact Snd.reqb_self c
      ·
        simp only [Snd.nthK_map _ _ hk] at has
        have hpr : packR P1 Dl2[k].1 = packR P (decR P.D (packR P1 Dl2[k].1)) :=
          (Snd.packR_decR hp (Snd.canP_packR (P := P1) hp _)).symm
        rw [hpr] at has
        simp only [Snd.packR3 hp, dotK_pk hp hD, Snd.nbeq] at has
        refine Or.inl (Or.inl (Or.inr ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_,
          List.mem_flatMap.mpr ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩))
        exact has
      ·
        refine Or.inl (Or.inr ⟨⟨decR P.D cd[i], w, k⟩, Snd.mem_ob2 hi hi2 (by rw [htg, h2]), ?_⟩)
        change reqb (decR P.D cd[i]) c = true
        rw [hci, hdc]
        exact Snd.reqb_self c
      ·
        refine Or.inr ⟨?_, ⟨decR P.D cd[i], u, j⟩, Snd.mem_ob1 hi hi1 ht1j, ?_, ?_⟩
        · change Nat.beq mx 1 = false
          rw [hmx0]
          rfl
        · change reqb (decR P.D cd[i]) c = true
          rw [hci, hdc]
          exact Snd.reqb_self c
        · change (match T.reps[j]? with | some rq => rq.isGoodMax | none => false) = true
          rw [hTr j hj]
          exact hgm j hj hg
  refine ⟨T, ?_⟩
  unfold verifyAll
  simp only [hwfP, hv1, hv2, hv3, hv4, Bool.and_self]

theorem frameK_of_parts {P : Pt} {d : FD} (h0 : partK P d 0 = true) (h1 : partK P d 1 = true)
    (h2 : partK P d 2 = true) (h3 : partK P d 3 = true) (h4 : partK P d 4 = true) :
    frameK P d = true := by
  change baseK P d = true at h0
  change candK P d = true at h1
  change tag1K P d = true at h2
  change repK P d = true at h3
  change s2K P d = true at h4
  rw [frameK, h0, h1, h2, h3, h4]
  rfl

end CFSG.ReflExt.RXK

end
