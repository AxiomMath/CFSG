module

public import CFSG.Certificates.Kernel.TwoNodeSmall.LaneSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallWord
public import Certificates.Data.CFSGNative.TwoNodeSmall.VerifyPos

public section

namespace CFSG.TwoNodeSmall.PosBK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.LaneSound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure LaneOK (F : Fd) (P : Pt) : Prop where
  fp : F.p = P.p
  dot : ∀ f v : Vec, dotK F (pkrP P.p P.D f) (pkP P.p P.D v) = P.dotv f v
  app : ∀ h f v : Vec, appK F (pkP P.p P.D h, pkrP P.p P.D f) (pkP P.p P.D v) =
    pkP P.p P.D (P.applyRefl ⟨f, h⟩ v)
  conj : ∀ gh gf rh rf : Vec,
    conjK F (pkP P.p P.D gh, pkrP P.p P.D gf) (pkP P.p P.D rh, pkrP P.p P.D rf) =
      (pkP P.p P.D (P.applyRefl ⟨gf, gh⟩ rh), pkrP P.p P.D (P.applyRefl ⟨gh, gf⟩ rf))

theorem laneOK_three {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) : LaneOK (fdB 3 P.D) P := by
  have e1 : pkP P.p P.D = pk P.D := by rw [hp]; rfl
  have e2 : pkrP P.p P.D = pkr P.D := by rw [hp]; rfl
  refine ⟨by rw [hp]; rfl, fun f v => ?_, fun h f v => ?_, fun gh gf rh rf => ?_⟩
  · rw [e1, e2]; exact dotK_pk hp hD f v
  · rw [e1, e2]; exact appK_pk hp hD h f v
  · rw [e1, e2]; exact conjK_pk hp hD gh gf rh rf

namespace OKS

@[expose] def md (p : Nat) (v : Vec) (i : Nat) : Nat := v.getD i 0 % p

theorem pkP_fw (p D : Nat) (v : Vec) : pkP p D v = fw D (md p v) := by
  induction D generalizing v with
  | zero => rfl
  | succ D ih =>
    rw [fw_succ_first]
    change Nat.add (Nat.mod (v.headD 0) p) (Nat.mul 65536 (pkP p D v.tail)) = _
    rw [ih]
    simp only [md, getD_succ, headD_eq]
    rfl

theorem pkrP_go (p D : Nat) : ∀ (v : Vec) (acc : Nat),
    (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p))) D v acc :
      Nat) = acc * 65536 ^ D + rv D (md p v) := by
  induction D with
  | zero => intro v acc; simp [rv, enc]
  | succ D ih =>
    intro v acc
    change (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p))) D v.tail
      (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p)) : Nat) = _
    rw [ih, rv_succ_first]
    have e : (fun i => md p v (i + 1)) = md p v.tail := by
      funext i
      simp only [md, getD_succ]
    rw [e]
    have e2 : (v.headD 0).mod p = v.getD 0 0 % p := by rw [headD_eq]; rfl
    simp only [md, Nat.add_eq, Nat.mul_eq, e2, pow_succ]
    ring

theorem pkrP_rv (p D : Nat) (f : Vec) : pkrP p D f = rv D (md p f) := by
  have h := pkrP_go p D f 0
  rw [Nat.zero_mul, Nat.zero_add] at h
  exact h

theorem md_lt {p : Nat} (hp : 0 < p) (hp' : p < 65536) (v : Vec) (i : Nat) : md p v i < 65536 := by
  have := Nat.mod_lt (v.getD i 0) hp
  unfold md
  omega

theorem pkP_inj {P : Pt} (hp : 0 < P.p) (hp' : P.p < 65536) (v w : Vec) :
    pkP P.p P.D v = pkP P.p P.D w ↔ P.vecEq v w = true := by
  rw [pkP_fw, pkP_fw]
  unfold fw
  rw [enc_map_inj _ _ _ (md_lt hp hp' v) (md_lt hp hp' w), Pt.vecEq, List.all_eq_true]
  simp only [Pt.ent, md, beq_iff_eq]

theorem shiftLeft_unitP (P : Pt) (hp : 2 ≤ P.p) {i : Nat} (hi : i < P.D) :
    Nat.shiftLeft 1 (Nat.mul 16 i) = pkP P.p P.D (P.unit i) := by
  change 1 <<< (16 * i) = _
  have e : (2 : Nat) ^ 16 = 65536 := rfl
  rw [pkP_fw, Nat.shiftLeft_eq, Nat.one_mul, pow_mul, e, ← fw_unit P.D i hi]
  unfold fw
  apply enc_map_congr
  intro j hj
  rw [List.mem_range] at hj
  simp only [md, Pt.unit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  split
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · exact (Nat.zero_mod _).symm

theorem enc_lane (l : List Nat) (hl : ∀ x ∈ l, x < 65536) (m : Nat) :
    enc l / 65536 ^ m % 65536 = l.getD m 0 := by
  induction l generalizing m with
  | nil => simp [enc]
  | cons x l ih =>
    have hx := hl x (by simp)
    cases m with
    | zero =>
      simp only [enc_cons, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ m =>
      rw [enc_cons, pow_succ', ← Nat.div_div_eq_div_mul, List.getD_cons_succ]
      have : (x + 65536 * enc l) / 65536 = enc l := by omega
      rw [this, ih (fun y hy => hl y (by simp [hy]))]

theorem land_mask {a s : Nat} (h : Nat.land a (Nat.shiftLeft 65535 s) = 0) :
    a / 65536 ^ (s / 16) % 65536 = 0 ∨ s % 16 ≠ 0 := by
  have e16 : (65536 : Nat) = 2 ^ 16 := rfl
  have e15 : (65535 : Nat) = 2 ^ 16 - 1 := rfl
  rcases Nat.eq_zero_or_pos (s % 16) with hs | hs
  · left
    have e1 : (65536 : Nat) ^ (s / 16) = 2 ^ s := by
      rw [e16, ← pow_mul]
      congr 1
      omega
    rw [e1]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit, e16, Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.testBit_shiftRight]
    by_cases hi : i < 16
    · have := congrArg (fun x => x.testBit (s + i)) h
      simp only [Nat.zero_testBit] at this
      change (a &&& 65535 <<< s).testBit (s + i) = false at this
      rw [Nat.testBit_and, Nat.testBit_shiftLeft, e15, Nat.testBit_two_pow_sub_one] at this
      simp only [ge_iff_le, Nat.le_add_right, decide_true, Nat.add_sub_cancel_left, hi,
        Bool.true_and, Bool.and_true] at this
      simp [this]
    · simp [hi]
  · right
    omega

theorem mask_md {p D b : Nat} (hp : 0 < p) (hp' : p < 65536) (hb : b < D) (f : Vec)
    (h : Nat.land (pkrP p D f) (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub D 1) b)))
      = 0) : f.getD b 0 % p = 0 := by
  have e16 : Nat.mul 16 (Nat.sub (Nat.sub D 1) b) / 16 = D - 1 - b := by
    change 16 * (D - 1 - b) / 16 = _
    omega
  rcases land_mask h with h | h
  · rw [e16, pkrP_rv] at h
    unfold rv at h
    have hlt : ∀ x ∈ (List.range D).reverse.map (md p f), x < 65536 := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact md_lt hp hp' f i
    rw [enc_lane _ hlt] at h
    have hl : D - 1 - b < ((List.range D).reverse.map (md p f)).length := by
      simp only [List.length_map, List.length_reverse, List.length_range]
      omega
    rw [List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse,
      List.getElem_range] at h
    simp only [List.length_range] at h
    have e : D - 1 - (D - 1 - b) = b := by omega
    rw [e] at h
    exact h
  · have e0 : Nat.mul 16 (Nat.sub (Nat.sub D 1) b) % 16 = 0 := by
      change 16 * (D - 1 - b) % 16 = 0
      omega
    exact absurd e0 h

theorem land_lor_zero {a E m : Nat} (h : Nat.land a (Nat.lor E m) = 0) :
    Nat.land a E = 0 ∧ Nat.land a m = 0 := by
  have ht := fun i => congrArg (fun x => Nat.testBit x i) h
  change ∀ i, (a &&& (E ||| m)).testBit i = Nat.testBit 0 i at ht
  constructor
  · apply Nat.eq_of_testBit_eq
    intro i
    have := ht i
    change (a &&& E).testBit i = _
    revert this
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit]
    cases a.testBit i <;> cases E.testBit i <;> cases m.testBit i <;> simp
  · apply Nat.eq_of_testBit_eq
    intro i
    have := ht i
    change (a &&& m).testBit i = _
    revert this
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit]
    cases a.testBit i <;> cases E.testBit i <;> cases m.testBit i <;> simp

theorem nthK_eq' {α : Type} (d : α) (l : List α) (k : Nat) : nthK d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih => cases k with
    | zero => rfl
    | succ k => exact ih k

theorem dropK_eq' {α : Type} (k : Nat) (l : List α) : dropK k l = l.drop k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (dropK k l).tail = _
    rw [ih, List.tail_drop]

theorem headD_drop {α : Type} (d : α) (l : List α) (i : Nat) : (l.drop i).headD d = l.getD i d := by
  induction l generalizing i with
  | nil => simp
  | cons x l ih => cases i with
    | zero => simp
    | succ i => simp only [List.drop_succ_cons, List.getD_cons_succ]; exact ih i

theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.eraseDups_cons]
    have ha := (List.nodup_cons.mp h).1
    have hf : l.filter (fun b => !b == a) = l := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun e => ha (e ▸ hb)
      simpa using this
    rw [hf, eraseDups_of_nodup l (List.nodup_cons.mp h).2]

theorem vec_of_vecEq (P : Pt) {a b : Vec} (h : P.vecEq a b = true) : P.vec a = P.vec b := by
  funext i
  have := (List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt)
  simp only [Pt.ent, beq_iff_eq] at this
  simp only [Pt.vec]
  rw [← ZMod.natCast_mod (a.getD i 0), this, ZMod.natCast_mod]

theorem vecEq_of_vec (P : Pt) {a b : Vec} (h : P.vec a = P.vec b) : P.vecEq a b = true := by
  unfold Pt.vecEq
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have := congrFun h ⟨j, hj⟩
  simp only [Pt.vec] at this
  rw [ZMod.natCast_eq_natCast_iff'] at this
  simp only [Pt.ent, beq_iff_eq]
  exact this

theorem dot_add (P : Pt) (f x y : P.V) : P.dot f (x + y) = P.dot f x + P.dot f y := by
  simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_sub (P : Pt) (f x y : P.V) : P.dot f (x - y) = P.dot f x - P.dot f y := by
  simp only [Pt.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_smul (P : Pt) (f x : P.V) (a : ZMod P.p) : P.dot f (a • x) = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sub_dot (P : Pt) (f g x : P.V) : P.dot (f - g) x = P.dot f x - P.dot g x := by
  simp only [Pt.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem smul_dot (P : Pt) (f x : P.V) (a : ZMod P.p) : P.dot (a • f) x = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_comm' (P : Pt) (f x : P.V) : P.dot f x = P.dot x f := by
  simp only [Pt.dot]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_single (P : Pt) (f : P.V) (i : Fin P.D) : P.dot f (Pi.single i 1) = f i := by
  simp [Pt.dot, Pi.single_apply]

theorem applyWord_nil (P : Pt) (v : Vec) : P.applyWord [] v = v := rfl

theorem applyWord_append (P : Pt) (a b : Word) (v : Vec) :
    P.applyWord (a ++ b) v = P.applyWord a (P.applyWord b v) := by
  simp only [Pt.applyWord, List.foldr_append]

theorem applyWord_cons (P : Pt) {i : Nat} (hi : i < P.gens.length) (w : Word) (v : Vec) :
    P.applyWord (i :: w) v = P.applyRefl (P.gens.getD i ⟨[], []⟩) (P.applyWord w v) := by
  simp only [Pt.applyWord, List.foldr_cons, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem _ _ hi]

theorem applyWord_single (P : Pt) {i : Nat} (hi : i < P.gens.length) (v : Vec) :
    P.applyWord [i] v = P.applyRefl (P.gens.getD i ⟨[], []⟩) v :=
  applyWord_cons P hi [] v

theorem wordOK_cons (P : Pt) (i : Nat) (w : Word) :
    P.wordOK (i :: w) = true ↔ i < P.gens.length ∧ P.wordOK w = true := by
  simp [Pt.wordOK]

variable {P : Pt}

theorem vec_refl [Fact P.p.Prime] (r : Refl) (v : Vec) :
    P.vec (P.applyRefl r v) = P.vec v - P.dot (P.vec r.f) (P.vec v) • P.vec r.h :=
  Pt.vec_applyRefl P r v

theorem word_rev [Fact P.p.Prime] (hwf : P.WF) :
    ∀ (w : Word), P.wordOK w = true → ∀ v, P.vec (P.applyWord w (P.applyWord w.reverse v)) = P.vec v
  | [], _, v => rfl
  | a :: w, hw, v => by
    rw [wordOK_cons] at hw
    rw [List.reverse_cons, applyWord_append, applyWord_single P hw.1, applyWord_cons P hw.1,
      vec_refl]
    have ih := word_rev hwf w hw.2 (P.applyRefl (P.gens.getD a ⟨[], []⟩) v)
    rw [ih, vec_refl]
    have hd : P.dot (P.vec (P.gens.getD a ⟨[], []⟩).f) (P.vec (P.gens.getD a ⟨[], []⟩).h) = 2 := by
      rw [List.getD_eq_getElem _ _ hw.1]; exact hwf _ (List.getElem_mem hw.1)
    rw [dot_sub, dot_smul, hd]
    module

abbrev CE := Refl × Word × Nat

@[expose] def dfl : CE := (⟨[], []⟩, [], 0)

@[expose] noncomputable def packR (P : Pt) (r : Refl) : Nat × Nat :=
  (pkP P.p P.D r.h, pkrP P.p P.D r.f)

@[expose] def conjR (P : Pt) (g r : Refl) : Refl := ⟨P.applyRefl ⟨g.h, g.f⟩ r.f, P.applyRefl g r.h⟩

@[expose] def stepC (P : Pt) (acc : List CE) (e : Nat × Nat × Nat × Nat) : CE :=
  let x := acc.getD e.2.1 dfl
  (conjR P (P.gens.getD e.1 ⟨[], []⟩) x.1, e.1 :: x.2.1, x.2.2)

@[expose] def cloD (P : Pt) : List CE → List (Nat × Nat × Nat × Nat) → List CE
  | acc, [] => acc
  | acc, e :: es => cloD P (acc ++ [stepC P acc e]) es

@[expose] def baseD (P : Pt) : List CE :=
  (List.range P.gens.length).map fun i => (P.gens.getD i ⟨[], []⟩, [], i)

@[expose] def gk (P : Pt) (x : CE) : Refl := P.gens.getD x.2.2 ⟨[], []⟩

@[expose] def Sem (P : Pt) (x : CE) : Prop :=
  P.wordOK x.2.1 = true ∧ x.2.2 < P.gens.length ∧
    P.vec x.1.h = P.vec (P.applyWord x.2.1 (gk P x).h) ∧
    ∀ u, P.dot (P.vec x.1.f) (P.vec u) = P.dot (P.vec (gk P x).f) (P.vec (P.applyWord x.2.1.reverse u))

theorem sem_base [Fact P.p.Prime] : ∀ x ∈ baseD P, Sem P x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  exact ⟨rfl, hi, rfl, fun u => rfl⟩

theorem sem_step [Fact P.p.Prime] {x : CE} (hx : Sem P x) {j : Nat} (hj : j < P.gens.length) :
    Sem P (conjR P (P.gens.getD j ⟨[], []⟩) x.1, j :: x.2.1, x.2.2) := by
  obtain ⟨hw, hk, hh, hf⟩ := hx
  set g := P.gens.getD j ⟨[], []⟩
  refine ⟨(wordOK_cons P j _).mpr ⟨hj, hw⟩, hk, ?_, fun u => ?_⟩
  · change P.vec (P.applyRefl g x.1.h) = P.vec (P.applyWord (j :: x.2.1) (gk P x).h)
    rw [applyWord_cons P hj, vec_refl, vec_refl, hh]
  · change P.dot (P.vec (P.applyRefl ⟨g.h, g.f⟩ x.1.f)) (P.vec u) =
      P.dot (P.vec (gk P x).f) (P.vec (P.applyWord (j :: x.2.1).reverse u))
    rw [List.reverse_cons, applyWord_append, applyWord_single P hj, ← hf, vec_refl, vec_refl,
      sub_dot, smul_dot, dot_sub, dot_smul]
    change P.dot (P.vec x.1.f) (P.vec u) - P.dot (P.vec g.h) (P.vec x.1.f) * P.dot (P.vec g.f) (P.vec u) =
      P.dot (P.vec x.1.f) (P.vec u) - P.dot (P.vec g.f) (P.vec u) * P.dot (P.vec x.1.f) (P.vec g.h)
    rw [dot_comm' P (P.vec g.h)]
    ring

@[expose] def sw (x : CE) : Word := x.2.1 ++ [x.2.2] ++ x.2.1.reverse

theorem sw_ok {x : CE} (hx : Sem P x) : P.wordOK (sw x) = true := by
  have hk := hx.2.1
  have hw := hx.1
  simp only [sw, Pt.wordOK, List.all_append, List.all_cons, List.all_nil, List.all_reverse,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
  exact ⟨⟨hw, hk⟩, hw⟩

theorem sw_act [Fact P.p.Prime] (hwf : P.WF) {x : CE} (hx : Sem P x) (v : Vec) :
    P.vec (P.applyWord (sw x) v) = P.vec (P.applyRefl x.1 v) := by
  obtain ⟨hw, hk, hh, hf⟩ := hx
  obtain ⟨γ, _, hγ⟩ := Pt.applyWord_spec P hwf x.2.1 hw
  rw [sw, List.append_assoc, applyWord_append, applyWord_append, applyWord_single P hk, ← hγ,
    vec_refl, map_sub, map_smul, hγ, hγ, word_rev hwf _ hw, vec_refl, hf, hh]
  rfl

@[expose] def ent (e : Nat × Nat × Nat × Nat) : Nat × Nat := (e.2.2.1, e.2.2.2)

theorem cloP_cons (F : Fd) (n : Nat) (G : List (Nat × Nat)) (e : Nat × Nat × Nat × Nat)
    (es : List (Nat × Nat × Nat × Nat)) (i cur : Nat) (suf : List (Nat × Nat)) :
    cloP F n G (e :: es) i cur suf =
      (let suf' := dropK (Nat.sub e.2.1 cur) suf
       let c := conjK F (nthK (0, 0) G e.1) (suf'.headD (0, 0))
       Nat.blt e.2.1 i && Nat.ble cur e.2.1 && Nat.blt e.1 n && Nat.beq e.2.2.1 c.1 &&
         Nat.beq e.2.2.2 c.2 && cloP F n G es (Nat.succ i) e.2.1 suf') := rfl

theorem conj_pack {F : Fd} (hL : LaneOK F P) (g r : Refl) :
    conjK F (packR P g) (packR P r) = packR P (conjR P g r) :=
  hL.conj g.h g.f r.h r.f

theorem length_cloD (P : Pt) : ∀ (acc : List CE) (clo : List (Nat × Nat × Nat × Nat)),
    (cloD P acc clo).length = acc.length + clo.length
  | acc, [] => rfl
  | acc, e :: es => by
    rw [cloD, length_cloD P _ es]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem cloP_spec [Fact P.p.Prime] {F : Fd} (hL : LaneOK F P) (C : List (Nat × Nat)) :
    ∀ (clo : List (Nat × Nat × Nat × Nat)) (acc : List CE) (cur : Nat) (rest : List (Nat × Nat)),
      cloP F P.gens.length (P.gens.map (packR P)) clo acc.length cur (C.drop cur) = true →
      cur ≤ acc.length → acc.map (fun x => packR P x.1) = C.take acc.length →
      C.drop acc.length = clo.map ent ++ rest → (∀ x ∈ acc, Sem P x) →
      (cloD P acc clo).map (fun x => packR P x.1) = C.take (acc.length + clo.length) ∧
        ∀ x ∈ cloD P acc clo, Sem P x
  | [], acc, _, _, _, _, hacc, _, hs => by
    refine ⟨?_, hs⟩
    simpa [cloD] using hacc
  | e :: es, acc, cur, rest, h, hcur, hacc, hdrop, hs => by
    rw [cloP_cons] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨⟨hq, hcq⟩, hj⟩, hc1⟩, hc2⟩, hrest⟩ := h
    have hlen : acc.length ≤ C.length := by
      have := congrArg List.length hacc
      simp only [List.length_map, List.length_take] at this
      omega
    have hsuf : dropK (Nat.sub e.2.1 cur) (C.drop cur) = C.drop e.2.1 := by
      rw [dropK_eq', List.drop_drop]
      congr 1
      change cur + (e.2.1 - cur) = e.2.1
      omega
    rw [hsuf] at hc1 hc2 hrest
    have hCq : (C.drop e.2.1).headD (0, 0) = packR P (acc.getD e.2.1 dfl).1 := by
      rw [headD_drop]
      have hqC : e.2.1 < C.length := by omega
      rw [List.getD_eq_getElem _ _ hqC, List.getD_eq_getElem _ _ hq]
      have := congrArg (fun l => l[e.2.1]?) hacc
      simp only [List.getElem?_map, List.getElem?_eq_getElem hq, List.getElem?_take,
        if_pos hq, List.getElem?_eq_getElem hqC,
        Option.map_some, Option.some.injEq] at this
      exact this.symm
    have hGj : nthK (0, 0) (P.gens.map (packR P)) e.1 = packR P (P.gens.getD e.1 ⟨[], []⟩) := by
      rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
    rw [hCq, hGj, conj_pack hL] at hc1 hc2
    have hent : ent e = packR P (stepC P acc e).1 := by
      simp only [ent, stepC, Prod.ext_iff]
      exact ⟨hc1, hc2⟩
    have hsem : Sem P (stepC P acc e) := by
      have hx : Sem P (acc.getD e.2.1 dfl) := by
        rw [List.getD_eq_getElem _ _ hq]; exact hs _ (List.getElem_mem hq)
      exact sem_step hx hj
    have hacc' : (acc ++ [stepC P acc e]).map (fun x => packR P x.1) =
        C.take (acc ++ [stepC P acc e]).length := by
      rw [List.map_append, hacc, List.length_append, List.length_singleton, List.take_succ]
      have h0 : C[acc.length]? = some (ent e) := by
        have := congrArg (fun l => l[0]?) hdrop
        simpa using this
      rw [h0]
      simp [hent]
    have hdrop' : C.drop (acc ++ [stepC P acc e]).length = es.map ent ++ rest := by
      rw [List.length_append, List.length_singleton, ← List.drop_drop, hdrop]
      simp
    have hs' : ∀ x ∈ acc ++ [stepC P acc e], Sem P x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs x hx
      · rw [List.mem_singleton.mp hx]; exact hsem
    have hl : (acc ++ [stepC P acc e]).length = Nat.succ acc.length := by simp
    rw [← hl] at hrest
    have := cloP_spec hL C es (acc ++ [stepC P acc e]) e.2.1 rest hrest (by simp; omega) hacc' hdrop' hs'
    have hl2 : (acc ++ [stepC P acc e]).length + es.length = acc.length + (e :: es).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [cloD]
    refine ⟨?_, this.2⟩
    rw [this.1, hl2]

abbrev TE := Vec × Nat × Nat

@[expose] def dt : TE := ([], 0, 0)

theorem clearB_spec {bs k : Nat} (h : clearB bs k = true) : bs.testBit k = false := by
  unfold clearB at h
  rw [Nat.beq_eq] at h
  change (bs >>> k) &&& 1 = 0 at h
  rw [Nat.and_one_is_mod] at h
  have e := Nat.testBit_shiftRight (i := k) (j := 0) bs
  rw [Nat.add_zero] at e
  rw [← e, Nat.testBit_zero, h]
  rfl

theorem testBit_lor_one (bs k j : Nat) :
    (Nat.lor bs (Nat.shiftLeft 1 k)).testBit j = (bs.testBit j || decide (k = j)) := by
  change (bs ||| 1 <<< k).testBit j = _
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem kidsM_nil (F : Fd) (km V m : Nat) (st : List Nat × Nat × Nat × Bool) :
    kidsM F km V [] m st = (st.1, st.2.1, st.2.2.1, st.2.2.2 && Nat.beq m 0) := rfl

theorem kidsM_cons (F : Fd) (km V : Nat) (r : Nat × Nat) (rs : List (Nat × Nat)) (m : Nat)
    (st : List Nat × Nat × Nat × Bool) :
    kidsM F km V (r :: rs) m st =
      bif Nat.beq m 0 then st
      else bif Nat.beq (Nat.land m 1) 0 then kidsM F km V rs (Nat.shiftRight m 1) st
      else kidsM F km V rs (Nat.shiftRight m 1)
        (appK F r V :: st.1, Nat.lor st.2.1 (Nat.shiftLeft 1 (Nat.mod (appK F r V) km)),
          Nat.succ st.2.2.1, st.2.2.2 && clearB st.2.1 (Nat.mod (appK F r V) km)) := rfl

theorem kids_false (F : Fd) (km V : Nat) : ∀ (rs : List (Nat × Nat)) (m : Nat)
    (st : List Nat × Nat × Nat × Bool), st.2.2.2 = false → (kidsM F km V rs m st).2.2.2 = false
  | [], m, st, h => by simp [kidsM_nil, h]
  | r :: rs, m, st, h => by
    rw [kidsM_cons]
    cases Nat.beq m 0
    · cases Nat.beq (Nat.land m 1) 0
      · exact kids_false F km V rs _ _ (by simp [h])
      · exact kids_false F km V rs _ st h
    · exact h

structure TInv (P : Pt) (km : Nat) (Sv : List Refl) (root : Vec) (T : List TE) (np : Nat)
    (fr bk : List Nat) (bs cnt : Nat) : Prop where
  q1 : (T.drop np).map (fun e => pkP P.p P.D e.1) = fr ++ bk.reverse
  q2 : cnt = T.length
  q3 : (T.map fun e => pkP P.p P.D e.1 % km).Nodup
  q4 : ∀ e ∈ T, bs.testBit (pkP P.p P.D e.1 % km) = true
  q5 : ∀ i (hi : i < T.length), 0 < i → T[i].2.1 < i ∧ T[i].2.2 < Sv.length ∧
    T[i].1 = P.applyRefl (Sv.getD T[i].2.2 ⟨[], []⟩) (T.getD T[i].2.1 dt).1
  q6 : T.head? = some (root, 0, 0)
  q7 : np ≤ T.length

structure TFin (P : Pt) (km : Nat) (Sv : List Refl) (root : Vec) (T : List TE) : Prop where
  q3 : (T.map fun e => pkP P.p P.D e.1 % km).Nodup
  q5 : ∀ i (hi : i < T.length), 0 < i → T[i].2.1 < i ∧ T[i].2.2 < Sv.length ∧
    T[i].1 = P.applyRefl (Sv.getD T[i].2.2 ⟨[], []⟩) (T.getD T[i].2.1 dt).1
  q6 : T.head? = some (root, 0, 0)

theorem drop_map_cons {T : List TE} {np : Nat} {g : TE → Nat} {x : Nat} {rest : List Nat}
    (h : (T.drop np).map g = x :: rest) :
    np < T.length ∧ g (T.getD np dt) = x ∧ (T.drop (np + 1)).map g = rest := by
  have hlt : np < T.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  rw [← List.getElem_cons_drop hlt, List.map_cons, List.cons.injEq] at h
  exact ⟨hlt, by rw [List.getD_eq_getElem _ _ hlt]; exact h.1, h.2⟩

theorem popK_cons (x : Nat) (xs bk : List Nat) : popK (x :: xs) bk = (x, xs, bk, true) := rfl

theorem popK_nil (bk : List Nat) :
    popK [] bk = List.rec (motive := fun _ => Nat × List Nat × List Nat × Bool) (0, [], [], false)
      (fun x xs _ => (x, xs, [], true)) bk.reverse := rfl

theorem pop_spec {P : Pt} {km : Nat} {Sv : List Refl} {root : Vec} {T : List TE} {np : Nat}
    {fr bk : List Nat} {bs cnt : Nat} (h : TInv P km Sv root T np fr bk bs cnt)
    (hp : (popK fr bk).2.2.2 = true) :
    np < T.length ∧ (popK fr bk).1 = pkP P.p P.D (T.getD np dt).1 ∧
      TInv P km Sv root T (np + 1) (popK fr bk).2.1 (popK fr bk).2.2.1 bs cnt := by
  have q1 := h.q1
  cases fr with
  | cons x xs =>
    rw [popK_cons]
    rw [List.cons_append] at q1
    obtain ⟨hlt, hx, hr⟩ := drop_map_cons q1
    exact ⟨hlt, hx.symm, ⟨hr, h.q2, h.q3, h.q4, h.q5, h.q6, hlt⟩⟩
  | nil =>
    rw [popK_nil] at hp ⊢
    rw [List.nil_append] at q1
    cases hb : bk.reverse with
    | nil => rw [hb] at hp; cases hp
    | cons x xs =>
      rw [hb] at q1
      obtain ⟨hlt, hx, hr⟩ := drop_map_cons q1
      refine ⟨hlt, hx.symm, ⟨?_, h.q2, h.q3, h.q4, h.q5, h.q6, hlt⟩⟩
      rw [hr]
      simp

theorem getD_append_left {α : Type} (l : List α) (x : α) (d : α) {i : Nat} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

theorem kids_spec {F : Fd} {P : Pt} (hL : LaneOK F P) {km : Nat} {Sv : List Refl} {root : Vec}
    {np par : Nat} {fr : List Nat} {V : Vec} :
    ∀ (rs : List Refl) (k m : Nat) (bk : List Nat) (bs cnt : Nat) (fl : Bool) (T : List TE),
      Sv.drop k = rs → par < T.length → (T.getD par dt).1 = V →
      TInv P km Sv root T np fr bk bs cnt →
      (kidsM F km (pkP P.p P.D V) (rs.map (packR P)) m (bk, bs, cnt, fl)).2.2.2 = true →
      ∃ T', (∃ new, T' = T ++ new) ∧
        TInv P km Sv root T' np fr (kidsM F km (pkP P.p P.D V) (rs.map (packR P)) m (bk, bs, cnt, fl)).1
          (kidsM F km (pkP P.p P.D V) (rs.map (packR P)) m (bk, bs, cnt, fl)).2.1
          (kidsM F km (pkP P.p P.D V) (rs.map (packR P)) m (bk, bs, cnt, fl)).2.2.1
  | [], k, m, bk, bs, cnt, fl, T, _, _, _, hI, _ => by
    rw [List.map_nil, kidsM_nil]
    exact ⟨T, ⟨[], by simp⟩, hI⟩
  | r :: rs, k, m, bk, bs, cnt, fl, T, hk, hpar, hV, hI, hfl => by
    have hk' : Sv.drop (k + 1) = rs := by rw [← List.tail_drop, hk]; rfl
    have hkl : k < Sv.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hk
      cases hk
    have hSk : Sv.getD k ⟨[], []⟩ = r := by
      rw [← headD_drop, hk]
      rfl
    rw [List.map_cons, kidsM_cons] at hfl ⊢
    cases hm : Nat.beq m 0
    · rw [hm] at hfl
      simp only [cond_false] at hfl ⊢
      cases hb : Nat.beq (Nat.land m 1) 0
      · rw [hb] at hfl
        simp only [cond_false] at hfl ⊢
        have hw : appK F (packR P r) (pkP P.p P.D V) = pkP P.p P.D (P.applyRefl r V) :=
          hL.app r.h r.f V
        rw [hw] at hfl ⊢
        set w := pkP P.p P.D (P.applyRefl r V) with hwdef
        have hin : (fl && clearB bs (w % km)) = true := by
          by_contra hc
          rw [Bool.not_eq_true] at hc
          rw [kids_false F km _ (rs.map (packR P)) _ _ hc] at hfl
          cases hfl
        have hcl : bs.testBit (w % km) = false := clearB_spec (Bool.and_eq_true _ _ ▸ hin).2
        let e : TE := (P.applyRefl r V, par, k)
        have hI' : TInv P km Sv root (T ++ [e]) np fr (w :: bk) (Nat.lor bs (Nat.shiftLeft 1 (w % km)))
            (Nat.succ cnt) := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [List.drop_append_of_le_length hI.q7, List.map_append, hI.q1]
            simp [e, hwdef]
          · rw [hI.q2]; simp
          · rw [List.map_append, List.nodup_append]
            refine ⟨hI.q3, by simp, ?_⟩
            intro a ha b hb hab
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
            have := hI.q4 x hx
            rw [hab, hb] at this
            simp only [e] at this
            rw [← hwdef, hcl] at this
            cases this
          · intro x hx
            rw [testBit_lor_one]
            rcases List.mem_append.mp hx with hx | hx
            · rw [hI.q4 x hx]; rfl
            · rw [List.mem_singleton.mp hx]; simp [e, hwdef]
          · intro i hi hi0
            rw [List.length_append, List.length_singleton] at hi
            rcases Nat.lt_or_ge i T.length with hiT | hiT
            · obtain ⟨a1, a2, a3⟩ := hI.q5 i hiT hi0
              rw [List.getElem_append_left hiT, getD_append_left _ _ _ (by omega)]
              exact ⟨a1, a2, a3⟩
            · have hiE : i = T.length := by omega
              subst hiE
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero, e]
              refine ⟨hpar, hkl, ?_⟩
              rw [getD_append_left _ _ _ hpar, hV, hSk]
          · obtain ⟨t, ht⟩ : ∃ t, T = (root, 0, 0) :: t := by
              have := hI.q6
              cases T with
              | nil => cases this
              | cons a t => exact ⟨t, by simp at this; rw [this]⟩
            rw [ht]
            rfl
          · simp only [List.length_append]
            have := hI.q7
            omega
        have hpar' : par < (T ++ [e]).length := by
          rw [List.length_append]
          omega
        obtain ⟨T', ⟨new, hT'⟩, hI''⟩ := kids_spec hL rs (k + 1) _ _ _ _ _ (T ++ [e]) hk' hpar' (by rw [getD_append_left _ _ _ hpar, hV]) hI' hfl
        exact ⟨T', ⟨e :: new, by rw [hT']; simp⟩, hI''⟩
      · rw [hb] at hfl
        simp only [cond_true] at hfl ⊢
        exact kids_spec hL rs (k + 1) _ bk bs cnt fl T hk' hpar hV hI hfl
    · simp only [cond_true]
      exact ⟨T, ⟨[], by simp⟩, hI⟩

@[expose] noncomputable def tloop (F : Fd) (km : Nat) (S : List (Nat × Nat)) (ms : List Nat) :
    List Nat × List Nat × Nat × Nat × Bool → Nat :=
  List.rec (motive := fun _ => List Nat × List Nat × Nat × Nat × Bool → Nat)
    (fun st => bif st.2.2.2.2 then st.2.2.2.1 else 0)
    (fun m _ ih st =>
      let p := popK st.1 st.2.1
      let r := kidsM F km p.1 S m (p.2.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 && p.2.2.2)
      ih (p.2.1, r.1, r.2.1, r.2.2.1, r.2.2.2))
    ms

theorem treeM_eq (F : Fd) (km : Nat) (S : List (Nat × Nat)) (root : Nat) (ms : List Nat) :
    treeM F km S root ms = tloop F km S ms ([root], [], Nat.shiftLeft 1 (Nat.mod root km), 1, true) :=
  rfl

theorem tloop_nil (F : Fd) (km : Nat) (S : List (Nat × Nat)) (st) :
    tloop F km S [] st = bif st.2.2.2.2 then st.2.2.2.1 else 0 := rfl

theorem tloop_cons (F : Fd) (km : Nat) (S : List (Nat × Nat)) (m : Nat) (ms : List Nat) (st) :
    tloop F km S (m :: ms) st = tloop F km S ms ((popK st.1 st.2.1).2.1,
      (kidsM F km (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).1,
      (kidsM F km (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.1,
      (kidsM F km (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.1,
      (kidsM F km (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.2) := rfl

theorem tloop_false (F : Fd) (km : Nat) (S : List (Nat × Nat)) :
    ∀ (ms : List Nat) (st : List Nat × List Nat × Nat × Nat × Bool), st.2.2.2.2 = false →
      tloop F km S ms st = 0
  | [], st, h => by rw [tloop_nil, h]; rfl
  | m :: ms, st, h => by
    rw [tloop_cons]
    apply tloop_false F km S ms
    exact kids_false F km _ S m _ (by simp [h])

theorem tloop_spec {F : Fd} {P : Pt} (hL : LaneOK F P) {km : Nat} {Sv : List Refl} {root : Vec} :
    ∀ (ms : List Nat) (st : List Nat × List Nat × Nat × Nat × Bool) (T : List TE) (np : Nat),
      TInv P km Sv root T np st.1 st.2.1 st.2.2.1 st.2.2.2.1 →
      tloop F km (Sv.map (packR P)) ms st ≠ 0 →
      ∃ T', TFin P km Sv root T' ∧ tloop F km (Sv.map (packR P)) ms st = T'.length
  | [], st, T, np, hI, h => by
    rw [tloop_nil] at h ⊢
    cases hf : st.2.2.2.2
    · rw [hf] at h; exact absurd rfl h
    · exact ⟨T, ⟨hI.q3, hI.q5, hI.q6⟩, by rw [cond_true, hI.q2]⟩
  | m :: ms, st, T, np, hI, h => by
    rw [tloop_cons] at h ⊢
    have hk : (kidsM F km (popK st.1 st.2.1).1 (Sv.map (packR P)) m ((popK st.1 st.2.1).2.2.1,
        st.2.2.1, st.2.2.2.1, st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.2 = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      exact h (tloop_false F km _ ms _ hc)
    have hin : (st.2.2.2.2 && (popK st.1 st.2.1).2.2.2) = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      rw [kids_false F km _ _ m _ hc] at hk
      cases hk
    have hpop := (Bool.and_eq_true _ _ ▸ hin).2
    obtain ⟨hlt, hx, hI1⟩ := pop_spec hI hpop
    rw [hx] at hk h ⊢
    obtain ⟨T1, _, hI2⟩ := kids_spec hL Sv 0 m _ _ _ _ T (List.drop_zero) hlt rfl hI1 hk
    exact tloop_spec hL ms _ T1 (np + 1) hI2 h

theorem treeM_spec {F : Fd} {P : Pt} (hL : LaneOK F P) (hp2 : 2 ≤ P.p) {km : Nat}
    {Sv : List Refl} {b : Nat} (hb : b < P.D) {ms : List Nat}
    (h : treeM F km (Sv.map (packR P)) (Nat.shiftLeft 1 (Nat.mul 16 b)) ms ≠ 0) :
    ∃ T, TFin P km Sv (P.unit b) T ∧
      treeM F km (Sv.map (packR P)) (Nat.shiftLeft 1 (Nat.mul 16 b)) ms = T.length := by
  rw [treeM_eq] at h ⊢
  rw [shiftLeft_unitP P hp2 hb] at h ⊢
  refine tloop_spec hL ms _ [(P.unit b, 0, 0)] 0 ⟨by simp, rfl, by simp, ?_, ?_, rfl, by simp⟩ h
  · intro e he
    rw [List.mem_singleton.mp he]
    change (1 <<< _).testBit _ = true
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    exact decide_eq_true rfl
  · intro i hi hi0
    simp at hi
    omega

theorem selK_spec (C : List (Nat × Nat)) (n : Nat) : ∀ (idx : List Nat) (cur : Nat),
    sortedLt n idx cur = true →
      selK idx cur (C.drop cur) = idx.map (fun i => C.getD i (0, 0)) ∧ ∀ i ∈ idx, i < n
  | [], _, _ => ⟨rfl, by simp⟩
  | i :: is, cur, h => by
    change (Nat.ble cur i && Nat.blt i n && sortedLt n is i) = true at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    have hd : dropK (Nat.sub i cur) (C.drop cur) = C.drop i := by
      rw [dropK_eq', List.drop_drop]
      congr 1
      change cur + (i - cur) = i
      omega
    change (dropK (Nat.sub i cur) (C.drop cur)).headD (0, 0) ::
      selK is i (dropK (Nat.sub i cur) (C.drop cur)) = _ ∧ _
    rw [hd, headD_drop]
    obtain ⟨h1, h2⟩ := selK_spec C n is i h.2
    refine ⟨by rw [h1]; rfl, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.2
    · exact h2 x hx

theorem code_go (P : Pt) (hp : 0 < P.p) (a b : Vec) : ∀ l : List Nat,
    l.foldr (fun j acc => P.ent a j + P.p * acc) 0 = l.foldr (fun j acc => P.ent b j + P.p * acc) 0 →
      ∀ j ∈ l, P.ent a j = P.ent b j
  | [], _ => by simp
  | j :: l, h => by
    simp only [List.foldr_cons] at h
    have ha : P.ent a j < P.p := Nat.mod_lt _ hp
    have hb : P.ent b j < P.p := Nat.mod_lt _ hp
    have e1 := congrArg (· % P.p) h
    have e2 := congrArg (· / P.p) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e1
    simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
      Nat.zero_add] at e2
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact e1
    · exact code_go P hp a b l e2 i hi

theorem vecEq_of_code (P : Pt) (hp : 0 < P.p) {a b : Vec} (h : P.code a = P.code b) :
    P.vecEq a b = true := by
  unfold Pt.vecEq
  rw [List.all_eq_true]
  intro j hj
  rw [code_go P hp a b _ h j hj]
  exact beq_self_eq_true _

theorem nodup_map_of {α β γ : Type} {f : α → β} {g : α → γ} : ∀ {l : List α}, (l.map f).Nodup →
    (∀ x ∈ l, ∀ y ∈ l, g x = g y → f x = f y) → (l.map g).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hg => by
    rw [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨fun hm => ?_, nodup_map_of h.2 (fun x hx y hy => hg x (by simp [hx]) y (by simp [hy]))⟩
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hm
    exact h.1 (List.mem_map.mpr ⟨y, hy, hg y (by simp [hy]) a (by simp) hya⟩)

theorem vecEq_rfl (P : Pt) (a : Vec) : P.vecEq a a = true := vecEq_of_vec P rfl

theorem dot_unit [Fact P.p.Prime] (f : Vec) {b : Nat} (hb : b < P.D) :
    P.dot (P.vec f) (P.vec (P.unit b)) = P.vec f ⟨b, hb⟩ := by
  rw [Pt.vec_unit P ⟨b, hb⟩, dot_single]

theorem refl_fix [Fact P.p.Prime] (r : Refl) {b : Nat} (hb : b < P.D) (h : r.f.getD b 0 % P.p = 0) :
    P.vecEq (P.applyRefl r (P.unit b)) (P.unit b) = true := by
  apply vecEq_of_vec
  rw [vec_refl, dot_unit _ hb]
  have h0 : P.vec r.f ⟨b, hb⟩ = 0 := by
    simp only [Pt.vec]
    rw [← ZMod.natCast_mod, h, Nat.cast_zero]
  rw [h0, zero_smul, sub_zero]

@[expose] def lev (P : Pt) (Dl : List CE) (b : Nat) (idx : List Nat) (T : List TE) : Level :=
  ⟨P.unit b, idx.map (fun i => sw (Dl.getD i dfl)), T⟩

theorem levelOK_of [Fact P.p.Prime] (hwf : P.WF) (hp' : P.p < 65536) {km : Nat} {Dl : List CE}
    (hs : ∀ x ∈ Dl, Sem P x) {bs : List Nat} (hbs : ∀ b ∈ bs, b < P.D) {b : Nat} {idx : List Nat}
    (hidx : ∀ i ∈ idx, i < Dl.length)
    (hfix : ∀ i ∈ idx, ∀ c ∈ bs, (Dl.getD i dfl).1.f.getD c 0 % P.p = 0) {T : List TE}
    (hT : TFin P km (idx.map fun i => (Dl.getD i dfl).1) (P.unit b) T) :
    P.levelOK (bs.map P.unit) (lev P Dl b idx T) = true := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  have hsem : ∀ i ∈ idx, Sem P (Dl.getD i dfl) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (hidx i hi)]
    exact hs _ (List.getElem_mem _)
  unfold Pt.levelOK
  simp only [lev, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro s hs'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs'
    exact sw_ok (hsem i hi)
  · intro s hs' v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    apply vecEq_of_vec
    rw [sw_act hwf (hsem i hi)]
    exact vec_of_vecEq P (refl_fix _ (hbs c hc) (hfix i hi c hc))
  · obtain ⟨t, rfl⟩ : ∃ t, T = (P.unit b, 0, 0) :: t := by
      have := hT.q6
      cases T with
      | nil => cases this
      | cons a t => exact ⟨t, by simp at this; rw [this]⟩
    exact vecEq_rfl P _
  · intro x hx
    obtain ⟨hlt, hxe⟩ := List.mem_zipIdx' hx
    rcases Nat.eq_zero_or_pos x.2 with h0 | h0
    · simp [h0]
    · obtain ⟨a1, a2, a3⟩ := hT.q5 x.2 hlt h0
      simp only [List.length_map] at a2
      rw [hxe]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.length_map]
      refine Or.inr ⟨⟨a1, a2⟩, ?_⟩
      have e1 : (idx.map fun i => (Dl.getD i dfl).1).getD T[x.2].2.2 ⟨[], []⟩ =
          (Dl.getD idx[T[x.2].2.2] dfl).1 := by
        rw [List.getD_eq_getElem _ _ (by simpa using a2), List.getElem_map]
      have e2 : (idx.map fun i => sw (Dl.getD i dfl)).getD T[x.2].2.2 [] =
          sw (Dl.getD idx[T[x.2].2.2] dfl) := by
        rw [List.getD_eq_getElem _ _ (by simpa using a2), List.getElem_map]
      rw [a3, e1, e2]
      apply vecEq_of_vec
      rw [sw_act hwf (hsem _ (List.getElem_mem _))]
      rfl
  · rw [beq_iff_eq, eraseDups_of_nodup, List.length_map]
    refine nodup_map_of (f := fun e => pkP P.p P.D e.1 % km) hT.q3 ?_
    intro x _ y _ hxy
    rw [(pkP_inj hp0 hp' x.1 y.1).mpr (vecEq_of_code P hp0 hxy)]

theorem chainM_cons (F : Fd) (km D nC : Nat) (C : List (Nat × Nat)) (L : Nat × List Nat × List Nat)
    (lv : List (Nat × List Nat × List Nat)) (E prod : Nat) :
    chainM F km D nC C (L :: lv) E prod =
      bif Nat.blt L.1 D && sortedLt nC L.2.1 0 &&
          (selK L.2.1 0 C).all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq (treeM F km (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2) 0) then
        chainM F km D nC C lv (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub D 1) L.1))))
          (Nat.mul prod (treeM F km (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2))
      else 0 := rfl

theorem chainM_spec [Fact P.p.Prime] {F : Fd} (hL : LaneOK F P) (hwf : P.WF) (hp' : P.p < 65536)
    {km : Nat} (Dl : List CE) (hs : ∀ x ∈ Dl, Sem P x) :
    ∀ (lv : List (Nat × List Nat × List Nat)) (bs : List Nat) (E prod : Nat),
      (∀ b ∈ bs, b < P.D) →
      (∀ f : Vec, Nat.land (pkrP P.p P.D f) E = 0 → ∀ b ∈ bs, f.getD b 0 % P.p = 0) →
      chainM F km P.D Dl.length (Dl.map fun x => packR P x.1) lv E prod ≠ 0 →
      ∃ Ls : List Level, P.chainProd (bs.map P.unit) Ls prod =
        some (chainM F km P.D Dl.length (Dl.map fun x => packR P x.1) lv E prod)
  | [], bs, E, prod, _, _, _ => ⟨[], rfl⟩
  | L :: lv, bs, E, prod, hbs, hE, h => by
    have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
    have hp2 : 2 ≤ P.p := (Fact.out : P.p.Prime).two_le
    rw [chainM_cons] at h ⊢
    set C := Dl.map fun x => packR P x.1 with hC
    cases hc : (Nat.blt L.1 P.D && sortedLt Dl.length L.2.1 0 &&
          (selK L.2.1 0 C).all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq (treeM F km (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2) 0))
    · rw [hc] at h
      exact absurd rfl h
    rw [hc] at h
    simp only [cond_true] at h ⊢
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', List.all_eq_true, Nat.beq_eq] at hc
    obtain ⟨⟨⟨hb, hsort⟩, hall⟩, ht0⟩ := hc
    have ht : treeM F km (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2 ≠ 0 := by
      intro h0
      rw [h0] at ht0
      simp at ht0
    obtain ⟨hsel, hidx⟩ := selK_spec C Dl.length L.2.1 0 hsort
    rw [List.drop_zero] at hsel
    have hSv : selK L.2.1 0 C = (L.2.1.map fun i => (Dl.getD i dfl).1).map (packR P) := by
      rw [hsel, List.map_map]
      apply List.map_congr_left
      intro i hi
      rw [hC, List.getD_eq_getElem _ _ (by simpa using hidx i hi), List.getElem_map]
      simp only [Function.comp_apply]
      rw [List.getD_eq_getElem _ _ (hidx i hi)]
    rw [hSv] at ht h ⊢
    rw [hSv] at hall
    obtain ⟨T, hT, htl⟩ := treeM_spec hL hp2 hb ht
    have hfix : ∀ i ∈ L.2.1, ∀ c ∈ bs, (Dl.getD i dfl).1.f.getD c 0 % P.p = 0 := by
      intro i hi c hc
      have := hall _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, rfl⟩)
      exact hE _ this c hc
    have hE' : ∀ f : Vec, Nat.land (pkrP P.p P.D f)
        (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub P.D 1) L.1)))) = 0 →
        ∀ c ∈ bs ++ [L.1], f.getD c 0 % P.p = 0 := by
      intro f hf c hc
      obtain ⟨h1, h2⟩ := land_lor_zero hf
      rcases List.mem_append.mp hc with hc | hc
      · exact hE f h1 c hc
      · rw [List.mem_singleton.mp hc]
        exact mask_md hp0 hp' hb f h2
    have hbs' : ∀ c ∈ bs ++ [L.1], c < P.D := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hbs c hc
      · rw [List.mem_singleton.mp hc]; exact hb
    obtain ⟨Ls, hLs⟩ := chainM_spec hL hwf hp' Dl hs lv (bs ++ [L.1]) _ _ hbs' hE' h
    refine ⟨lev P Dl L.1 L.2.1 T :: Ls, ?_⟩
    rw [Pt.chainProd, if_pos (levelOK_of hwf hp' hs hbs hidx hfix hT)]
    rw [List.map_append, List.map_singleton] at hLs
    change P.chainProd (bs.map P.unit ++ [P.unit L.1]) Ls (prod * T.length) = _
    rw [← htl]
    exact hLs

theorem getD_range_map (D : Nat) (g : Nat → Nat) {i : Nat} (hi : i < D) :
    ((List.range D).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem sig_vecs [Fact P.p.Prime] {x : CE} (hx : Sem P x) :
    P.vec (P.sigmaVecs x.2.1 x.2.2).1 = P.vec x.1.h ∧
      P.vec (P.sigmaVecs x.2.1 x.2.2).2 = P.vec x.1.f := by
  obtain ⟨_, _, hh, hf⟩ := hx
  refine ⟨hh.symm, ?_⟩
  funext i
  change ((((List.range P.D).map fun j =>
    P.dotv (gk P x).f (P.applyWord x.2.1.reverse (P.unit j))).getD i 0 : ℕ) : ZMod P.p) =
      P.vec x.1.f i
  rw [getD_range_map _ _ i.isLt, Pt.dotv_spec, ← hf, dot_unit _ i.isLt]

theorem dotv_lt' (P : Pt) (hp : 0 < P.p) (f v : Vec) : P.dotv f v < P.p := Nat.mod_lt _ hp

theorem dotv_congr [Fact P.p.Prime] {a a' b b' : Vec} (ha : P.vec a = P.vec a')
    (hb : P.vec b = P.vec b') : P.dotv a b = P.dotv a' b' := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  have h := Pt.dotv_spec P a b
  rw [ha, hb, ← Pt.dotv_spec P a' b', ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt (dotv_lt' P hp0 a b), Nat.mod_eq_of_lt (dotv_lt' P hp0 a' b')] at h

theorem cast_refl (p a b : Nat) (hp : 0 < p) :
    (((a + (p - b % p)) % p : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt b hp)), ZMod.natCast_mod,
    ZMod.natCast_self]
  ring

theorem vec_sigmaApply [Fact P.p.Prime] (cb : Vec × Vec) (v : Vec) :
    P.vec (P.sigmaApply cb v) = P.vec v - P.dot (P.vec cb.2) (P.vec v) • P.vec cb.1 := by
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  funext i
  change (((P.sigmaApply cb v).getD i 0 : ℕ) : ZMod P.p) =
    P.vec v i - P.dot (P.vec cb.2) (P.vec v) * P.vec cb.1 i
  simp only [Pt.sigmaApply]
  rw [getD_range_map _ _ i.isLt, cast_refl _ _ _ hp0, Nat.cast_mul, Pt.dotv_spec]
  simp only [Pt.ent, ZMod.natCast_mod]
  rfl

@[expose] def wv (P : Pt) (Sv : List Refl) (w : List Nat) (v : Vec) : Vec :=
  w.foldr (fun l acc => P.applyRefl (Sv.getD l ⟨[], []⟩) acc) v

theorem wordB_spec {F : Fd} (hL : LaneOK F P) (Sv : List Refl) :
    ∀ (w : List Nat), (∀ l ∈ w, l < Sv.length) → ∀ v : Vec,
      wordB F (Sv.map (packR P)) w (pkP P.p P.D v) = pkP P.p P.D (wv P Sv w v)
  | [], _, v => rfl
  | l :: w, hw, v => by
    have hl := hw l (by simp)
    change appK F (nthK (0, 0) (Sv.map (packR P)) l) (wordB F (Sv.map (packR P)) w (pkP P.p P.D v)) =
      pkP P.p P.D (P.applyRefl (Sv.getD l ⟨[], []⟩) (wv P Sv w v))
    rw [wordB_spec hL Sv w (fun x hx => hw x (by simp [hx])) v, nthK_eq',
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl]
    exact hL.app _ _ _

theorem sigmaWord_spec [Fact P.p.Prime] (S : List (Vec × Vec)) (Sv : List Refl)
    (hS : ∀ l (hl : l < S.length), P.vec S[l].1 = P.vec (Sv.getD l ⟨[], []⟩).h ∧
      P.vec S[l].2 = P.vec (Sv.getD l ⟨[], []⟩).f) :
    ∀ (w : List Nat), (∀ l ∈ w, l < S.length) → ∀ v : Vec,
      P.vec (P.sigmaWord S w v) = P.vec (wv P Sv w v)
  | [], _, v => rfl
  | l :: w, hw, v => by
    have hl := hw l (by simp)
    have ih := sigmaWord_spec S Sv hS w (fun x hx => hw x (by simp [hx])) v
    simp only [Pt.sigmaWord, wv, List.foldr_cons, List.getElem?_eq_getElem hl] at ih ⊢
    rw [vec_sigmaApply, vec_refl, ih, (hS l hl).1, (hS l hl).2]

theorem exprB_spec (F : Fd) (S : List (Nat × Nat)) (w : List Nat) (r : Nat × Nat) :
    ∀ k, exprB F S w r k = true → ∀ j < k,
      wordB F S w (Nat.shiftLeft 1 (Nat.mul 16 j)) = appK F r (Nat.shiftLeft 1 (Nat.mul 16 j))
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, h, j, hj => by
    change (Nat.beq (wordB F S w (Nat.shiftLeft 1 (Nat.mul 16 k)))
      (appK F r (Nat.shiftLeft 1 (Nat.mul 16 k))) && exprB F S w r k) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact exprB_spec F S w r k h.2 j hj
    · exact h.1

theorem pair_cond (t D i j a b p : Nat)
    (h : (bif Nat.beq (bondB t D i j) 0 then Nat.beq a 0 && Nat.beq b 0
      else Nat.beq (Nat.mod (Nat.mul a b) p) (bondB t D i j)) = true) :
    (if t == 0 then
          (if i + 1 == j || j + 1 == i then (a * b) % p == 1 else a == 0 && b == 0)
        else if t == 1 then
          (if (i == D - 1 && j == D - 2) || (j == D - 1 && i == D - 2) then
              (a * b) % p == 2
           else if i + 1 == j || j + 1 == i then (a * b) % p == 1
           else a == 0 && b == 0)
        else if t == 2 then
          (if ((i + 1 == j && j + 2 < D) || ((j + 1 == i && i + 2 < D) ||
              ((i + 3 == D && (j + 2 == D || j + 1 == D)) ||
                (j + 3 == D && (i + 2 == D || i + 1 == D))))) then
              (a * b) % p == 1
           else a == 0 && b == 0)
        else
          (if ((i == 0 && j == 2) || ((i == 2 && j == 0) || ((i == 1 && j == 3) ||
              ((i == 3 && j == 1) || ((i == 2 && j == 3) || ((i == 3 && j == 2) ||
              ((i == 3 && j == 4) || ((i == 4 && j == 3) || ((i == 4 && j == 5) ||
              ((i == 5 && j == 4) || ((i == 5 && j == 6) || (i == 6 && j == 5)))))))))))) then
              (a * b) % p == 1
           else a == 0 && b == 0)) = true := by
  unfold bondB at h
  split_ifs at h ⊢ <;> simp_all [Bool.or_assoc] <;> omega

theorem kind_lt {t D : Nat} (h : kindOK t D = true) : t < 4 := by
  unfold kindOK at h
  simp at h
  omega

end OKS

open OKS in
theorem oK_verify {F : Fd} {P : Pt} (hp : P.p.Prime) (hp3 : 3 ≤ P.p) (hp' : P.p < 65536)
    (hL : LaneOK F P) (hwf : wfCheck P = true) {bnd : Nat} {o : ORec}
    (h : oK F P.D bnd (P.gens.map fun g => (pkP P.p P.D g.h, pkrP P.p P.D g.f)) o = true) :
    (o.2.1 = 0 → ∃ w, verifyO P w bnd = true) ∧ (o.2.1 ≠ 0 → ∃ c, verifyWPos P c = true) := by
  have : Fact P.p.Prime := ⟨hp⟩
  have hp0 : 0 < P.p := hp.pos
  have hWF : P.WF := by
    intro r hr
    have h1 := List.all_eq_true.mp hwf r hr
    rw [beq_iff_eq] at h1
    rw [← Pt.dotv_spec, h1, ZMod.natCast_mod]
    simp
  unfold oK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hclo, hrest⟩ := h
  have e1 : (baseD P).length = P.gens.length := by simp [baseD]
  have hclo' : cloP F P.gens.length (P.gens.map (packR P)) o.2.2.2.1 (baseD P).length 0
      ((P.gens.map (packR P) ++ o.2.2.2.1.map ent).drop 0) = true := by
    rw [e1, List.drop_zero]
    rw [List.length_map] at hclo
    exact hclo
  have hacc : (baseD P).map (fun x => packR P x.1) =
      (P.gens.map (packR P) ++ o.2.2.2.1.map ent).take (baseD P).length := by
    rw [e1, List.take_left' (by simp)]
    apply List.ext_getElem (by simp [baseD])
    intro i h1 h2
    simp only [baseD, List.length_map, List.length_range] at h1
    simp [baseD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hdrop : (P.gens.map (packR P) ++ o.2.2.2.1.map ent).drop (baseD P).length =
      o.2.2.2.1.map ent ++ [] := by
    rw [e1, List.append_nil, List.drop_left' (by simp)]
  obtain ⟨hDl, hsem⟩ := cloP_spec hL _ o.2.2.2.1 (baseD P) 0 [] hclo' (Nat.zero_le _) hacc hdrop
    sem_base
  have hlen : (cloD P (baseD P) o.2.2.2.1).length =
      Nat.add (P.gens.map fun g => (pkP P.p P.D g.h, pkrP P.p P.D g.f)).length o.2.2.2.1.length := by
    rw [length_cloD, e1, List.length_map]
    rfl
  have hC : (cloD P (baseD P) o.2.2.2.1).map (fun x => packR P x.1) =
      P.gens.map (packR P) ++ o.2.2.2.1.map ent := by
    rw [hDl, List.take_of_length_le]
    simp [e1]
  generalize cloD P (baseD P) o.2.2.2.1 = Dl at hlen hC hsem
  have hrest' : (bif Nat.beq o.2.1 0 then
      Nat.blt bnd (chainM F o.2.2.1 P.D Dl.length (Dl.map fun x => packR P x.1) o.2.2.2.2.1 0 1)
      else wPosK F o.2.2.1 P.D Dl.length (Nat.sub o.2.1 1) (P.gens.map (packR P))
        (Dl.map fun x => packR P x.1) o.2.2.2.2.2.1 o.2.2.2.2.2.2 o.2.2.2.2.1) = true := by
    rw [hC, hlen]
    exact hrest
  clear hrest hclo hclo' hacc hdrop hDl
  constructor
  · intro h0
    have hb : Nat.beq o.2.1 0 = true := by rw [h0]; rfl
    rw [hb, cond_true, Nat.blt_eq] at hrest'
    obtain ⟨Ls, hLs⟩ := chainM_spec (km := o.2.2.1) hL hWF hp' Dl hsem o.2.2.2.2.1 [] 0 1
      (by simp) (by simp) (by omega)
    simp only [List.map_nil] at hLs
    refine ⟨⟨Ls⟩, ?_⟩
    unfold verifyO
    rw [hLs]
    exact decide_eq_true hrest'
  · intro h0
    have hb : Nat.beq o.2.1 0 = false := by
      rw [Bool.eq_false_iff]
      intro hq
      exact h0 (Nat.eq_of_beq_eq_true hq)
    rw [hb, cond_false] at hrest'
    unfold wPosK at hrest'
    simp only [Bool.and_eq_true] at hrest'
    obtain ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := hrest'
    set t := Nat.sub o.2.1 1
    set sig := o.2.2.2.2.2.1
    set expr := o.2.2.2.2.2.2
    have hsig : ∀ i ∈ sig, i < Dl.length := by
      intro i hi
      have := List.all_eq_true.mp k3 i hi
      rwa [Nat.blt_eq] at this
    have hsigl : sig.length = P.D := Nat.eq_of_beq_eq_true k2
    let xs := sig.map fun i => Dl.getD i dfl
    have hxs : ∀ x ∈ xs, Sem P x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [List.getD_eq_getElem _ _ (hsig i hi)]
      exact hsem _ (List.getElem_mem _)
    have hxl : xs.length = P.D := by simp [xs, hsigl]
    have hSK : sig.map (nthK (0, 0) (Dl.map fun x => packR P x.1)) = (xs.map (·.1)).map (packR P) := by
      simp only [xs, List.map_map]
      apply List.map_congr_left
      intro i hi
      rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hsig i hi), List.getElem_map,
        Function.comp_apply, Function.comp_apply, List.getD_eq_getElem _ _ (hsig i hi)]
    rw [hSK] at k4 k5 k7
    set Sv := xs.map (·.1) with hSv
    have hSvl : Sv.length = P.D := by simp [hSv, hxl]
    have k8' : Nat.sub (wOrd t P.D) 1 <
        chainM F o.2.2.1 P.D Dl.length (Dl.map fun x => packR P x.1) o.2.2.2.2.1 0 1 := by
      rwa [Nat.blt_eq] at k8
    obtain ⟨Ls, hLs⟩ := chainM_spec (km := o.2.2.1) hL hWF hp' Dl hsem o.2.2.2.2.1 [] 0 1
      (by simp) (by simp) (by omega)
    simp only [List.map_nil] at hLs
    have hgetx : ∀ i (hi : i < xs.length), P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 =
        P.vec (Sv.getD i ⟨[], []⟩).h ∧ P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 =
        P.vec (Sv.getD i ⟨[], []⟩).f := by
      intro i hi
      have e : Sv.getD i ⟨[], []⟩ = xs[i].1 := by
        simp [hSv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [e]
      exact sig_vecs (hxs _ (List.getElem_mem _))
    refine ⟨⟨t, xs.map (fun x => (x.2.1, x.2.2)), expr, ⟨Ls⟩⟩, ?_⟩
    unfold verifyWPos
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩, ?_⟩
    · exact decide_eq_true (kind_lt k1)
    · exact k1
    · rw [beq_iff_eq, List.length_map]
      exact hxl
    · rw [List.all_eq_true]
      intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      have := hxs x hx
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨this.1, this.2.1⟩
    · rw [List.all_eq_true]
      intro cb hcb
      simp only [List.map_map, List.mem_map] at hcb
      obtain ⟨x, hx, rfl⟩ := hcb
      have hsx := sig_vecs (hxs x hx)
      have h2 := List.all_eq_true.mp k4 (packR P x.1)
        (List.mem_map.mpr ⟨x.1, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
      unfold reflOK at h2
      rw [Nat.beq_eq] at h2
      change dotK F (pkrP P.p P.D x.1.f) (pkP P.p P.D x.1.h) = 2 at h2
      rw [hL.dot] at h2
      rw [beq_iff_eq, Function.comp_apply, dotv_congr hsx.2 hsx.1, h2, Nat.mod_eq_of_lt (by omega)]
    · rw [List.all_eq_true]
      intro i hi
      rw [List.all_eq_true]
      intro j hj
      have k5ij := List.all_eq_true.mp (List.all_eq_true.mp k5 i hi) j hj
      rw [List.mem_range] at hi hj
      rw [Bool.or_eq_true] at k5ij ⊢
      rcases k5ij with k | k
      · left
        rw [Nat.beq_eq] at k
        rw [k, beq_self_eq_true]
      · right
        have hiS : i < Sv.length := by omega
        have hjS : j < Sv.length := by omega
        have hl : (xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2) =
            xs.map fun x => P.sigmaVecs x.2.1 x.2.2 := by
          rw [List.map_map]
          rfl
        have hgi : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD i
            ([], []) = P.sigmaVecs xs[i].2.1 xs[i].2.2 := by
          rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
        have hgj : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD j
            ([], []) = P.sigmaVecs xs[j].2.1 xs[j].2.2 := by
          rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
        have hnK : ∀ l (hl : l < Sv.length), nthK (0, 0) (Sv.map (packR P)) l =
            packR P (Sv.getD l ⟨[], []⟩) := by
          intro l hl
          rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
            List.getD_eq_getElem _ _ hl]
        have ha : dotK F (nthK (0, 0) (Sv.map (packR P)) i).2 (nthK (0, 0) (Sv.map (packR P)) j).1 =
            P.dotv (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 (P.sigmaVecs xs[j].2.1 xs[j].2.2).1 := by
          rw [hnK i hiS, hnK j hjS]
          change dotK F (pkrP P.p P.D _) (pkP P.p P.D _) = _
          rw [hL.dot, dotv_congr (hgetx i (by omega)).2 (hgetx j (by omega)).1]
        have hb : dotK F (nthK (0, 0) (Sv.map (packR P)) j).2 (nthK (0, 0) (Sv.map (packR P)) i).1 =
            P.dotv (P.sigmaVecs xs[j].2.1 xs[j].2.2).2 (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 := by
          rw [hnK i hiS, hnK j hjS]
          change dotK F (pkrP P.p P.D _) (pkP P.p P.D _) = _
          rw [hL.dot, dotv_congr (hgetx j (by omega)).2 (hgetx i (by omega)).1]
        have hpc := pair_cond t P.D i j
          (dotK F (nthK (0, 0) (Sv.map (packR P)) i).2 (nthK (0, 0) (Sv.map (packR P)) j).1)
          (dotK F (nthK (0, 0) (Sv.map (packR P)) j).2 (nthK (0, 0) (Sv.map (packR P)) i).1) F.p k
        rw [ha, hb, hL.fp] at hpc
        simp only [hgi, hgj]
        exact hpc
    · rw [beq_iff_eq]
      have := Nat.eq_of_beq_eq_true k6
      rwa [List.length_map] at this
    · rw [List.all_eq_true]
      intro x hx
      obtain ⟨w, r⟩ := x
      have hm : (w, packR P r) ∈ expr.zip (P.gens.map (packR P)) := by
        rw [List.zip_map_right]
        exact List.mem_map.mpr ⟨(w, r), hx, rfl⟩
      have h7 := List.all_eq_true.mp k7 _ hm
      simp only [Bool.and_eq_true] at h7
      obtain ⟨hw, he⟩ := h7
      have hw' : ∀ l ∈ w, l < P.D := by
        intro l hl
        have := List.all_eq_true.mp hw l hl
        rwa [Nat.blt_eq] at this
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      refine ⟨hw', fun j hj => ?_⟩
      rw [List.mem_range] at hj
      have hej := exprB_spec F _ w _ P.D he j hj
      rw [shiftLeft_unitP P (by omega) hj, wordB_spec hL Sv w (fun l hl => hSvl ▸ hw' l hl)] at hej
      change _ = appK F (pkP P.p P.D r.h, pkrP P.p P.D r.f) _ at hej
      rw [hL.app] at hej
      have hv := vec_of_vecEq P ((pkP_inj hp0 hp' _ _).mp hej)
      apply vecEq_of_vec
      have hSMl : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).length =
          P.D := by simp [hxl]
      have hSM : ∀ l (hl : l < ((xs.map fun x => (x.2.1, x.2.2)).map
          (fun s => P.sigmaVecs s.1 s.2)).length),
          P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].1 =
            P.vec (Sv.getD l ⟨[], []⟩).h ∧
          P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].2 =
            P.vec (Sv.getD l ⟨[], []⟩).f := by
        intro l hl
        simp only [List.getElem_map]
        exact hgetx l (by simpa using hl)
      rw [sigmaWord_spec _ Sv hSM w (fun l hl => hSMl ▸ hw' l hl) (P.unit j), hv]
    · unfold verifyO
      rw [hLs]
      exact decide_eq_true k8'

end CFSG.TwoNodeSmall.PosBK

end
