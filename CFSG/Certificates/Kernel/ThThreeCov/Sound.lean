module

public import Certificates.Data.Kernel.ThThreeCov.Defs
public import Certificates.Data.Kernel.ThThreeCov.Sim
public import CFSG.Certificates.Kernel.Th.ExprSound
public import CFSG.Certificates.Kernel.ThThreeCov.Cover
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

public section

namespace CFSG.KC.ThThreeCov

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.KC.Th CFSG.KC.Th.Spec CFSG.KC.Th.Expr
  CFSG.SectionRank.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem andB_t {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem orB_t {a b : Bool} (h : CFSG.KC.Th.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem beq_t {m n : Nat} (h : Nat.beq m n = true) : m = n := Nat.eq_of_beq_eq_true h

theorem blt_t {m n : Nat} (h : Nat.blt m n = true) : m < n := Nat.le_of_ble_eq_true h

theorem lenR_eq {α : Type} (l : List α) : lenR l = l.length := by
  induction l with
  | nil => rfl
  | cons _ l ih => exact congrArg Nat.succ ih

theorem listAll_t {α : Type} {F : α → Bool} : ∀ {l : List α},
    List.rec (motive := fun _ => Bool) true (fun e _ acc => CFSG.KC.Th.andB (F e) acc) l = true →
      ∀ e ∈ l, F e = true
  | [], _, _, h => nomatch h
  | e :: l, h, e', he => by
    obtain ⟨h1, h2⟩ := andB_t h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact listAll_t h2 e' he

theorem listAny_t {α : Type} {F : α → Bool} : ∀ {l : List α},
    List.rec (motive := fun _ => Bool) false (fun e _ acc => CFSG.KC.Th.orB (F e) acc) l = true →
      ∃ e ∈ l, F e = true
  | [], h => absurd h Bool.false_ne_true
  | e :: l, h => by
    rcases orB_t h with h | h
    · exact ⟨e, List.mem_cons.2 (Or.inl rfl), h⟩
    · obtain ⟨e', he', h'⟩ := listAny_t h
      exact ⟨e', List.mem_cons.2 (Or.inr he'), h'⟩

theorem natRec_t {F : Nat → Bool} : ∀ m : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun j acc => CFSG.KC.Th.andB acc (F j)) m = true →
      ∀ j < m, F j = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, h, j, hj => by
    obtain ⟨h1, h2⟩ := andB_t h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact natRec_t m h1 j hj
    · exact h2

theorem allLt_t {n : Nat} {l : List Nat} (h : allLt n l = true) : ∀ r ∈ l, r < n :=
  fun r hr => blt_t (listAll_t (F := fun r => Nat.blt r n) h r hr)

theorem memB_t {x : Nat} {l : List Nat} (h : memB x l = true) : x ∈ l := by
  obtain ⟨r, hr, e⟩ := listAny_t (F := fun r => Nat.beq r x) h
  exact beq_t e ▸ hr

theorem memE_t {x : Nat} {E : List (Nat × Nat × List Nat)} (h : memE x E = true) :
    ∃ e ∈ E, x ∈ e.2.2 := by
  obtain ⟨e, he, h⟩ := listAny_t (F := fun e : Nat × Nat × List Nat => memB x e.2.2) h
  exact ⟨e, he, memB_t h⟩

theorem defs_all {k : K} {R : Nat → Nat} {D : List (List Nat)} (hl : lenR D ≤ 224)
    (h : ∀ c < 14, defsChunk k R D c = true) :
    ∀ i < lenR D, defOK k R i (D.getD i []) = true := by
  intro i hi
  have hc : Bool.rec true (defOK k R (16 * (i / 16) + i % 16) (D.getD (16 * (i / 16) + i % 16) []))
      (Nat.blt (16 * (i / 16) + i % 16) (lenR D)) = true :=
    natRec_t (F := fun j => Bool.rec true (defOK k R (16 * (i / 16) + j)
      (D.getD (16 * (i / 16) + j) [])) (Nat.blt (16 * (i / 16) + j) (lenR D))) 16
      (h (i / 16) (by omega)) (i % 16) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod i 16] at hc
  have hb : Nat.blt i (lenR D) = true := Nat.ble_eq_true_of_le hi
  rw [hb] at hc
  exact hc

theorem freshLt_t {n : Nat} : ∀ {l : List Nat} {m : Nat}, freshLt n l m = true →
    (∀ o ∈ l, o < n ∧ m.testBit o = false) ∧ l.Nodup
  | [], _, _ => ⟨fun _ h => (nomatch h), List.nodup_nil⟩
  | o :: l, m, h => by
    obtain ⟨h1, h⟩ := andB_t h
    obtain ⟨h2, h3⟩ := andB_t h
    obtain ⟨ih1, ih2⟩ := freshLt_t h3
    have hbit : m.testBit o = false := by
      have e : (m >>> o) &&& 1 = 0 := beq_t h2
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at e
      rw [Nat.testBit_eq_decide_div_mod_eq, e]
      rfl
    have hnew : ∀ o' ∈ l, o' ≠ o ∧ m.testBit o' = false := fun o' ho' => by
      have e : (m ||| 1 <<< o).testBit o' = false := (ih1 o' ho').2
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at e
      exact ⟨fun h => e.2 h.symm, e.1⟩
    refine ⟨fun o' ho' => ?_, List.nodup_cons.2 ⟨fun ho => (hnew o ho).1 rfl, ih2⟩⟩
    rcases List.mem_cons.1 ho' with rfl | ho'
    · exact ⟨blt_t h1, hbit⟩
    · exact ⟨(ih1 o' ho').1, (hnew o' ho').2⟩

theorem ord_surj {ord : List Nat} (hlen : ord.length = 81) (h : freshLt 81 ord 0 = true) :
    ∀ m < 81, ∃ p < 81, ord.getD p 0 = m := by
  obtain ⟨hlt, hnd⟩ := freshLt_t h
  have hsub : ord.toFinset ⊆ Finset.range 81 := fun o ho =>
    Finset.mem_range.2 (hlt o (List.mem_toFinset.1 ho)).1
  have heq : ord.toFinset = Finset.range 81 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [List.toFinset_card_of_nodup hnd, hlen]; simp)
  intro m hm
  have hmem : m ∈ ord := List.mem_toFinset.1 (heq ▸ Finset.mem_range.2 hm)
  obtain ⟨p, hp, e⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨p, hlen ▸ hp, by rw [List.getD_eq_getElem _ _ hp, e]⟩

structure IsPk (P : Nat) (g : J) : Prop where
  lay : InLayout P
  eq : pkMat P = toMat g

variable {k : K}

theorem IsPk.mul' (hk : Ctx k) {P Q : Nat} {g h : J} (hP : IsPk P g) (hQ : IsPk Q h) :
    IsPk (k.mul P Q) (g * h) :=
  ⟨hk.lay P Q, by rw [hk.mul, hP.eq, hQ.eq, toMat_mul]⟩

theorem IsPk.one' (hk : Ctx k) : IsPk k.ONE 1 := ⟨hk.layOne, by rw [hk.one, toMat_one]⟩

theorem IsPk.elt_eq {P Q : Nat} {g h : J} (hP : IsPk P g) (hQ : IsPk Q h) (e : P = Q) : g = h :=
  toMat_injective (by rw [← hP.eq, ← hQ.eq, e])

theorem IsPk.nat_eq {P Q : Nat} {g h : J} (hP : IsPk P g) (hQ : IsPk Q h) (e : g = h) : P = Q :=
  pkMat_inj hP.lay hQ.lay (by rw [hP.eq, hQ.eq, e])

theorem isPk_te (hk : Ctx k) {e : TE} {g : J} (h : IsRows e.rows g) : IsPk (e.pk k) g :=
  ⟨lay_pk hk e, (pk_sound hk e).trans h.eq⟩

theorem isPk_prodR (hk : Ctx k) {R : Nat → Nat} {g : Nat → J} :
    ∀ l : List Nat, (∀ r ∈ l, IsPk (R r) (g r)) → IsPk (prodR k R l) (l.map g).prod
  | [], _ => IsPk.one' hk
  | r :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact (h r (List.mem_cons.2 (Or.inl rfl))).mul' hk
      (isPk_prodR hk l fun s hs => h s (List.mem_cons.2 (Or.inr hs)))

theorem regs_sound (hk : Ctx k) {R : Nat → Nat}
    {D : List (List Nat)} (hs : seedsOK k R = true)
    (hd : ∀ i < lenR D, defOK k R i (D.getD i []) = true) :
    ∃ g : Nat → J, (∀ r < 5 + lenR D, IsPk (R r) (g r)) ∧ g 0 = a ∧ g 1 = b ∧ g 2 = x ∧
      g 3 = y ∧ ∀ i < lenR D, g (5 + i) = ((D.getD i []).map g).prod := by
  obtain ⟨e0, hs⟩ := andB_t hs
  obtain ⟨e1, hs⟩ := andB_t hs
  obtain ⟨e2, hs⟩ := andB_t hs
  obtain ⟨e3, e4⟩ := andB_t hs
  have key : ∀ m ≤ lenR D, ∃ g : Nat → J, (∀ r < 5 + m, IsPk (R r) (g r)) ∧ g 0 = a ∧
      g 1 = b ∧ g 2 = x ∧ g 3 = y ∧ ∀ i < m, g (5 + i) = ((D.getD i []).map g).prod := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun r => if r = 0 then a else if r = 1 then b else if r = 2 then x
        else if r = 3 then y else y ^ 5, fun r hr => ?_, rfl, rfl, rfl, rfl,
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      interval_cases r
      · rw [beq_t e0]
        exact isPk_te hk isRows_a
      · rw [beq_t e1]
        exact isPk_te hk isRows_b
      · rw [beq_t e2]
        exact isPk_te hk isRows_x
      · rw [beq_t e3]
        exact isPk_te hk isRows_y
      · rw [beq_t e4]
        exact isPk_te hk (isRows_y.pow 5)
    | succ m ih =>
      intro hm
      obtain ⟨g, hR, ga, gb, gx, gy, hg⟩ := ih (by omega)
      have hdm := andB_t (hd m (by omega))
      have hpk := isPk_prodR hk (D.getD m []) fun r hr => hR r (allLt_t hdm.1 r hr)
      let g' : Nat → J := fun r => if r = 5 + m then ((D.getD m []).map g).prod else g r
      have hgg : ∀ r < 5 + m, g' r = g r := fun r hr => if_neg (by omega)
      have hmap : ∀ i ≤ m, (D.getD i []).map g' = (D.getD i []).map g := fun i hi =>
        List.map_congr_left fun r hr => hgg r (by
          have := allLt_t (andB_t (hd i (by omega))).1 r hr
          omega)
      have hnew : g' (5 + m) = ((D.getD m []).map g).prod := if_pos rfl
      refine ⟨g', fun r hr => ?_, (hgg 0 (by omega)).trans ga, (hgg 1 (by omega)).trans gb,
        (hgg 2 (by omega)).trans gx, (hgg 3 (by omega)).trans gy, fun i hi => ?_⟩
      · by_cases hrm : r = 5 + m
        · rw [hrm, hnew, beq_t hdm.2]
          exact hpk
        · rw [hgg r (by omega)]
          exact hR r (by omega)
      · rw [hmap i (by omega)]
        by_cases him : i = m
        · rw [him, hnew]
        · rw [hgg (5 + i) (by omega)]
          exact hg i (by omega)
  obtain ⟨g, hR, ga, gb, gx, gy, hg⟩ := key (lenR D) le_rfl
  exact ⟨g, hR, ga, gb, gx, gy, hg⟩

theorem tab_sound (hk : Ctx k) {R : Nat → Nat} {g : Nat → J} {n tb g1 g2 kv : Nat}
    {tpar tgen cl ord : List Nat} (hR : ∀ r < n, IsPk (R r) (g r))
    (hG : tabGlobal k R n tb g1 g2 ord = true)
    (hT : ∀ j < 81, tabRow k R tb g1 g2 kv tpar tgen cl ord j = true) :
    TabFacts (fun j => g (tb + j)) (fun i => g (genR g1 g2 i)) := by
  obtain ⟨hn, hG⟩ := andB_t hG
  obtain ⟨hg1, hG⟩ := andB_t hG
  obtain ⟨hg2, hG⟩ := andB_t hG
  obtain ⟨h0, hG⟩ := andB_t hG
  obtain ⟨hlen, hfresh⟩ := andB_t hG
  have hn : tb + 81 ≤ n := Nat.le_of_ble_eq_true hn
  have hg1 := blt_t hg1
  have hg2 := blt_t hg2
  have hlen : ord.length = 81 := (lenR_eq ord).symm.trans (beq_t hlen)
  have hrow := fun j (hj : j < 81) => andB_t (hT j hj)
  refine ⟨(hR tb (by omega)).elt_eq (IsPk.one' hk) (beq_t h0), fun j hj0 hj => ?_,
    fun j hj i hi => ?_, fun j hj l hl e => ?_⟩
  · obtain ⟨h1, -⟩ := hrow j hj
    cases hb : Nat.beq j 0
    · rw [hb] at h1
      obtain ⟨hp, h1⟩ := andB_t h1
      obtain ⟨hgn, h1⟩ := andB_t h1
      have hp := blt_t hp
      have hgn := blt_t hgn
      have hgr : genR g1 g2 (tgen.getD j 0) < n := by
        unfold genR
        cases Nat.beq (tgen.getD j 0) 0
        · exact hg2
        · exact hg1
      exact ⟨tpar.getD j 0, hp, tgen.getD j 0, hgn,
        (hR _ (by omega)).elt_eq ((hR _ (by omega)).mul' hk (hR _ hgr)) (beq_t h1)⟩
    · exact absurd (beq_t hb) (by omega)
  · obtain ⟨-, h2⟩ := hrow j hj
    obtain ⟨hc0, h2⟩ := andB_t h2
    obtain ⟨hc1, -⟩ := andB_t h2
    interval_cases i
    · obtain ⟨hl, he⟩ := andB_t hc0
      have hl := blt_t hl
      exact ⟨cl.getD (2 * j) 0, hl,
        ((hR _ (by omega)).mul' hk (hR _ hg1)).elt_eq (hR _ (by omega)) (beq_t he)⟩
    · obtain ⟨hl, he⟩ := andB_t hc1
      have hl := blt_t hl
      exact ⟨cl.getD (2 * j + 1) 0, hl,
        ((hR _ (by omega)).mul' hk (hR _ hg2)).elt_eq (hR _ (by omega)) (beq_t he)⟩
  · have hkey : ∀ p < 80, vecB k.rm kv (R (tb + ord.getD p 0)) <
        vecB k.rm kv (R (tb + ord.getD (p + 1) 0)) := fun p hp => by
      obtain ⟨-, h2⟩ := hrow p (by omega)
      obtain ⟨-, h2⟩ := andB_t h2
      obtain ⟨-, h2⟩ := andB_t h2
      have hb : Nat.blt p 80 = true := Nat.ble_eq_true_of_le hp
      rw [hb] at h2
      exact blt_t h2
    have hmono : ∀ p q, p < q → q < 81 → vecB k.rm kv (R (tb + ord.getD p 0)) <
        vecB k.rm kv (R (tb + ord.getD q 0)) := by
      intro p q hpq hq
      induction q with
      | zero => omega
      | succ q ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with h | rfl
        · exact (ih h (by omega)).trans (hkey q (by omega))
        · exact hkey p (by omega)
    obtain ⟨p, hp, rfl⟩ := ord_surj hlen hfresh j hj
    obtain ⟨q, hq, rfl⟩ := ord_surj hlen hfresh l hl
    have eR : R (tb + ord.getD p 0) = R (tb + ord.getD q 0) :=
      (hR _ (by omega)).nat_eq (hR _ (by omega)) e
    rcases lt_trichotomy p q with h | h | h
    · have := hmono p q h hq
      rw [eR] at this
      exact absurd this (lt_irrefl _)
    · rw [h]
    · have := hmono q p h hp
      rw [eR] at this
      exact absurd this (lt_irrefl _)

theorem invs_sound (hk : Ctx k) {R : Nat → Nat} {g : Nat → J} {n : Nat}
    (hR : ∀ r < n, IsPk (R r) (g r)) {I : List (Nat × Nat)} (h : invsOK k R n I = true) :
    ∀ p ∈ I, p.1 < n ∧ p.2 < n ∧ g p.1 * g p.2 = 1 := by
  intro p hp
  obtain ⟨a1, h1⟩ := andB_t (listAll_t (F := fun p : Nat × Nat => CFSG.KC.Th.andB
    (Nat.blt p.1 n) (CFSG.KC.Th.andB (Nat.blt p.2 n) (Nat.beq (k.mul (R p.1) (R p.2)) k.ONE)))
    h p hp)
  obtain ⟨a2, h1⟩ := andB_t h1
  exact ⟨blt_t a1, blt_t a2,
    ((hR _ (blt_t a1)).mul' hk (hR _ (blt_t a2))).elt_eq (IsPk.one' hk) (beq_t h1)⟩

theorem cls_sound (hk : Ctx k) {R : Nat → Nat} {g : Nat → J} {n tb : Nat}
    {I : List (Nat × Nat)} {cl : Nat × List (Nat × Nat × List Nat) × List Nat × List Nat}
    (hR : ∀ r < n, IsPk (R r) (g r)) (h2 : g 2 = x) (h3 : g 3 = y) (hn : tb + 81 ≤ n)
    (hn3 : 3 < n) (hI : invsOK k R n I = true) (h : clsOK k R n tb I cl = true) :
    ClassGen (fun j => g (tb + j)) (g cl.1) := by
  obtain ⟨hrep, h⟩ := andB_t h
  obtain ⟨hents, h⟩ := andB_t h
  obtain ⟨hw, hp⟩ := andB_t h
  obtain ⟨hwx, hwy⟩ := andB_t hw
  obtain ⟨hpx, hpy⟩ := andB_t hp
  have hrep := blt_t hrep
  have hinv := invs_sound hk hR hI
  have hentF : ∀ e ∈ cl.2.1, e.1 < 81 ∧ IsConj (g cl.1) (g (tb + e.1)) ∧
      ∀ z ∈ e.2.2, z < n ∧ g z * g (tb + e.1) = g (tb + e.1) * g z := by
    intro e he
    obtain ⟨h1, h⟩ := andB_t (listAll_t (F := entOK k R n tb cl.1) hents e he)
    obtain ⟨h2, h⟩ := andB_t h
    obtain ⟨h3, h4⟩ := andB_t h
    have h1 := blt_t h1
    have h2 := blt_t h2
    have hT := hR (tb + e.1) (by omega)
    refine ⟨h1, isConj_iff.2 ⟨(g e.2.1)⁻¹, ?_⟩, fun z hz => ?_⟩
    · have e' := ((hR _ hrep).mul' hk (hR _ h2)).elt_eq ((hR _ h2).mul' hk hT) (beq_t h3)
      rw [inv_inv, mul_assoc, e', ← mul_assoc, inv_mul_cancel, one_mul]
    · obtain ⟨hz1, hz2⟩ := andB_t (listAll_t (F := fun z => CFSG.KC.Th.andB (Nat.blt z n)
        (Nat.beq (k.mul (R z) (R (tb + e.1))) (k.mul (R (tb + e.1)) (R z)))) h4 z hz)
      have hz1 := blt_t hz1
      exact ⟨hz1, ((hR _ hz1).mul' hk hT).elt_eq (hT.mul' hk (hR _ hz1)) (beq_t hz2)⟩
  let Z : Set J := {u | ∃ e ∈ cl.2.1, ∃ z ∈ e.2.2, u = g z}
  have hlet : ∀ w, wordIn I cl.2.1 w = true → ∀ l ∈ w, l < n ∧ g l ∈ Subgroup.closure Z := by
    intro w hw l hl
    rcases orB_t (listAll_t (F := inZs I cl.2.1) hw l hl) with hz | hz
    · obtain ⟨e, he, hle⟩ := memE_t hz
      exact ⟨((hentF e he).2.2 l hle).1, Subgroup.subset_closure ⟨e, he, l, hle, rfl⟩⟩
    · obtain ⟨p, hp, hz⟩ := listAny_t
        (F := fun p : Nat × Nat => CFSG.KC.Th.andB (Nat.beq p.2 l) (memE p.1 cl.2.1)) hz
      obtain ⟨hpl, hz⟩ := andB_t hz
      obtain ⟨e, he, hpe⟩ := memE_t hz
      obtain ⟨-, hp2, hpp⟩ := hinv p hp
      rw [← beq_t hpl]
      refine ⟨hp2, ?_⟩
      have hm := (Subgroup.closure Z).inv_mem (Subgroup.subset_closure ⟨e, he, p.1, hpe, rfl⟩)
      have hinv' : g p.2 = (g p.1)⁻¹ := eq_inv_of_mul_eq_one_right hpp
      rw [← hinv'] at hm
      exact hm
  have hword : ∀ w, wordIn I cl.2.1 w = true → ∀ {v : J} {r : Nat}, r < n → g r = v →
      Nat.beq (prodR k R w) (R r) = true → v ∈ Subgroup.closure Z := by
    intro w hw v r hr hv he
    have e' := (isPk_prodR hk w fun l hl => hR l (hlet w hw l hl).1).elt_eq (hR r hr) (beq_t he)
    rw [← hv, ← e']
    refine Subgroup.list_prod_mem _ fun u hu => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hu
    exact (hlet w hw l hl).2
  refine ⟨Z, ?_, hword _ hwx (by omega) h2 hpx, hword _ hwy hn3 h3 hpy⟩
  rintro _ ⟨e, he, z, hz, rfl⟩
  obtain ⟨h1, hc, hcomm⟩ := hentF e he
  exact ⟨e.1, h1, hc, (hcomm z hz).2⟩

theorem sim_sound {D : List (List Nat)} {g : Nat → J}
    (hdef : ∀ i < D.length, g (5 + i) = ((D.getD i []).map g).prod) :
    ∀ (p : List Op) (ψ : Nat → Nat) (f : Nat) (RJ : Nat → J), simOK D ψ f p = true →
      (∀ r, RJ r = g (ψ r)) → ∀ r, p.foldl opJ RJ r = g (simMap ψ f p r)
  | [], _, _, _, _, hRJ => hRJ
  | o :: p, ψ, f, RJ, h, hRJ => by
    simp only [simOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h5, hlt⟩, hD⟩, hp⟩ := h
    have hf : g f = ((opLetters ψ o).map g).prod := by
      have := hdef (f - 5) hlt
      rwa [Nat.add_sub_cancel' h5, hD] at this
    refine sim_sound hdef p _ _ _ hp fun r => ?_
    cases o with
    | mul i j o =>
      by_cases hr : r = o
      · simp only [opJ, updMap, opOut, Function.update_apply, hr, ↓reduceIte]
        rw [hf, hRJ, hRJ]
        simp [opLetters]
      · simp only [opJ, updMap, opOut, Function.update_apply, hr, ↓reduceIte]
        exact hRJ r
    | pow e i o =>
      by_cases hr : r = o
      · simp only [opJ, updMap, opOut, Function.update_apply, hr, ↓reduceIte]
        rw [hf, hRJ]
        simp [opLetters, List.map_replicate, List.prod_replicate]
      · simp only [opJ, updMap, opOut, Function.update_apply, hr, ↓reduceIte]
        exact hRJ r

theorem slp_link {D : List (List Nat)} {g : Nat → J}
    (hdef : ∀ i < D.length, g (5 + i) = ((D.getD i []).map g).prod) (ha : g 0 = a)
    (hb : g 1 = b) (h5 : g 5 = 1) {p : List Op} {f : Nat} (h : simOK D psi0 f p = true)
    (r : Nat) : slpJ a b p r = g (simMap psi0 f p r) :=
  sim_sound hdef p psi0 f (initJ a b) h (fun r => by
    simp only [initJ, psi0]
    split_ifs
    · exact ha.symm
    · exact hb.symm
    · exact h5.symm) r

theorem z_link {D : List (List Nat)} {g : Nat → J}
    (hdef : ∀ i < D.length, g (5 + i) = ((D.getD i []).map g).prod) (ha : g 0 = a)
    (hb : g 1 = b) (hlen : 56 < D.length)
    (h1 : D.getD 54 [] = (Native.abWord Native.x1Str).map abL)
    (h2 : D.getD 55 [] = (Native.abWord Native.x2Str).map abL)
    (h3 : D.getD 56 [] = (List.replicate 9 [59, 60]).flatten) : g 61 = ThCent.zJ := by
  have hab : ∀ s, ((Native.abWord s).map abL).map g = (Native.abWord s).map (pairLetters a b) :=
    fun s => by
      rw [List.map_map]
      refine List.map_congr_left fun l hl => ?_
      obtain ⟨ch, -, rfl⟩ := List.mem_map.1 hl
      by_cases hc : ch = 'a'
      · simp [hc, abL, pairLetters, ha]
      · simp [hc, abL, pairLetters, hb]
  have g59 : g 59 = ThCent.x1J := by
    rw [hdef 54 (by omega), h1, hab]
    rfl
  have g60 : g 60 = ThCent.x2J := by
    rw [hdef 55 (by omega), h2, hab]
    rfl
  rw [hdef 56 hlen, h3, List.map_flatten, List.map_replicate, List.prod_flatten,
    List.map_replicate, List.prod_replicate]
  simp [g59, g60, ThCent.zJ]

end CFSG.KC.ThThreeCov

end
