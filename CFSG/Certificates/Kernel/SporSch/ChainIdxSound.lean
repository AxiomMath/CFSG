module

public import CFSG.Certificates.Kernel.SporSch.ChainCKDefs
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Certificates.Data.Kernel.SporSch.J1Pt

public section

namespace CFSG.KS.SporSch.CIdx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Certificates.ChainArrays

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_iff' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem apL_nil (w m x : Nat) : apL w m [] x = x := rfl

theorem apL_cons (w m t : Nat) (T : List Nat) (x : Nat) :
    apL w m (t :: T) x = pg w m t (apL w m T x) := by
  change strictN (apL w m T x) (fun y => pg w m t y) = _
  rw [strictN_eq]

theorem apL_append (w m : Nat) (A B : List Nat) (x : Nat) :
    apL w m (A ++ B) x = apL w m A (apL w m B x) := by
  induction A with
  | nil => rfl
  | cons t A ih => rw [List.cons_append, apL_cons, apL_cons, ih]

theorem itF_zero (f : Nat → Nat) (x : Nat) : itF f 0 x = x := rfl

theorem itF_succ (f : Nat → Nat) (e x : Nat) : itF f (e + 1) x = f (itF f e x) := by
  change strictN (itF f e x) f = _
  rw [strictN_eq]

theorem elemTR_zero (n nw : Nat) (LR TR : Nat → Nat) (j : Nat) (acc : List Nat) :
    elemTR n nw LR TR 0 j acc = acc := rfl

theorem elemTR_succ (n nw : Nat) (LR TR : Nat → Nat) (d j : Nat) (acc : List Nat) :
    elemTR n nw LR TR (d + 1) j acc = elemTR n nw LR TR d (j / rcnt (LR d))
      (TR (roff n nw (LR d) + j % rcnt (LR d)) :: acc) := rfl

theorem ordK_succ (LR : Nat → Nat) (d : Nat) : ordK LR (d + 1) = rcnt (LR d) * ordK LR d := rfl

theorem fixB_iff {w m BP nb : Nat} {f : Nat → Nat} :
    fixB w m BP nb f = true ↔ ∀ t < nb, f (pg w m BP t) = pg w m BP t := by
  unfold fixB
  rw [allN_iff]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [strictB_eq, Nat.beq_eq]

theorem eqB_iff {w m BP nb : Nat} {f g : Nat → Nat} :
    eqB w m BP nb f g = true ↔ ∀ t < nb, f (pg w m BP t) = g (pg w m BP t) := by
  unfold eqB
  rw [allN_iff]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [strictB_eq, Nat.beq_eq]

section Chain

variable {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}

abbrev Wd (kO kS : Nat) (D : List (List Int)) : Array (List Int) :=
  CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D

abbrev sz (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i : Nat) : Nat :=
  (lev n S base i).pts.size

variable (hQ : ChainCK n w PS PSI LR TR TRI kS kO nb BP S base D)
include hQ

theorem hd : Hd n S base kO (Wd kO kS D) := by
  obtain ⟨hk, hH⟩ := rawHeadOK_of hQ.1 hQ.2.1
  exact hd_of_head hk hH

theorem perms : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  have h := hQ.2.1
  unfold headK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact h.2.2.2.2.1

theorem base_size : base.size = nb := hQ.1.2.2.2.2.2.1

theorem n_lt : n < 65536 := hQ.1.2.2.1

theorem base_lt : ∀ t < nb, base[t]! < n := fun t ht =>
  (hd hQ).base_lt t (by rw [base_size hQ]; exact ht)

theorem base_eq : ∀ t < nb, base[t]! = pg w (mask w) BP t := hQ.1.2.2.2.2.2.2

theorem card_le : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod := hQ.2.2.2

theorem agree {i : Nat} (hi : i < nb) :
    Agree n w (LR i) (lev n S base i)
        (fun k => permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k)))) ∧
      ∀ k < rcnt (LR i), PRep n w (TR (roff n (n * w) (LR i) + k))
          (permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k)))) ∧
        PRep n w (TRI (roff n (n * w) (LR i) + k))
          (permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k))))⁻¹ :=
  agree_levelK hQ.1 (perms hQ) (base_lt hQ) hi (hQ.2.2.1 i hi)

theorem rcnt_eq {i : Nat} (hi : i < nb) : rcnt (LR i) = sz n S base i := (agree hQ hi).1.cnt

theorem sz_pos {i : Nat} (hi : i < nb) : 0 < sz n S base i :=
  (lev_facts (hd hQ) (by rw [base_size hQ]; exact hi)).pos

omit hQ in
theorem rep_unique' {t : Array Nat} {g h : Equiv.Perm (Fin n)} (hg : Rep n t g) (hh : Rep n t h) :
    g = h := Equiv.ext fun x => Fin.ext (by rw [← hg x, ← hh x])

theorem pg_TR {i k : Nat} (hi : i < nb) (hk : k < sz n S base i) (x : Fin n) :
    pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x = trP n S base i k x := by
  obtain ⟨A, hP⟩ := agree hQ hi
  have e : permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k))) = trP n S base i k :=
    rep_unique' (A.tr k hk).1 (rep_tr (hd hQ) (by rw [base_size hQ]; exact hi) hk)
  rw [(hP k (by rw [rcnt_eq hQ hi]; exact hk)).1 x, e]

omit hQ in
@[expose] noncomputable def elemGR (n : Nat) (S : Array (Array Nat)) (base : Array Nat) :
    Nat → Nat → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | 0, _, acc => acc
  | d + 1, j, acc => elemGR n S base d (j / sz n S base d)
      (trP n S base d (j % sz n S base d) * acc)

omit hQ in
@[expose] noncomputable def el (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (nb j : Nat) :
    Equiv.Perm (Fin n) :=
  elemGR n S base nb j 1

theorem apL_elemTR : ∀ d ≤ nb, ∀ (j : Nat) (acc : List Nat) (f : Equiv.Perm (Fin n)),
    (∀ y : Fin n, apL w (mask w) acc y = f y) →
    ∀ y : Fin n, apL w (mask w) (elemTR n (n * w) LR TR d j acc) y = elemGR n S base d j f y := by
  intro d
  induction d with
  | zero => intro _ j acc f hf y; exact hf y
  | succ d ih =>
    intro hd j acc f hf y
    have hdn : d < nb := by omega
    rw [elemTR_succ, rcnt_eq hQ hdn]
    refine ih (by omega) _ _ _ (fun z => ?_) y
    rw [apL_cons, hf z, pg_TR hQ hdn (Nat.mod_lt _ (sz_pos hQ hdn)), Equiv.Perm.mul_apply]

theorem apL_elemT (j : Nat) (y : Fin n) :
    apL w (mask w) (elemT n (n * w) LR TR nb j) y = el n S base nb j y :=
  apL_elemTR hQ nb le_rfl j [] 1 (fun _ => rfl) y

omit hQ in
@[expose] def ordG (n : Nat) (S : Array (Array Nat)) (base : Array Nat) : Nat → Nat
  | 0 => 1
  | d + 1 => sz n S base d * ordG n S base d

theorem ordK_eq : ∀ d ≤ nb, ordK LR d = ordG n S base d
  | 0, _ => rfl
  | d + 1, hd => by rw [ordK_succ, ordG, rcnt_eq hQ (by omega), ordK_eq d (by omega)]

theorem tr_fix {i k : Nat} (hi : i < nb) (hk : k < sz n S base i) :
    trP n S base i k ∈ Fix n S kO base i :=
  (tr_spec (hd hQ) (by rw [base_size hQ]; exact hi) k hk).1

theorem tr_base {i k : Nat} (hi : i < nb) (hk : k < sz n S base i) :
    (trP n S base i k ⟨base[i]!, base_lt hQ i hi⟩ : Nat) = (lev n S base i).pts[k]! :=
  (tr_spec (hd hQ) (by rw [base_size hQ]; exact hi) k hk).2

theorem tr_cancel {i k k' : Nat} (hi : i < nb) (hk : k < sz n S base i)
    (hk' : k' < sz n S base i) {f f' : Equiv.Perm (Fin n)} (hf : f ∈ Fix n S kO base (i + 1))
    (hf' : f' ∈ Fix n S kO base (i + 1)) (e : trP n S base i k * f = trP n S base i k' * f') :
    k = k' ∧ f = f' := by
  have hb := base_lt hQ i hi
  have F := lev_facts (hd hQ) (by rw [base_size hQ]; exact hi)
  have e1 := congrArg (fun g : Equiv.Perm (Fin n) => (g ⟨base[i]!, hb⟩ : Nat)) e
  simp only [Equiv.Perm.mul_apply, hf.2 i (by omega) hb, hf'.2 i (by omega) hb] at e1
  rw [tr_base hQ hi hk, tr_base hQ hi hk'] at e1
  have hkk : k = k' := by rw [← F.pos_pts k hk, ← F.pos_pts k' hk', e1]
  subst hkk
  exact ⟨rfl, mul_left_cancel e⟩

theorem elemGR_spec : ∀ d ≤ nb, ∀ j < ordG n S base d, ∀ f ∈ Fix n S kO base d,
    elemGR n S base d j f ∈ Fix n S kO base 0 ∧
      ∀ j' < ordG n S base d, ∀ f' ∈ Fix n S kO base d,
        elemGR n S base d j f = elemGR n S base d j' f' → j = j' ∧ f = f' := by
  intro d
  induction d with
  | zero =>
    intro _ j hj f hf
    refine ⟨hf, fun j' hj' f' _ e => ⟨by simp [ordG] at hj hj'; omega, e⟩⟩
  | succ d ih =>
    intro hdn j hj f hf
    have hd' : d < nb := by omega
    have hc := sz_pos hQ hd'
    set c := sz n S base d
    have hjc : j / c < ordG n S base d := by
      rw [Nat.div_lt_iff_lt_mul hc, Nat.mul_comm]
      exact hj
    have hkc : j % c < c := Nat.mod_lt _ hc
    have hmem : trP n S base d (j % c) * f ∈ Fix n S kO base d :=
      Subgroup.mul_mem _ (tr_fix hQ hd' hkc) (Fix_succ_le hf)
    obtain ⟨h1, h2⟩ := ih (by omega) _ hjc _ hmem
    refine ⟨h1, fun j' hj' f' hf' e => ?_⟩
    have hjc' : j' / c < ordG n S base d := by
      rw [Nat.div_lt_iff_lt_mul hc, Nat.mul_comm]
      exact hj'
    have hmem' : trP n S base d (j' % c) * f' ∈ Fix n S kO base d :=
      Subgroup.mul_mem _ (tr_fix hQ hd' (Nat.mod_lt _ hc)) (Fix_succ_le hf')
    obtain ⟨e1, e2⟩ := h2 _ hjc' _ hmem' e
    obtain ⟨e3, e4⟩ := tr_cancel hQ hd' hkc (Nat.mod_lt _ hc) hf hf' e2
    refine ⟨?_, e4⟩
    rw [← Nat.div_add_mod j c, ← Nat.div_add_mod j' c, e1, e3]

omit hQ in
theorem fix_zero : Fix n S kO base 0 = Gen n S kO := Fix_zero

omit hQ in
theorem one_fix : (1 : Equiv.Perm (Fin n)) ∈ Fix n S kO base nb := Subgroup.one_mem _

theorem el_mem {j : Nat} (hj : j < ordK LR nb) : el n S base nb j ∈ Gen n S kO := by
  rw [← fix_zero]
  exact (elemGR_spec hQ nb le_rfl j (by rwa [← ordK_eq hQ nb le_rfl]) 1 one_fix).1

theorem el_inj {j j' : Nat} (hj : j < ordK LR nb) (hj' : j' < ordK LR nb)
    (e : el n S base nb j = el n S base nb j') : j = j' := by
  rw [ordK_eq hQ nb le_rfl] at hj hj'
  exact ((elemGR_spec hQ nb le_rfl j hj 1 one_fix).2 j' hj' 1 one_fix e).1

theorem eq_of_base {g h : Equiv.Perm (Fin n)} (hg : g ∈ Gen n S kO) (hh : h ∈ Gen n S kO)
    (e : ∀ t (ht : t < nb), (g ⟨base[t]!, base_lt hQ t ht⟩ : Nat) = h ⟨base[t]!, base_lt hQ t ht⟩) :
    g = h := by
  have hm : h⁻¹ * g ∈ Fix n S kO base base.size := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg, fun t ht hb => ?_⟩
    rw [base_size hQ] at ht
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (e t ht)
  have := fix_one (hd hQ) (card_le hQ) hm
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem pbase_lt {t : Nat} (ht : t < nb) : pg w (mask w) BP t < n := by
  rw [← base_eq hQ t ht]
  exact base_lt hQ t ht

theorem eq_of_pbase {g h : Equiv.Perm (Fin n)} (hg : g ∈ Gen n S kO) (hh : h ∈ Gen n S kO)
    (e : ∀ t < nb, ∀ hb : pg w (mask w) BP t < n,
      (g ⟨pg w (mask w) BP t, hb⟩ : Nat) = h ⟨pg w (mask w) BP t, hb⟩) : g = h := by
  refine eq_of_base hQ hg hh fun t ht => ?_
  have key : ∀ (a b : Nat) (_ : a = b) (pa : a < n) (pb : b < n),
      (g ⟨b, pb⟩ : Nat) = h ⟨b, pb⟩ → (g ⟨a, pa⟩ : Nat) = h ⟨a, pa⟩ := by
    rintro a b rfl pa pb e'
    exact e'
  exact key _ _ (base_eq hQ t ht) _ _ (e t ht (pbase_lt hQ ht))

abbrev Acts (n : Nat) (f : Nat → Nat) (g : Equiv.Perm (Fin n)) : Prop := ∀ y : Fin n, f y = g y

theorem fixB_iff_eq_one {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : Acts n f g)
    (hg : g ∈ Gen n S kO) : fixB w (mask w) BP nb f = true ↔ g = 1 := by
  rw [fixB_iff]
  constructor
  · intro h
    refine eq_of_pbase hQ hg (Subgroup.one_mem _) fun t ht hb => ?_
    rw [← hf ⟨_, hb⟩]
    exact h t ht
  · rintro rfl t ht
    exact hf ⟨_, pbase_lt hQ ht⟩

theorem eqB_iff_eq {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin n)} (hf : Acts n f g)
    (hf' : Acts n f' g') (hg : g ∈ Gen n S kO) (hg' : g' ∈ Gen n S kO) :
    eqB w (mask w) BP nb f f' = true ↔ g = g' := by
  rw [eqB_iff]
  constructor
  · intro h
    refine eq_of_pbase hQ hg hg' fun t ht hb => ?_
    rw [← hf ⟨_, hb⟩, ← hf' ⟨_, hb⟩]
    exact h t ht
  · rintro rfl t ht
    rw [hf ⟨_, pbase_lt hQ ht⟩, hf' ⟨_, pbase_lt hQ ht⟩]

omit hQ in
theorem acts_itF {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : Acts n f g) :
    ∀ e, Acts n (itF f e) (g ^ e)
  | 0, y => by rw [itF_zero, pow_zero]; rfl
  | e + 1, y => by
    rw [itF_succ, pow_succ', Equiv.Perm.mul_apply, acts_itF hf e y]
    exact hf ((g ^ e) y)

theorem ordF_iff {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : Acts n f g)
    (hg : g ∈ Gen n S kO) {e : Nat} : ordF w (mask w) BP nb f e = true ↔ orderOf g = e := by
  have hfix : ∀ d, fixB w (mask w) BP nb (itF f d) = true ↔ g ^ d = 1 := fun d =>
    fixB_iff_eq_one hQ (acts_itF hf d) (Subgroup.pow_mem _ hg d)
  unfold ordF
  rw [bAnd_iff', bAnd_iff', Nat.blt_eq, hfix, allN_iff]
  have hd : ∀ d, (bIf(Nat.beq d (nat_lit 0), true, bIf(Nat.beq (Nat.mod e d) (nat_lit 0),
      bIf(fixB w (mask w) BP nb (itF f d), false, true), true)) = true) ↔
      (d ≠ 0 → e % d = 0 → g ^ d ≠ 1) := by
    intro d
    by_cases h0 : d = 0
    · subst h0
      simp
    · have : Nat.beq d 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [this]
      by_cases h1 : e % d = 0
      · have : Nat.beq (e % d) 0 = true := by rw [Nat.beq_eq]; exact h1
        change Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true
          (Bool.rec (motive := fun _ => Bool) true false (fixB w (mask w) BP nb (itF f d)))
            (Nat.beq (e % d) 0)) true false = true ↔ _
        rw [this]
        cases hb : fixB w (mask w) BP nb (itF f d)
        · have := (hfix d).not.1 (by rw [hb]; simp)
          simp [h0, h1, this]
        · have := (hfix d).1 hb
          simp [h0, h1, this]
      · have : Nat.beq (e % d) 0 = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
        change Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true
          (Bool.rec (motive := fun _ => Bool) true false (fixB w (mask w) BP nb (itF f d)))
            (Nat.beq (e % d) 0)) true false = true ↔ _
        rw [this]
        simp [h1]
  simp only [hd]
  constructor
  · rintro ⟨he, hp, hdiv⟩
    have hdvd := orderOf_dvd_of_pow_eq_one hp
    have hpos := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨e, he, hp⟩)
    by_contra hne
    have hlt : orderOf g < e := lt_of_le_of_ne (Nat.le_of_dvd he hdvd) hne
    exact hdiv _ hlt (by omega) (Nat.mod_eq_zero_of_dvd hdvd) (pow_orderOf_eq_one g)
  · rintro rfl
    have hpos : 0 < orderOf g := orderOf_pos g
    exact ⟨hpos, pow_orderOf_eq_one g, fun d hd h0 _ =>
      pow_ne_one_of_lt_orderOf h0 hd⟩

omit hQ in
@[expose] noncomputable def trLists (n : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (i d : Nat) : List (List (Equiv.Perm (Fin n))) :=
  (List.range d).map fun l => (List.range (sz n S base (i + l))).map (trP n S base (i + l))

omit hQ in
theorem trLists_succ (i d : Nat) : trLists n S base i (d + 1) =
    (List.range (sz n S base i)).map (trP n S base i) :: trLists n S base (i + 1) d := by
  unfold trLists
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 2
  funext l
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 l]

theorem products_spec : ∀ d i, i + d = nb →
    (∀ g, g ∈ products (trLists n S base i d) ↔ g ∈ Fix n S kO base i) ∧
      (products (trLists n S base i d)).Nodup := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hib : i = base.size := by rw [base_size hQ]; omega
    simp only [trLists, List.range_zero, List.map_nil, products, List.mem_singleton,
      List.nodup_singleton, and_true]
    intro g
    constructor
    · rintro rfl
      exact Subgroup.one_mem _
    · intro hg
      rw [hib] at hg
      exact fix_one (hd hQ) (card_le hQ) hg
  | succ d ih =>
    intro i hi
    have hin : i < nb := by omega
    obtain ⟨hm, hnd⟩ := ih (i + 1) (by omega)
    rw [trLists_succ, products]
    refine ⟨fun g => ?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range, hm]
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, f, hf, rfl⟩
        exact Subgroup.mul_mem _ (tr_fix hQ hin hk) (Fix_succ_le hf)
      · intro hg
        obtain ⟨k, hk, hgk⟩ := fix_surj (hd hQ) (card_le hQ) (by rw [base_size hQ]; exact hin) hg
        have hb := base_lt hQ i hin
        refine ⟨trP n S base i k, ⟨k, hk, rfl⟩, (trP n S base i k)⁻¹ * g, ⟨Subgroup.mul_mem _
          (Subgroup.inv_mem _ (tr_fix hQ hin hk).1) hg.1, fun t ht hbt => ?_⟩, by group⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · rw [Equiv.Perm.mul_apply, hg.2 t ht hbt, Equiv.Perm.inv_eq_iff_eq,
            (tr_fix hQ hin hk).2 t ht hbt]
        · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
          apply Fin.ext
          rw [tr_base hQ hin hk, ← hgk]
    · rw [List.nodup_flatMap]
      refine ⟨fun t _ => hnd.map (mul_right_injective t), ?_⟩
      rw [List.pairwise_map]
      refine List.nodup_range.pairwise_of_forall_ne fun k hk k' hk' hne => ?_
      rw [List.mem_range] at hk hk'
      unfold Function.onFun
      rw [List.disjoint_left]
      rintro _ h1 h2
      simp only [List.mem_map] at h1 h2
      obtain ⟨f, hf, rfl⟩ := h1
      obtain ⟨f', hf', e⟩ := h2
      exact hne (tr_cancel hQ hin hk' hk ((hm f').1 hf') ((hm f).1 hf) e).1.symm

end Chain

end CFSG.KS.SporSch.CIdx

end
