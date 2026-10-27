module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.ComponentClassification.WittDesign CFSG.EvenSmallLie.UnitarySix.MathieuExt
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def theta (m : ℕ) : toddModule := Submodule.Quotient.mk (vecOfMask m)

theorem theta_xor (m m' : ℕ) : theta (m ^^^ m') = theta m + theta m' := by
  rw [theta, vecOfMask_xor, Submodule.Quotient.mk_add]
  rfl

theorem vecOfMask_two_pow (j : Fin 22) : vecOfMask (2 ^ (j : ℕ)) = basisW j := by
  ext i
  rw [vecOfMask_apply, bvec, basisW_apply, Nat.testBit_two_pow]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm (Fin.val_ne_of_ne h)]

theorem theta_two_pow (j : Fin 22) : theta (2 ^ (j : ℕ)) = toddPoint j := by
  rw [theta, vecOfMask_two_pow]
  rfl

theorem ptvArr_low : ∀ j : Fin 22, (j : ℕ) < 10 → ptvArr.getD j 0 = 2 ^ (j : ℕ) := by
  decide

theorem ptvArr_high : ∀ l : Fin 12, ptvArr.getD (l + 10) 0 = toddBM l ^^^ 2 ^ ((l : ℕ) + 10) := by
  decide

theorem ptvArr_lt (k : ℕ) : ptvArr.getD k 0 < 1024 := by
  have h : ∀ j : Fin 22, ptvArr.getD j 0 < 1024 := by decide
  by_cases hk : k < 22
  · exact h ⟨k, hk⟩
  · have hs : ¬ k < ptvArr.size := by simpa [ptvArr] using hk
    simp [Array.getD, hs]

theorem theta_ptvArr (j : Fin 22) : theta (ptvArr.getD j 0) = toddPoint j := by
  by_cases hj : (j : ℕ) < 10
  · rw [ptvArr_low j hj, theta_two_pow]
  · obtain ⟨l, hl⟩ : ∃ l : Fin 12, (l : ℕ) + 10 = j := ⟨⟨j - 10, by omega⟩, by simp; omega⟩
    have hj' : j = ⟨(l : ℕ) + 10, by omega⟩ := Fin.ext hl.symm
    have h0 : theta (toddBM l) = 0 := by
      rw [theta, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨l, rfl⟩
    have h := ptvArr_high l
    rw [show ((l : ℕ) + 10 : ℕ) = ((⟨(l : ℕ) + 10, by omega⟩ : Fin 22) : ℕ) from rfl] at h
    rw [hj', h, theta_xor, h0, zero_add, theta_two_pow]

theorem vecOfMask_eq_sum (m : ℕ) :
    vecOfMask m = ∑ i : Fin 22, if m.testBit i then basisW i else 0 := by
  ext j
  rw [vecOfMask_apply, W22.sum_apply, Finset.sum_eq_single j]
  · by_cases h : m.testBit j <;> simp [h, bvec, basisW_apply, W22.zero_apply]
  · intro i _ hij
    by_cases h : m.testBit i <;> simp [h, basisW_apply, Ne.symm hij, W22.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem theta_eq_sum (m : ℕ) :
    theta m = ∑ i : Fin 22, if m.testBit i then toddPoint i else 0 := by
  rw [theta, vecOfMask_eq_sum, ← Submodule.mkQ_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [toddPoint]

theorem rep_ap {t : Table} {g : Equiv.Perm (Fin 22)} (h : Rep 22 t g) (i : Fin 22) :
    ap t i = (g i : ℕ) := by
  rw [h i i.2, idx_of_lt g i.2]
  rfl

theorem rep_unique {t : Table} {g g' : Equiv.Perm (Fin 22)} (h : Rep 22 t g)
    (h' : Rep 22 t g') : g = g' :=
  Equiv.ext fun i => Fin.ext ((rep_ap h i).symm.trans (rep_ap h' i))

theorem rep_tableF (g : Equiv.Perm (Fin 22)) : Rep 22 (tableF ⇑g) g :=
  CFSG.Sporadic.Schreier.rep_toTable (by norm_num) g

theorem keyT_congr {t t' : Table} {g : Equiv.Perm (Fin 22)} (h : Rep 22 t g)
    (h' : Rep 22 t' g) : keyT t = keyT t' := by
  unfold keyT
  refine List.foldl_ext _ _ _ fun acc i hi => ?_
  rw [List.mem_range] at hi
  rw [h i hi, h' i hi]

theorem compT_eq {P Q P' Q' : Table}
    (h : ∀ i < 22, ap (compT 22 P Q) i = ap (compT 22 P' Q') i) :
    compT 22 P Q = compT 22 P' Q' := by
  unfold compT
  refine Array.ext (by simp) fun i hi _ => ?_
  have hi' : i < 22 := by simpa using hi
  have := h i hi'
  unfold compT at this
  rw [ap_ofFn _ hi', ap_ofFn _ hi'] at this
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  exact UInt32.toNat_inj.1 this

theorem compT_comm {y t : Table} {g h : Equiv.Perm (Fin 22)} (hy : Rep 22 y g)
    (ht : Rep 22 t h) (hc : g * h = h * g) : compT 22 y t = compT 22 t y :=
  compT_eq fun i hi => by rw [(hy.compT ht) i hi, (ht.compT hy) i hi, hc]

theorem theta_foldl {t : Table} {g : Equiv.Perm (Fin 22)} (ht : Rep 22 t g) (m : ℕ)
    (L : List (Fin 22)) (acc : ℕ) :
    theta (L.foldl
      (fun acc (i : Fin 22) => if m.testBit i then acc ^^^ ptvArr.getD (ap t i) 0 else acc)
      acc) = theta acc + (L.map fun (i : Fin 22) => if m.testBit i then toddPoint (g i) else 0).sum
      := by
  induction L generalizing acc with
  | nil => simp
  | cons i L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    split_ifs
    · rw [theta_xor, rep_ap ht, theta_ptvArr]
    · rw [add_zero]

theorem toddAct_theta_eq_sum
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (m : ℕ) :
    toddAct hg (theta m) = ∑ i : Fin 22, if m.testBit i then toddPoint (g i) else 0 := by
  rw [theta_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · exact toddAct_point hg i
  · exact map_zero _

theorem theta_actM
    {t : Table} {g : Equiv.Perm (Fin 22)} (ht : Rep 22 t g)
    (hg : g ∈ hexadAut) (m : ℕ) : theta (actM t m) = toddAct hg (theta m) := by
  rw [actM, theta_foldl ht, toddAct_theta_eq_sum, Fin.sum_univ_def]
  simp [theta, vecOfMask_zero]

theorem actM_lt (t : Table) (m : ℕ) : actM t m < 1024 := by
  have key : ∀ (L : List (Fin 22)) (acc : ℕ), acc < 2 ^ 10 →
      L.foldl (fun acc (i : Fin 22) => if m.testBit i then acc ^^^ ptvArr.getD (ap t i) 0
        else acc) acc < 2 ^ 10 := by
    intro L
    induction L with
    | nil => exact fun acc h => h
    | cons i L ih =>
      intro acc hacc
      rw [List.foldl_cons]
      refine ih _ ?_
      split_ifs
      · exact Nat.xor_lt_two_pow hacc (ptvArr_lt _)
      · exact hacc
  exact key _ 0 (by norm_num)

theorem theta_injOn {m m' : ℕ} (hm : m < 1024) (hm' : m' < 1024) (h : theta m = theta m') :
    m = m' := by
  have hx : m ^^^ m' < 2 ^ 10 := Nat.xor_lt_two_pow (by simpa using hm) (by simpa using hm')
  have hK : vecOfMask (m ^^^ m') ∈ toddKernel := by
    rw [theta, theta, Submodule.Quotient.eq] at h
    rw [vecOfMask_xor]
    have e : vecOfMask m - vecOfMask m' = vecOfMask m + vecOfMask m' := by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (two_smul_eq_zero (vecOfMask m'))]
    rwa [e] at h
  have h0 : vecOfMask (m ^^^ m') = 0 := by
    rw [mem_toddKernel_iff.1 hK]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hb : (m ^^^ m').testBit ((toddPivot l : Fin 22) : ℕ) = false :=
      Nat.testBit_eq_false_of_lt (hx.trans_le
        (Nat.pow_le_pow_right (by norm_num) (by simp [toddPivot])))
    rw [vecOfMask_apply, bvec, hb]
    simp
  have hbits : ∀ i, (m ^^^ m').testBit i = false := by
    intro i
    by_cases hi : i < 22
    · have := congrFun h0 ⟨i, hi⟩
      change (if (m ^^^ m').testBit i = true then (1 : ZMod 2) else 0) = 0 at this
      cases hb : (m ^^^ m').testBit i
      · rfl
      · rw [hb] at this
        exact absurd this (by decide)
    · exact Nat.testBit_eq_false_of_lt (hx.trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine Nat.eq_of_testBit_eq fun i => ?_
  have h := hbits i
  rw [Nat.testBit_xor] at h
  revert h
  cases m.testBit i <;> cases m'.testBit i <;> decide

theorem theta_surj (v : toddModule) : ∃ m < 1024, theta m = v := by
  have hinj : Function.Injective fun m : Fin 1024 => theta m :=
    fun a b h => Fin.ext (theta_injOn a.2 b.2 h)
  have hfin : Finite toddModule :=
    Nat.finite_of_card_ne_zero (by rw [card_toddModule]; norm_num)
  have hcard : Nat.card (Set.range fun m : Fin 1024 => theta m) = Nat.card toddModule := by
    rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin,
      card_toddModule]
    norm_num
  have huniv : (Set.range fun m : Fin 1024 => theta m) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hcard]) (Set.toFinite _)
  obtain ⟨m, hm⟩ : v ∈ Set.range fun m : Fin 1024 => theta m := huniv ▸ Set.mem_univ v
  exact ⟨m, m.2, hm⟩

@[expose] def repSet (L : List Table) : Set (Equiv.Perm (Fin 22)) := {g | ∃ t ∈ L, Rep 22 t g}

abbrev fixV
    (X : Subgroup (Equiv.Perm (Fin 22))) (hX : X ≤ hexadAut) : Type :=
  {v : toddModule // ∀ x (hx : x ∈ X), toddAct (hX hx) v = v}

theorem commute_of_sq {X : Subgroup (Equiv.Perm (Fin 22))} (hsq : ∀ x ∈ X, x * x = 1)
    {x y : Equiv.Perm (Fin 22)} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x := by
  have h := inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hx hy))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq x hx),
    inv_eq_of_mul_eq_one_right (hsq y hy)] at h
  exact h.symm

structure NodeInv
    (X : Subgroup (Equiv.Perm (Fin 22))) (hX : X ≤ hexadAut) (span : List Table)
    (fix : List ℕ) (rest : List Table) : Prop where
  span_le : ∀ t ∈ span, ∃ g ∈ X, Rep 22 t g
  one_mem : (1 : Equiv.Perm (Fin 22)) ∈ repSet span
  mul_mem : ∀ g ∈ repSet span, ∀ h ∈ repSet span, g * h ∈ repSet span
  fix_mem : ∀ m < 1024, (∀ g (hg : g ∈ X), toddAct (hX hg) (theta m) = theta m) → m ∈ fix
  cover : ∀ z ∈ X, z ∈ repSet span ∨ ∃ t ∈ rest, Rep 22 t z
  sorted : rest.Pairwise fun a b => keyT a < keyT b

theorem card_le_length {X : Subgroup (Equiv.Perm (Fin 22))} {span : List Table}
    (h : ∀ z ∈ X, z ∈ repSet span) : Nat.card X ≤ span.length := by
  have hc : ∀ z : X, ∃ i : Fin span.length, Rep 22 span[i] z := fun z => by
    obtain ⟨t, ht, hr⟩ := h z z.2
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ⟨⟨i, hi⟩, hr⟩
  choose f hf using hc
  have hinj : Function.Injective f := fun a b hab => by
    have hb := hf b
    rw [← hab] at hb
    exact Subtype.ext (rep_unique (hf a) hb)
  simpa using Nat.card_le_card_of_injective f hinj

theorem card_fixV_le
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut) {fix : List ℕ}
    (h : ∀ m < 1024, (∀ g (hg : g ∈ X), toddAct (hX hg) (theta m) = theta m) → m ∈ fix) :
    Nat.card (fixV X hX) ≤ fix.length := by
  have hc : ∀ v : fixV X hX, ∃ i : Fin fix.length, theta fix[i] = v.1 := fun v => by
    obtain ⟨m, hm, hmv⟩ := theta_surj v.1
    have hmem := h m hm fun g hg => by rw [hmv]; exact v.2 g hg
    obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hmem
    exact ⟨⟨i, hi⟩, by rw [← hmv, ← hfi]; rfl⟩
  choose f hf using hc
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (by rw [← hf a, ← hf b, hab])
  simpa using Nat.card_le_card_of_injective f hinj

theorem exists_first {α : Type*} (p : α → Prop) :
    ∀ l : List α, (∃ a ∈ l, p a) →
      ∃ pre a post, l = pre ++ a :: post ∧ p a ∧ ∀ b ∈ pre, ¬ p b
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : p a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · obtain ⟨b, hb, hpb⟩ := h
      have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with rfl | hb
        · exact absurd hpb ha
        · exact hb
      obtain ⟨pre, c, post, rfl, hc, hpre⟩ := exists_first p l ⟨b, hb', hpb⟩
      refine ⟨a :: pre, c, post, rfl, hc, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact ha
      · exact hpre d hd

theorem repSet_le {X : Subgroup (Equiv.Perm (Fin 22))} {span : List Table}
    (h : ∀ t ∈ span, ∃ g ∈ X, Rep 22 t g) {g : Equiv.Perm (Fin 22)} (hg : g ∈ repSet span) :
    g ∈ X := by
  obtain ⟨t, ht, hr⟩ := hg
  obtain ⟨g', hg', hr'⟩ := h t ht
  rwa [rep_unique hr hr']

theorem mem_repSet_extend {span : List Table} {y : Table} {gy : Equiv.Perm (Fin 22)}
    (hy : Rep 22 y gy) (hspan : ∀ t ∈ span, ∃ g : Equiv.Perm (Fin 22), Rep 22 t g)
    {g : Equiv.Perm (Fin 22)} :
    g ∈ repSet (span ++ span.map (compT 22 y)) ↔
      g ∈ repSet span ∨ ∃ h ∈ repSet span, g = gy * h := by
  constructor
  · rintro ⟨t, ht, hr⟩
    rcases List.mem_append.1 ht with ht | ht
    · exact Or.inl ⟨t, ht, hr⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      obtain ⟨h, hh⟩ := hspan s hs
      exact Or.inr ⟨h, ⟨s, hs, hh⟩, rep_unique hr (hy.compT hh)⟩
  · rintro (⟨t, ht, hr⟩ | ⟨h, ⟨s, hs, hh⟩, rfl⟩)
    · exact ⟨t, List.mem_append_left _ ht, hr⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hs), hy.compT hh⟩

section Step

variable {X : Subgroup (Equiv.Perm (Fin 22))} {hX : X ≤ hexadAut} {span : List Table}
  {fix : List ℕ} {pre ys : List Table} {y : Table} {gy : Equiv.Perm (Fin 22)}

theorem mem_tail_of_first
    (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep 22 t g ∧ g ∉ repSet span) {g : Equiv.Perm (Fin 22)}
    (hgX : g ∈ X) (hg : g ∉ repSet span) {t : Table} (ht : t ∈ pre ++ y :: ys)
    (hr : Rep 22 t g) : t ∈ y :: ys := by
  rcases List.mem_append.1 ht with ht | ht
  · exact absurd ⟨g, hgX, hr, hg⟩ (hpre t ht)
  · exact ht

theorem newGen_of_first
    (hI : NodeInv X hX span fix (pre ++ y :: ys)) (hgyX : gy ∈ X)
    (hy : Rep 22 y gy) (hgy : gy ∉ repSet span)
    (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep 22 t g ∧ g ∉ repSet span) (hsq : ∀ x ∈ X, x * x = 1) :
    newGen span y = true := by
  rw [newGen, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨?_, fun s hs => ?_⟩
  · by_contra hc
    rw [Bool.not_eq_false, List.contains_iff_mem] at hc
    exact hgy ⟨y, hc, hy⟩
  · obtain ⟨gs, hgsX, hgs⟩ := hI.span_le s hs
    have hprod : gy * gs ∉ repSet span := fun hm => hgy (by
      have := hI.mul_mem _ hm gs ⟨s, hs, hgs⟩
      rwa [mul_assoc, hsq gs hgsX, mul_one] at this)
    obtain ⟨t, ht, hrt⟩ := (hI.cover _ (mul_mem hgyX hgsX)).resolve_left hprod
    have hkey : keyT t = keyT (compT 22 y s) := keyT_congr hrt (hy.compT hgs)
    rw [decide_eq_true_eq, ← hkey]
    rcases List.mem_cons.1 (mem_tail_of_first hpre (mul_mem hgyX hgsX) hprod ht hrt) with
      rfl | ht'
    · exact le_rfl
    · exact (List.pairwise_cons.1 (List.pairwise_append.1 hI.sorted).2.1).1 t ht' |>.le

theorem nodeInv_step
    (hI : NodeInv X hX span fix (pre ++ y :: ys)) (hgyX : gy ∈ X)
    (hy : Rep 22 y gy) (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep 22 t g ∧ g ∉ repSet span)
    (hsq : ∀ x ∈ X, x * x = 1) :
    NodeInv X hX (span ++ span.map (compT 22 y)) (fix.filter fun m => actM y m == m)
      (ys.filter fun z => compT 22 y z == compT 22 z y) := by
  have hspan : ∀ t ∈ span, ∃ g : Equiv.Perm (Fin 22), Rep 22 t g := fun t ht => by
    obtain ⟨g, -, hg⟩ := hI.span_le t ht
    exact ⟨g, hg⟩
  have hle : ∀ {g}, g ∈ repSet span → g ∈ X := fun hg => repSet_le hI.span_le hg
  have hcomm : ∀ {g h}, g ∈ X → h ∈ X → g * h = h * g := fun hg hh => commute_of_sq hsq hg hh
  refine ⟨fun t ht => ?_, ?_, fun g hg h hh => ?_, fun m hm hfix => ?_, fun z hz => ?_, ?_⟩
  · rcases List.mem_append.1 ht with ht | ht
    · exact hI.span_le t ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      obtain ⟨gs, hgsX, hgs⟩ := hI.span_le s hs
      exact ⟨gy * gs, mul_mem hgyX hgsX, hy.compT hgs⟩
  · exact (mem_repSet_extend hy hspan).2 (Or.inl hI.one_mem)
  · rw [mem_repSet_extend hy hspan] at hg hh ⊢
    rcases hg with hg | ⟨g', hg', rfl⟩ <;> rcases hh with hh | ⟨h', hh', rfl⟩
    · exact Or.inl (hI.mul_mem _ hg _ hh)
    · refine Or.inr ⟨g * h', hI.mul_mem _ hg _ hh', ?_⟩
      rw [← mul_assoc, ← mul_assoc, hcomm (hle hg) hgyX]
    · exact Or.inr ⟨g' * h, hI.mul_mem _ hg' _ hh, by rw [mul_assoc]⟩
    · refine Or.inl ?_
      have e : gy * g' * (gy * h') = g' * h' :=
        calc gy * g' * (gy * h') = gy * (g' * gy) * h' := by simp only [mul_assoc]
          _ = gy * (gy * g') * h' := by rw [hcomm (hle hg') hgyX]
          _ = g' * h' := by rw [← mul_assoc gy gy g', hsq gy hgyX, one_mul]
      rw [e]
      exact hI.mul_mem _ hg' _ hh'
  · refine List.mem_filter.2 ⟨hI.fix_mem m hm hfix, ?_⟩
    have h1 := theta_actM hy (hX hgyX) m
    rw [hfix gy hgyX] at h1
    rw [theta_injOn (actM_lt y m) hm h1, beq_self_eq_true]
  · by_cases hzs : z ∈ repSet span
    · exact Or.inl ((mem_repSet_extend hy hspan).2 (Or.inl hzs))
    · obtain ⟨t, ht, hrt⟩ := (hI.cover z hz).resolve_left hzs
      rcases List.mem_cons.1 (mem_tail_of_first hpre hz hzs ht hrt) with rfl | ht'
      · rw [rep_unique hrt hy]
        exact Or.inl ((mem_repSet_extend hy hspan).2 (Or.inr ⟨1, hI.one_mem, (mul_one _).symm⟩))
      · refine Or.inr ⟨t, List.mem_filter.2 ⟨ht', ?_⟩, hrt⟩
        rw [compT_comm hy hrt (hcomm hgyX hz), beq_self_eq_true]
  · exact (List.pairwise_cons.1 (List.pairwise_append.1 hI.sorted).2.1).2.filter _

end Step

theorem node_sound
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    (hsq : ∀ x ∈ X, x * x = 1) {B : ℕ} :
    ∀ (fuel : ℕ) (span : List Table) (fix : List ℕ) (rest : List Table),
      node B fuel span fix rest = true → NodeInv X hX span fix rest →
        Nat.card X * Nat.card (fixV X hX) ≤ B
  | 0, _, _, _, h, _ => by simp [node] at h
  | fuel + 1, span, fix, rest, h, hI => by
    rw [node, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hB, hall⟩ := h
    by_cases hcov : ∀ z ∈ X, z ∈ repSet span
    · exact (Nat.mul_le_mul (card_le_length hcov) (card_fixV_le hX hI.fix_mem)).trans hB
    · push Not at hcov
      obtain ⟨z, hzX, hz⟩ := hcov
      obtain ⟨t, ht, hzt⟩ := (hI.cover z hzX).resolve_left hz
      obtain ⟨pre, y, ys, hrest, ⟨gy, hgyX, hy, hgy⟩, hpre⟩ :=
        exists_first (fun t => ∃ g ∈ X, Rep 22 t g ∧ g ∉ repSet span) rest
          ⟨t, ht, z, hzX, hzt, hz⟩
      subst hrest
      have hmem : (y :: ys) ∈ (pre ++ y :: ys).tails := by
        rw [List.mem_tails]
        exact List.suffix_append _ _
      have hy' : (!(newGen span y) || node B fuel (span ++ span.map (compT 22 y))
          (fix.filter fun m => actM y m == m)
          (ys.filter fun z => compT 22 y z == compT 22 z y)) = true := hall _ hmem
      rw [newGen_of_first hI hgyX hy hgy hpre hsq, Bool.not_true, Bool.false_or] at hy'
      exact node_sound hX hsq fuel _ _ _ hy' (nodeInv_step hI hgyX hy hpre hsq)

theorem bound_of_rootCheck
    {X : Subgroup (Equiv.Perm (Fin 22))} (hX : X ≤ hexadAut)
    (hsq : ∀ x ∈ X, x * x = 1) {B : ℕ} {T : Table} {C : List Table} {r : Equiv.Perm (Fin 22)}
    (hT : Rep 22 T r) (hr : r ∈ X) (hC : ∀ z ∈ X, z ≠ 1 → z ≠ r → ∃ t ∈ C, Rep 22 t z)
    (hsort : C.Pairwise fun a b => keyT a < keyT b) (hchk : rootCheck B T C = true) :
    Nat.card X * Nat.card (fixV X hX) ≤ B := by
  have h1 : Rep 22 (idT 22) (1 : Equiv.Perm (Fin 22)) := Rep.idT (by norm_num)
  have hset : ∀ g, g ∈ repSet [idT 22, T] ↔ g = 1 ∨ g = r := fun g => by
    constructor
    · rintro ⟨t, ht, hg⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (rep_unique hg h1)
      · exact Or.inr (rep_unique hg hT)
    · rintro (rfl | rfl)
      · exact ⟨_, List.mem_cons_self, h1⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hT⟩
  refine node_sound hX hsq 8 _ _ _ hchk ⟨fun t ht => ?_, (hset 1).2 (Or.inl rfl),
    fun g hg h hh => ?_, fun m hm hfix => ?_, fun z hz => ?_, hsort⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨1, one_mem X, h1⟩
    · exact ⟨r, hr, hT⟩
  · rw [hset] at hg hh ⊢
    rcases hg with hg | hg <;> rcases hh with hh | hh <;> rw [hg, hh]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul r)
    · exact Or.inr (mul_one r)
    · exact Or.inl (hsq r hr)
  · refine List.mem_filter.2 ⟨List.mem_range.2 hm, ?_⟩
    have h := theta_actM hT (hX hr) m
    rw [hfix r hr] at h
    rw [theta_injOn (actM_lt T m) hm h, beq_self_eq_true]
  · by_cases h1z : z = 1
    · exact Or.inl ((hset z).2 (Or.inl h1z))
    · by_cases hrz : z = r
      · exact Or.inl ((hset z).2 (Or.inr hrz))
      · exact Or.inr (hC z hz h1z hrz)

end CFSG.EvenSmallLie.UnitarySix.Hunt
