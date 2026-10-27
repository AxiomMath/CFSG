module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Fix

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def newGen (span : List ℕ) (y : ℕ) : Bool :=
  !(span.contains y) && span.all fun s => decide (y ≤ mulK y s)

@[expose] def node (B : ℕ) : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, span, fix, rest =>
    decide (span.length * fix.length ≤ B) &&
      rest.tails.all fun
        | [] => true
        | y :: ys => !(newGen span y) ||
          node B fuel (span ++ span.map (mulK y)) (fix.filter fun v => mulVecK y v == v)
            (ys.filter fun z => mulK y z == mulK z y)

@[expose] def fixList (r : ℕ) : List ℕ := (List.range 4096).filter fun v => mulVecK r v == v

@[expose] def rootCheck (B r : ℕ) (C base : List ℕ) : Bool :=
  node B 8 [idK, r] (base.filter fun v => mulVecK r v == v) C

@[expose] def repSet (L : List ℕ) : Set GL12 := {g | ∃ t ∈ L, Rep t g}

theorem commute_of_sq {X : Subgroup GL12} (hsq : ∀ x ∈ X, x * x = 1) {x y : GL12} (hx : x ∈ X)
    (hy : y ∈ X) : x * y = y * x := by
  have h := inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hx hy))
  rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq x hx),
    inv_eq_of_mul_eq_one_right (hsq y hy)] at h
  exact h.symm

structure NodeInv (X : Subgroup GL12) (Z : Set Vec12) (span fix rest : List ℕ) : Prop where
  span_le : ∀ t ∈ span, ∃ g ∈ X, Rep t g
  one_mem : (1 : GL12) ∈ repSet span
  mul_mem : ∀ g ∈ repSet span, ∀ h ∈ repSet span, g * h ∈ repSet span
  fix_mem : ∀ v < 4096, toVec 12 v ∈ Z → toVec 12 v ∈ fixV X → v ∈ fix
  cover : ∀ z ∈ X, z ∈ repSet span ∨ ∃ t ∈ rest, Rep t z
  sorted : rest.Pairwise (· < ·)
  rest_lt : ∀ t ∈ rest, t < 2 ^ 144

theorem card_le_length {X : Subgroup GL12} {span : List ℕ} (h : ∀ z ∈ X, z ∈ repSet span) :
    Nat.card X ≤ span.length := by
  have hc : ∀ z : X, ∃ i : Fin span.length, Rep span[i] z := fun z => by
    obtain ⟨t, ht, hr⟩ := h z z.2
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ⟨⟨i, hi⟩, hr⟩
  choose f hf using hc
  have hinj : Function.Injective f := fun a b hab => by
    have hb := hf b
    rw [← hab] at hb
    exact Subtype.ext ((hf a).unique hb)
  simpa using Nat.card_le_card_of_injective f hinj

theorem card_fixV_le {X : Subgroup GL12} {Z : Set Vec12} {fix : List ℕ}
    (h : ∀ v < 4096, toVec 12 v ∈ Z → toVec 12 v ∈ fixV X → v ∈ fix) :
    Nat.card ↥(Z ∩ fixV X) ≤ fix.length := by
  have hc : ∀ v : ↥(Z ∩ fixV X), ∃ i : Fin fix.length, toVec 12 fix[i] = v.1 := fun v => by
    have hmem := h (vecBits v.1) (vecBits_lt _) (by rw [toVec_vecBits]; exact v.2.1)
      (by rw [toVec_vecBits]; exact v.2.2)
    obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hmem
    exact ⟨⟨i, hi⟩, by simp only [Fin.getElem_fin, hfi, toVec_vecBits]⟩
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

theorem repSet_le {X : Subgroup GL12} {span : List ℕ} (h : ∀ t ∈ span, ∃ g ∈ X, Rep t g)
    {g : GL12} (hg : g ∈ repSet span) : g ∈ X := by
  obtain ⟨t, ht, hr⟩ := hg
  obtain ⟨g', hg', hr'⟩ := h t ht
  rwa [hr.unique hr']

theorem mem_repSet_extend {span : List ℕ} {y : ℕ} {gy : GL12} (hy : Rep y gy)
    (hspan : ∀ t ∈ span, ∃ g : GL12, Rep t g) {g : GL12} :
    g ∈ repSet (span ++ span.map (mulK y)) ↔ g ∈ repSet span ∨ ∃ h ∈ repSet span, g = gy * h := by
  constructor
  · rintro ⟨t, ht, hr⟩
    rcases List.mem_append.1 ht with ht | ht
    · exact Or.inl ⟨t, ht, hr⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      obtain ⟨h, hh⟩ := hspan s hs
      exact Or.inr ⟨h, ⟨s, hs, hh⟩, hr.unique (hy.mul hh)⟩
  · rintro (⟨t, ht, hr⟩ | ⟨h, ⟨s, hs, hh⟩, rfl⟩)
    · exact ⟨t, List.mem_append_left _ ht, hr⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hs), hy.mul hh⟩

section Step

variable {X : Subgroup GL12} {Z : Set Vec12} {span fix pre ys : List ℕ} {y : ℕ} {gy : GL12}

theorem mem_tail_of_first (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep t g ∧ g ∉ repSet span) {g : GL12}
    (hgX : g ∈ X) (hg : g ∉ repSet span) {t : ℕ} (ht : t ∈ pre ++ y :: ys) (hr : Rep t g) :
    t ∈ y :: ys := by
  rcases List.mem_append.1 ht with ht | ht
  · exact absurd ⟨g, hgX, hr, hg⟩ (hpre t ht)
  · exact ht

theorem newGen_of_first (hI : NodeInv X Z span fix (pre ++ y :: ys)) (hgyX : gy ∈ X)
    (hy : Rep y gy) (hgy : gy ∉ repSet span)
    (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep t g ∧ g ∉ repSet span) (hsq : ∀ x ∈ X, x * x = 1) :
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
    have hkey : t = mulK y s := hrt.key_unique (hy.mul hgs) (hI.rest_lt t ht) (mulK_lt _ _)
    rw [decide_eq_true_eq, ← hkey]
    rcases List.mem_cons.1 (mem_tail_of_first hpre (mul_mem hgyX hgsX) hprod ht hrt) with
      rfl | ht'
    · exact le_rfl
    · exact (List.pairwise_cons.1 (List.pairwise_append.1 hI.sorted).2.1).1 t ht' |>.le

theorem nodeInv_step (hI : NodeInv X Z span fix (pre ++ y :: ys)) (hgyX : gy ∈ X)
    (hy : Rep y gy) (hpre : ∀ t ∈ pre, ¬ ∃ g ∈ X, Rep t g ∧ g ∉ repSet span)
    (hsq : ∀ x ∈ X, x * x = 1) :
    NodeInv X Z (span ++ span.map (mulK y)) (fix.filter fun v => mulVecK y v == v)
      (ys.filter fun z => mulK y z == mulK z y) := by
  have hspan : ∀ t ∈ span, ∃ g : GL12, Rep t g := fun t ht => by
    obtain ⟨g, -, hg⟩ := hI.span_le t ht
    exact ⟨g, hg⟩
  have hle : ∀ {g}, g ∈ repSet span → g ∈ X := fun hg => repSet_le hI.span_le hg
  have hcomm : ∀ {g h}, g ∈ X → h ∈ X → g * h = h * g := fun hg hh => commute_of_sq hsq hg hh
  refine ⟨fun t ht => ?_, ?_, fun g hg h hh => ?_, fun v hv hZ hfix => ?_, fun z hz => ?_, ?_,
    fun t ht => hI.rest_lt t (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_filter.1 ht).1))⟩
  · rcases List.mem_append.1 ht with ht | ht
    · exact hI.span_le t ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      obtain ⟨gs, hgsX, hgs⟩ := hI.span_le s hs
      exact ⟨gy * gs, mul_mem hgyX hgsX, hy.mul hgs⟩
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
  · refine List.mem_filter.2 ⟨hI.fix_mem v hv hZ hfix, ?_⟩
    have h1 : toVec 12 (mulVecK y v) = toVec 12 v := by
      rw [toVec_mulVecK, hy]
      exact hfix gy hgyX
    rw [toVec_injOn (mulVecK_lt _ _) hv h1, beq_self_eq_true]
  · by_cases hzs : z ∈ repSet span
    · exact Or.inl ((mem_repSet_extend hy hspan).2 (Or.inl hzs))
    · obtain ⟨t, ht, hrt⟩ := (hI.cover z hz).resolve_left hzs
      rcases List.mem_cons.1 (mem_tail_of_first hpre hz hzs ht hrt) with rfl | ht'
      · rw [hrt.unique hy]
        exact Or.inl ((mem_repSet_extend hy hspan).2 (Or.inr ⟨1, hI.one_mem, (mul_one _).symm⟩))
      · refine Or.inr ⟨t, List.mem_filter.2 ⟨ht', ?_⟩, hrt⟩
        have e : mulK y t = mulK t y := (hy.mul hrt).key_unique
          (by rw [hcomm hgyX hz]; exact hrt.mul hy) (mulK_lt _ _) (mulK_lt _ _)
        rw [e, beq_self_eq_true]
  · exact (List.pairwise_cons.1 (List.pairwise_append.1 hI.sorted).2.1).2.filter _

end Step

theorem node_sound {X : Subgroup GL12} {Z : Set Vec12} (hsq : ∀ x ∈ X, x * x = 1) {B : ℕ} :
    ∀ (fuel : ℕ) (span fix rest : List ℕ), node B fuel span fix rest = true →
      NodeInv X Z span fix rest → Nat.card X * Nat.card ↥(Z ∩ fixV X) ≤ B
  | 0, _, _, _, h, _ => by simp [node] at h
  | fuel + 1, span, fix, rest, h, hI => by
    rw [node, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hB, hall⟩ := h
    by_cases hcov : ∀ z ∈ X, z ∈ repSet span
    · exact (Nat.mul_le_mul (card_le_length hcov) (card_fixV_le hI.fix_mem)).trans hB
    · push Not at hcov
      obtain ⟨z, hzX, hz⟩ := hcov
      obtain ⟨t, ht, hzt⟩ := (hI.cover z hzX).resolve_left hz
      obtain ⟨pre, y, ys, hrest, ⟨gy, hgyX, hy, hgy⟩, hpre⟩ :=
        exists_first (fun t => ∃ g ∈ X, Rep t g ∧ g ∉ repSet span) rest
          ⟨t, ht, z, hzX, hzt, hz⟩
      subst hrest
      have hmem : (y :: ys) ∈ (pre ++ y :: ys).tails := by
        rw [List.mem_tails]
        exact List.suffix_append _ _
      have hy' : (!(newGen span y) || node B fuel (span ++ span.map (mulK y))
          (fix.filter fun v => mulVecK y v == v)
          (ys.filter fun z => mulK y z == mulK z y)) = true := hall _ hmem
      rw [newGen_of_first hI hgyX hy hgy hpre hsq, Bool.not_true, Bool.false_or] at hy'
      exact node_sound hsq fuel _ _ _ hy' (nodeInv_step hI hgyX hy hpre hsq)

theorem bound_of_rootCheck {X : Subgroup GL12} {Z : Set Vec12} (hsq : ∀ x ∈ X, x * x = 1)
    {B R : ℕ} {C base : List ℕ} {r : GL12} (hR : Rep R r) (hr : r ∈ X)
    (hC : ∀ z ∈ X, z ≠ 1 → z ≠ r → ∃ t ∈ C, Rep t z) (hsort : C.Pairwise (· < ·))
    (hlt : ∀ t ∈ C, t < 2 ^ 144) (hbase : ∀ v < 4096, toVec 12 v ∈ Z → v ∈ base)
    (hchk : rootCheck B R C base = true) :
    Nat.card X * Nat.card ↥(Z ∩ fixV X) ≤ B := by
  have hset : ∀ g, g ∈ repSet [idK, R] ↔ g = 1 ∨ g = r := fun g => by
    constructor
    · rintro ⟨t, ht, hg⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (hg.unique rep_one)
      · exact Or.inr (hg.unique hR)
    · rintro (rfl | rfl)
      · exact ⟨_, List.mem_cons_self, rep_one⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hR⟩
  refine node_sound hsq 8 _ _ _ hchk ⟨fun t ht => ?_, (hset 1).2 (Or.inl rfl),
    fun g hg h hh => ?_, fun v hv hZ hfix => ?_, fun z hz => ?_, hsort, hlt⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨1, one_mem X, rep_one⟩
    · exact ⟨r, hr, hR⟩
  · rw [hset] at hg hh ⊢
    rcases hg with hg | hg <;> rcases hh with hh | hh <;> rw [hg, hh]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul r)
    · exact Or.inr (mul_one r)
    · exact Or.inl (hsq r hr)
  · refine List.mem_filter.2 ⟨hbase v hv hZ, ?_⟩
    have h1 : toVec 12 (mulVecK R v) = toVec 12 v := by
      rw [toVec_mulVecK, hR]
      exact hfix r hr
    rw [toVec_injOn (mulVecK_lt _ _) hv h1, beq_self_eq_true]
  · by_cases h1z : z = 1
    · exact Or.inl ((hset z).2 (Or.inl h1z))
    · by_cases hrz : z = r
      · exact Or.inl ((hset z).2 (Or.inr hrz))
      · exact Or.inr (hC z hz h1z hrz)

end CFSG.EvenSmallLie.OmegaEight.Stage2
