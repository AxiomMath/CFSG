module

public import CFSG.GF2Type.SmithTypeE.LMod.UaBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open scoped Pointwise

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList

section Rank

@[expose] def uaRank (i c : ℕ) : Set (Equiv.Perm (Fin 1953)) :=
  if c = 1 then tvP '' wPlane i
  else if c = 2 then
    {u | u ∉ tvP '' wPlane i ∧ ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ u = tvP p * tvP q}
  else (UA i : Set (Equiv.Perm (Fin 1953))) \ ({1} ∪ tvP '' wPlane i ∪
    {u | u ∉ tvP '' wPlane i ∧ ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ u = tvP p * tvP q})

theorem uaRank_one (i : ℕ) : uaRank i 1 = tvP '' wPlane i := by
  simp [uaRank]

theorem uaRank_two (i : ℕ) : uaRank i 2 =
    {u | u ∉ tvP '' wPlane i ∧ ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ u = tvP p * tvP q} := by
  simp [uaRank]

theorem uaRank_three (i : ℕ) : uaRank i 3 =
    (UA i : Set (Equiv.Perm (Fin 1953))) \ ({1} ∪ tvP '' wPlane i ∪
    {u | u ∉ tvP '' wPlane i ∧ ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ u = tvP p * tvP q}) := by
  simp [uaRank]

end Rank

section Zero

theorem f1_contains_uco (a : ℕ) : uco.contains a = true ↔ ∃ k < 49, uco[k]! = a := by
  have hs : uco.size = 49 := uaFacts.uco_size
  rw [Array.contains_iff_mem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hs ▸ hi, getElem!_pos uco i hi⟩
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < uco.size := hs ▸ hk
    exact ⟨k, hk', (getElem!_pos uco k hk').symm⟩

theorem f1_uco_ne {k l : ℕ} (hk : k < 49) (hl : l < 49) (hkl : k ≠ l) : uco[k]! ≠ uco[l]! := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact uaFacts.uco_inj l hl k h
  · exact fun e => uaFacts.uco_inj k hk l h e.symm

theorem f1_xor_lt {x y : ℕ} (hx : x < 512) (hy : y < 512) : x ^^^ y < 512 := by
  have h : x ^^^ y < 2 ^ 9 := Nat.xor_lt_two_pow (by norm_num; omega) (by norm_num; omega)
  exact lt_of_lt_of_eq h (by norm_num)

theorem f1_eq_of_xor_zero {x y : ℕ} (h : x ^^^ y = 0) : x = y := by
  have hx : x = (x ^^^ y) ^^^ y := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hx, h, Nat.zero_xor]

theorem f1_uSums {a : ℕ} (ha : a < 512) :
    uSums[a]! = true ↔ ∃ k < 49, ∃ l < 49, k ≠ l ∧ uco[k]! ^^^ uco[l]! = a := by
  have hs : a < uSums.size := by simp [uSums, ha]
  rw [Array.getElem!_eq_getD, Array.getD, dif_pos hs]
  simp only [uSums, Array.getInternal_eq_getElem, Array.getElem_ofFn, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]

theorem f1_uCls_one {a : ℕ} : uCls uSums a = 1 ↔ a ≠ 0 ∧ ∃ k < 49, uco[k]! = a := by
  unfold uCls
  split_ifs with h0 hc hs
  · obtain rfl : a = 0 := beq_iff_eq.1 h0
    simp
  · exact iff_of_true rfl ⟨by simpa using h0, (f1_contains_uco a).1 hc⟩
  · exact iff_of_false (by norm_num) fun h => hc ((f1_contains_uco a).2 h.2)
  · exact iff_of_false (by norm_num) fun h => hc ((f1_contains_uco a).2 h.2)

theorem f1_uCls_two {a : ℕ} (ha : a < 512) :
    uCls uSums a = 2 ↔ a ≠ 0 ∧ (∀ k < 49, uco[k]! ≠ a) ∧
      ∃ k < 49, ∃ l < 49, k ≠ l ∧ uco[k]! ^^^ uco[l]! = a := by
  unfold uCls
  split_ifs with h0 hc hs
  · obtain rfl : a = 0 := beq_iff_eq.1 h0
    simp
  · obtain ⟨k, hk, he⟩ := (f1_contains_uco a).1 hc
    exact iff_of_false (by norm_num) fun h => h.2.1 k hk he
  · exact iff_of_true rfl ⟨by simpa using h0,
      fun k hk he => hc ((f1_contains_uco a).2 ⟨k, hk, he⟩), (f1_uSums ha).1 hs⟩
  · exact iff_of_false (by norm_num) fun h => hs ((f1_uSums ha).2 h.2.2)

theorem f1_uCls_three {a : ℕ} (ha : a < 512) :
    uCls uSums a = 3 ↔ a ≠ 0 ∧ (∀ k < 49, uco[k]! ≠ a) ∧
      ¬ ∃ k < 49, ∃ l < 49, k ≠ l ∧ uco[k]! ^^^ uco[l]! = a := by
  unfold uCls
  split_ifs with h0 hc hs
  · obtain rfl : a = 0 := beq_iff_eq.1 h0
    simp
  · obtain ⟨k, hk, he⟩ := (f1_contains_uco a).1 hc
    exact iff_of_false (by norm_num) fun h => h.2.1 k hk he
  · exact iff_of_false (by norm_num) fun h => h.2.2 ((f1_uSums ha).1 hs)
  · exact iff_of_true rfl ⟨by simpa using h0,
      fun k hk he => hc ((f1_contains_uco a).2 ⟨k, hk, he⟩), fun h => hs ((f1_uSums ha).2 h)⟩

theorem f1_mem_tvP_zero {a : ℕ} (ha : a < 512) :
    psi0 a ∈ tvP '' wPlane 0 ↔ ∃ k < 49, uco[k]! = a := by
  constructor
  · rintro ⟨p, hp, hpe⟩
    obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
    rw [tvP_pt0 hk] at hpe
    exact ⟨k, hk, psi0_inj (uaFacts.uco_parts k hk).2 ha hpe⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨pt0 k, pt0_mem hk, tvP_pt0 hk⟩

theorem f1_pair {k l : ℕ} (hk : k < 49) (hl : l < 49) :
    tvP (pt0 k) * tvP (pt0 l) = psi0 (uco[k]! ^^^ uco[l]!) := by
  rw [tvP_pt0 hk, tvP_pt0 hl, psi0_xor]

theorem f1_two_iff {a : ℕ} (ha : a < 512) :
    (∃ p ∈ wPlane 0, ∃ q ∈ wPlane 0, p ≠ q ∧ psi0 a = tvP p * tvP q) ↔
      ∃ k < 49, ∃ l < 49, k ≠ l ∧ uco[k]! ^^^ uco[l]! = a := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq, he⟩
    obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
    obtain ⟨l, hl, rfl⟩ := exists_pt0 hq
    have hkl : k ≠ l := fun h => hpq (congrArg pt0 h)
    have hx : uco[k]! ^^^ uco[l]! < 512 :=
      f1_xor_lt (uaFacts.uco_parts k hk).2 (uaFacts.uco_parts l hl).2
    exact ⟨k, hk, l, hl, hkl, psi0_inj hx ha ((f1_pair hk hl).symm.trans he.symm)⟩
  · rintro ⟨k, hk, l, hl, hkl, hx⟩
    refine ⟨pt0 k, pt0_mem hk, pt0 l, pt0_mem hl, ?_, ?_⟩
    · intro hpq
      have h1 : psi0 uco[k]! = psi0 uco[l]! := by
        rw [← tvP_pt0 hk, ← tvP_pt0 hl, hpq]
      exact f1_uco_ne hk hl hkl (psi0_inj (uaFacts.uco_parts k hk).2 (uaFacts.uco_parts l hl).2 h1)
    · rw [f1_pair hk hl, hx]

theorem f1_mem_class_one {u : Equiv.Perm (Fin 1953)} :
    u ∈ uaRank 0 1 ↔ ∃ a < 512, uCls uSums a = 1 ∧ psi0 a = u := by
  rw [uaRank_one]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
    exact ⟨uco[k]!, (uaFacts.uco_parts k hk).2,
      f1_uCls_one.2 ⟨(uaFacts.uco_parts k hk).1.ne', k, hk, rfl⟩, (tvP_pt0 hk).symm⟩
  · rintro ⟨a, -, hcls, rfl⟩
    obtain ⟨-, k, hk, hka⟩ := f1_uCls_one.1 hcls
    exact ⟨pt0 k, pt0_mem hk, by rw [tvP_pt0 hk, hka]⟩

theorem f1_mem_class_two {u : Equiv.Perm (Fin 1953)} :
    u ∈ uaRank 0 2 ↔ ∃ a < 512, uCls uSums a = 2 ∧ psi0 a = u := by
  rw [uaRank_two, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnot, p, hp, q, hq, hpq, rfl⟩
    obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
    obtain ⟨l, hl, rfl⟩ := exists_pt0 hq
    have hkl : k ≠ l := fun h => hpq (congrArg pt0 h)
    have hx : uco[k]! ^^^ uco[l]! < 512 :=
      f1_xor_lt (uaFacts.uco_parts k hk).2 (uaFacts.uco_parts l hl).2
    have hne : uco[k]! ^^^ uco[l]! ≠ 0 := fun h => f1_uco_ne hk hl hkl (f1_eq_of_xor_zero h)
    have hnP1 : ∀ m < 49, uco[m]! ≠ uco[k]! ^^^ uco[l]! := by
      intro m hm he
      apply hnot
      refine ⟨pt0 m, pt0_mem hm, ?_⟩
      rw [tvP_pt0 hm, he]
      exact (f1_pair hk hl).symm
    exact ⟨uco[k]! ^^^ uco[l]!, hx,
      (f1_uCls_two hx).2 ⟨hne, hnP1, k, hk, l, hl, hkl, rfl⟩, (f1_pair hk hl).symm⟩
  · rintro ⟨a, ha, hcls, rfl⟩
    obtain ⟨ha0, hnP1, k, hk, l, hl, hkl, hx⟩ := (f1_uCls_two ha).1 hcls
    refine ⟨?_, (f1_two_iff ha).2 ⟨k, hk, l, hl, hkl, hx⟩⟩
    rintro ⟨r, hr, hre⟩
    obtain ⟨m, hm, rfl⟩ := exists_pt0 hr
    rw [tvP_pt0 hm] at hre
    exact hnP1 m hm (psi0_inj (uaFacts.uco_parts m hm).2 ha hre)

theorem f1_mem_class_three {u : Equiv.Perm (Fin 1953)} :
    u ∈ uaRank 0 3 ↔ ∃ a < 512, uCls uSums a = 3 ∧ psi0 a = u := by
  rw [uaRank_three, Set.mem_diff]
  constructor
  · rintro ⟨hUA, hnot⟩
    obtain ⟨a, ha, rfl⟩ := mem_UA_zero.1 hUA
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or] at hnot
    obtain ⟨⟨h1, hT⟩, hS⟩ := hnot
    have ha0 : a ≠ 0 := fun h => h1 (by rw [h, psi0_zero])
    have hP1 : ¬ ∃ k < 49, uco[k]! = a := fun h => hT ((f1_mem_tvP_zero ha).2 h)
    have hP2 : ¬ ∃ k < 49, ∃ l < 49, k ≠ l ∧ uco[k]! ^^^ uco[l]! = a :=
      fun h => hS ⟨hT, (f1_two_iff ha).2 h⟩
    exact ⟨a, ha, (f1_uCls_three ha).2 ⟨ha0, fun k hk he => hP1 ⟨k, hk, he⟩, hP2⟩, rfl⟩
  · rintro ⟨a, ha, hcls, rfl⟩
    obtain ⟨ha0, hP1, hP2⟩ := (f1_uCls_three ha).1 hcls
    refine ⟨mem_UA_zero.2 ⟨a, ha, rfl⟩, ?_⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or]
    refine ⟨⟨fun h => ha0 (psi0_inj ha (by norm_num) (h.trans psi0_zero.symm)), ?_⟩, ?_⟩
    · intro h
      obtain ⟨k, hk, he⟩ := (f1_mem_tvP_zero ha).1 h
      exact hP1 k hk he
    · rintro ⟨-, h⟩
      exact hP2 ((f1_two_iff ha).1 h)

theorem mem_uaRank_zero_iff {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3) {u : Equiv.Perm (Fin 1953)} :
    u ∈ uaRank 0 c ↔ ∃ a < 512, uCls uSums a = c ∧ psi0 a = u := by
  rcases hc with rfl | rfl | rfl
  · exact f1_mem_class_one
  · exact f1_mem_class_two
  · exact f1_mem_class_three

theorem f1_card_filter {q : ℕ → Prop} [DecidablePred q] (p : ℕ → Bool)
    (hp : ∀ a, p a = true ↔ q a) :
    ((Finset.range 512).filter q).card = (List.range 512).countP p := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]
  refine congrArg List.length (List.filter_congr fun a _ => ?_)
  by_cases h : q a
  · simp [h, (hp a).2 h]
  · have h' : p a = false := by
      cases hpa : p a
      · rfl
      · exact absurd ((hp a).1 hpa) h
    simp [h, h']

theorem f1_ncard_set {c : ℕ} :
    {a : ℕ | a < 512 ∧ uCls uSums a = c}.ncard =
      (List.range 512).countP (fun v => uCls uSums v == c) := by
  have hset : {a : ℕ | a < 512 ∧ uCls uSums a = c} =
      ↑((Finset.range 512).filter (fun a => uCls uSums a = c)) := by
    ext a
    simp
  rw [hset, Set.ncard_coe_finset]
  exact f1_card_filter _ (fun a => beq_iff_eq)

theorem f1_ncard_aux {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3) :
    (uaRank 0 c).ncard = (List.range 512).countP (fun v => uCls uSums v == c) := by
  have himg : uaRank 0 c = psi0 '' {a : ℕ | a < 512 ∧ uCls uSums a = c} := by
    ext u
    rw [mem_uaRank_zero_iff hc, Set.mem_image]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, h1, h2⟩
      exact ⟨a, ⟨ha, h1⟩, h2⟩
    · rintro ⟨a, ⟨ha, h1⟩, h2⟩
      exact ⟨a, ha, h1, h2⟩
  have hinj : Set.InjOn psi0 {a : ℕ | a < 512 ∧ uCls uSums a = c} :=
    fun a ha b hb h => psi0_inj ha.1 hb.1 h
  rw [himg, Set.InjOn.ncard_image hinj, f1_ncard_set]

theorem ncard_uaRank_zero {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3) :
    (uaRank 0 c).ncard = if c = 1 then 49 else if c = 2 then 294 else 168 := by
  rw [f1_ncard_aux hc]
  obtain ⟨h1, h2, h3⟩ := uCounts_holds
  rcases hc with rfl | rfl | rfl
  · rw [h1]; simp
  · rw [h2]; simp
  · rw [h3]; simp

theorem bitProd_congr {G : Type*} [Group G] {g g' : ℕ → G} (a n : ℕ)
    (h : ∀ j < n, g j = g' j) : bitProd g a n = bitProd g' a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bitProd_succ, bitProd_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem getElem!_findIdx {A : Array ℕ} {x : ℕ} (hx : x ∈ A) :
    A[A.findIdx (· == x)]! = x := by
  have hlt : A.findIdx (· == x) < A.size := Array.findIdx_lt_size_of_exists ⟨x, hx, by simp⟩
  rw [getElem!_pos A _ hlt]
  exact beq_iff_eq.mp (Array.findIdx_getElem (w := hlt))

theorem tvP_eq_psi0_pos0 {y : Fin 1953} (hy : y ∈ wPlane 0) :
    tvP y = psi0 (uco[pos0 y.val]!) := by
  have hsz : (planePtsArr[0]!).size = 49 := by
    rw [planePtsArr_get (by norm_num : (0:ℕ) < 1395), ← card_planeSet_eq 0,
      card_planeSet (by norm_num : (0:ℕ) < 1395)]
  have hmem : y.val ∈ planePtsArr[0]! := by
    rw [planePtsArr_get (by norm_num : (0:ℕ) < 1395)]
    exact mem_planePts.2 ⟨y.isLt, mem_wPlane.1 hy⟩
  have hlt : pos0 y.val < 49 := by
    unfold pos0
    rw [← hsz]
    exact Array.findIdx_lt_size_of_exists ⟨y.val, hmem, by simp⟩
  have hget : (planePtsArr[0]!)[pos0 y.val]! = y.val := by
    unfold pos0
    exact getElem!_findIdx hmem
  have hpt : pt0 (pos0 y.val) = y := by
    apply Fin.ext
    rw [pt0_val hlt]
    exact hget
  exact (congrArg tvP hpt.symm).trans (tvP_pt0 hlt)

theorem image_wPlane_zero_tvP {p : ℕ} (hp1 : p < 1953) (hp2 : planeImg p 0 = 0) :
    ⇑(tvP ⟨p, hp1⟩) '' wPlane 0 = wPlane 0 := by
  rw [image_wPlane_tvP (by norm_num : (0:ℕ) < 1395)]
  exact congrArg wPlane hp2

theorem conj_gen_psi0 {p : ℕ} (hp1 : p < 1953) (hp2 : planeImg p 0 = 0) {j : ℕ} (hj : j < 9) :
    tvP ⟨p, hp1⟩ * tvP (gen0 j) * (tvP ⟨p, hp1⟩)⁻¹ = psi0 ((ucols p)[j]!) := by
  have hW := image_wPlane_zero_tvP hp1 hp2
  have hw : (tvP ⟨p, hp1⟩) (gen0 j) ∈ wPlane 0 := by
    rw [← hW]
    exact Set.mem_image_of_mem _ (gen0_mem j hj)
  have hug : ugens[j]! < 1953 := by
    have h := (gen0 j).isLt
    rwa [gen0_val hj] at h
  have hx : ((tvP ⟨p, hp1⟩) (gen0 j) : ℕ) = (tvTab[p]!)[ugens[j]!]! := by
    rw [tvTab_get hp1 hug, ← gen0_val hj]
    exact tvP_apply ⟨p, hp1⟩ (gen0 j)
  have hsz : (ucols p).size = 9 := by simp [ucols]
  have hj' : j < (ucols p).size := by omega
  have hcol : (ucols p)[j]! = uco[pos0 (tvTab[p]!)[ugens[j]!]!]! := by
    rw [getElem!_pos (ucols p) j hj']
    simp [ucols]
  rw [mul_tvP_mul_inv (tvP_mem (⟨p, hp1⟩ : Fin 1953)), tvP_eq_psi0_pos0 hw, hx, hcol]

theorem conj_psi0 {p : ℕ} (hp : p ∈ stabGens) (a : ℕ) :
    tvP ⟨p, (mem_stabGens.1 hp).1⟩ * psi0 a * (tvP ⟨p, (mem_stabGens.1 hp).1⟩)⁻¹ =
      psi0 (CFSG.SmithE.applyCols (ucols p) a) := by
  obtain ⟨hp1, hp2⟩ := mem_stabGens.1 hp
  have hsz : (ucols p).size = 9 := by simp [ucols]
  have e0 : psi0 a = bitProd (fun j => tvP (gen0 j)) a 9 := rfl
  have e1 : tvP ⟨p, hp1⟩ * psi0 a * (tvP ⟨p, hp1⟩)⁻¹ =
      bitProd (fun j => psi0 ((ucols p)[j]!)) a 9 := by
    rw [e0, conj_bitProd]
    exact bitProd_congr a 9 (fun j hj => conj_gen_psi0 hp1 hp2 hj)
  have e2 : bitProd (fun j => psi0 ((ucols p)[j]!)) a 9 =
      psi0 (CFSG.SmithE.applyCols (ucols p) a) := by
    refine (bitProd_hom psi0_zero psi0_xor (fun j => (ucols p)[j]!) a 9).trans ?_
    rw [CFSG.SmithE.applyCols, hsz]
  exact e1.trans e2

theorem conj_step {p : ℕ} (hp : p ∈ stabGens) {g' : Equiv.Perm (Fin 1953)} {r u v : ℕ}
    (hg' : g' * psi0 r * g'⁻¹ = psi0 u) (hap : CFSG.SmithE.applyCols (ucols p) u = v) :
    tvP ⟨p, (mem_stabGens.1 hp).1⟩ * g' * psi0 r *
      (tvP ⟨p, (mem_stabGens.1 hp).1⟩ * g')⁻¹ = psi0 v := by
  calc tvP ⟨p, (mem_stabGens.1 hp).1⟩ * g' * psi0 r *
        (tvP ⟨p, (mem_stabGens.1 hp).1⟩ * g')⁻¹
      = tvP ⟨p, (mem_stabGens.1 hp).1⟩ * (g' * psi0 r * g'⁻¹) *
          (tvP ⟨p, (mem_stabGens.1 hp).1⟩)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
    _ = tvP ⟨p, (mem_stabGens.1 hp).1⟩ * psi0 u * (tvP ⟨p, (mem_stabGens.1 hp).1⟩)⁻¹ := by
        rw [hg']
    _ = psi0 (CFSG.SmithE.applyCols (ucols p) u) := conj_psi0 hp u
    _ = psi0 v := by rw [hap]

theorem conj_tree_zero (a : ℕ) (ha : a < 512) (h0 : uCls uSums a ≠ 0) :
    ∃ g ∈ PA 0, g * psi0 (uRoot uSums (uCls uSums a)) * g⁻¹ = psi0 a := by
  refine uReach_holds
    (fun a => uCls uSums a ≠ 0 →
      ∃ g ∈ PA 0, g * psi0 (uRoot uSums (uCls uSums a)) * g⁻¹ = psi0 a) ?_ ?_ a ha h0
  · intro v _ hr hv0
    simp only [beq_iff_eq] at hr
    refine ⟨1, (PA 0).one_mem, ?_⟩
    rw [← hr]
    simp
  · intro p hp u _ v _ he hQu hv0
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hp0, hcls⟩, hap⟩ := he
    have hQu' : uCls uSums u ≠ 0 →
        ∃ g ∈ PA 0, g * psi0 (uRoot uSums (uCls uSums u)) * g⁻¹ = psi0 u := hQu
    have hu0 : uCls uSums u ≠ 0 := by
      rw [hcls]
      exact hv0
    obtain ⟨g', hg', hg'e⟩ := hQu' hu0
    have hmem : p ∈ stabGens := mem_stabGens.2 ⟨hp, hp0⟩
    rw [← hcls]
    exact ⟨tvP ⟨p, (mem_stabGens.1 hmem).1⟩ * g',
      (PA 0).mul_mem (tvP_mem_PA_zero hmem) hg', conj_step hmem hg'e hap⟩

theorem exists_PA_conj_zero {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3) {u v : Equiv.Perm (Fin 1953)}
    (hu : u ∈ uaRank 0 c) (hv : v ∈ uaRank 0 c) : ∃ g ∈ PA 0, g * u * g⁻¹ = v := by
  obtain ⟨a, ha, hac, rfl⟩ := (mem_uaRank_zero_iff hc).1 hu
  obtain ⟨b, hb, hbc, rfl⟩ := (mem_uaRank_zero_iff hc).1 hv
  have hc0 : c ≠ 0 := by omega
  obtain ⟨ga, hga, hgae⟩ := conj_tree_zero a ha (by rw [hac]; exact hc0)
  obtain ⟨gb, hgb, hgbe⟩ := conj_tree_zero b hb (by rw [hbc]; exact hc0)
  have hroot : uRoot uSums (uCls uSums b) = uRoot uSums (uCls uSums a) := by
    rw [hac, hbc]
  rw [hroot] at hgbe
  refine ⟨gb * ga⁻¹, (PA 0).mul_mem hgb ((PA 0).inv_mem hga), ?_⟩
  rw [← hgae, ← hgbe]
  group

end Zero

section General

theorem mem_uaRank_cases {i : ℕ} (hi : i < 1395) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ UA i)
    (hu1 : u ≠ 1) : u ∈ uaRank i 1 ∨ u ∈ uaRank i 2 ∨ u ∈ uaRank i 3 := by
  by_cases h1 : u ∈ tvP '' wPlane i
  · left
    rw [uaRank_one]
    exact h1
  by_cases h2 : ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ u = tvP p * tvP q
  · right
    left
    rw [uaRank_two]
    exact ⟨h1, h2⟩
  right
  right
  rw [uaRank_three]
  refine ⟨hu, fun h => ?_⟩
  rcases h with (h | h) | h
  · exact hu1 (Set.mem_singleton_iff.mp h)
  · exact h1 h
  · exact h2 h.2

theorem conj_one {i j : ℕ} {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g)
    (h : ⇑g '' wPlane i = wPlane j) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ uaRank i 1) :
    g * u * g⁻¹ ∈ uaRank j 1 := by
  rw [uaRank_one] at hu ⊢
  obtain ⟨p, hp, rfl⟩ := hu
  have hm : g p ∈ wPlane j := by
    have := Set.mem_image_of_mem (⇑g) hp
    rwa [h] at this
  exact ⟨g p, hm, (hg p).symm⟩

theorem conj_two {i j : ℕ} {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g)
    (h : ⇑g '' wPlane i = wPlane j) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ uaRank i 2) :
    g * u * g⁻¹ ∈ uaRank j 2 := by
  have hgm : ∀ p ∈ wPlane i, g p ∈ wPlane j := fun p hp => by
    have := Set.mem_image_of_mem (⇑g) hp
    rwa [h] at this
  have hgi : ∀ r ∈ wPlane j, g⁻¹ r ∈ wPlane i := fun r hr => by
    have := Set.mem_image_of_mem (⇑g⁻¹) hr
    rwa [image_wPlane_inv h] at this
  rw [uaRank_two] at hu ⊢
  obtain ⟨hu1, p, hp, q, hq, hpq, rfl⟩ := hu
  refine ⟨?_, g p, hgm p hp, g q, hgm q hq, fun e => hpq (g.injective e), ?_⟩
  · rintro ⟨r, hr, hreq⟩
    apply hu1
    refine ⟨g⁻¹ r, hgi r hr, ?_⟩
    have h1 := hg.inv r
    rw [inv_inv] at h1
    rw [← h1, hreq]
    group
  · calc g * (tvP p * tvP q) * g⁻¹ = (g * tvP p * g⁻¹) * (g * tvP q * g⁻¹) := by group
      _ = tvP (g p) * tvP (g q) := by rw [hg p, hg q]

theorem conj_three {i j : ℕ} {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g)
    (h : ⇑g '' wPlane i = wPlane j) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ uaRank i 3) :
    g * u * g⁻¹ ∈ uaRank j 3 := by
  have hgi : ∀ r ∈ wPlane j, g⁻¹ r ∈ wPlane i := fun r hr => by
    have := Set.mem_image_of_mem (⇑g⁻¹) hr
    rwa [image_wPlane_inv h] at this
  rw [uaRank_three] at hu ⊢
  obtain ⟨hUA, hnot⟩ := hu
  refine ⟨conj_mem_UA hg h hUA, fun hv => ?_⟩
  rcases hv with (hv | hv) | hv
  · have h1 : g * u * g⁻¹ = 1 := Set.mem_singleton_iff.mp hv
    have e : u = 1 := by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    exact hnot (Or.inl (Or.inl (Set.mem_singleton_iff.mpr e)))
  · obtain ⟨r, hr, hreq⟩ := hv
    apply hnot
    refine Or.inl (Or.inr ⟨g⁻¹ r, hgi r hr, ?_⟩)
    have h1 := hg.inv r
    rw [inv_inv] at h1
    rw [← h1, hreq]
    group
  · have hv2 : g * u * g⁻¹ ∈ uaRank j 2 := by
      rw [uaRank_two]
      exact hv
    have hb := conj_two hg.inv (image_wPlane_inv h) hv2
    have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rw [e, uaRank_two] at hb
    exact hnot (Or.inr hb)

theorem conj_mem_uaRank {i j : ℕ} (hi : i < 1395) (hj : j < 1395) {g : Equiv.Perm (Fin 1953)}
    (hg : IsTvAut g) (h : ⇑g '' wPlane i = wPlane j) {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3)
    {u : Equiv.Perm (Fin 1953)} (hu : u ∈ uaRank i c) : g * u * g⁻¹ ∈ uaRank j c := by
  rcases hc with rfl | rfl | rfl
  · exact conj_one hg h hu
  · exact conj_two hg h hu
  · exact conj_three hg h hu

theorem ncard_uaRank {i : ℕ} (hi : i < 1395) {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3) :
    (uaRank i c).ncard = if c = 1 then 49 else if c = 2 then 294 else 168 := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have himg : (fun u : Equiv.Perm (Fin 1953) => x * u * x⁻¹) '' uaRank 0 c = uaRank i c := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact conj_mem_uaRank (by norm_num) hi (isTvAut_of_mem hx) hW hc hu
    · intro hv
      refine ⟨x⁻¹ * v * x, ?_, ?_⟩
      · have h' := conj_mem_uaRank hi (by norm_num) (isTvAut_of_mem hx).inv
          (image_wPlane_inv hW) hc hv
        rwa [inv_inv] at h'
      · show x * (x⁻¹ * v * x) * x⁻¹ = v
        group
  have hinj : Function.Injective (fun u : Equiv.Perm (Fin 1953) => x * u * x⁻¹) := by
    intro a b hab
    simpa using hab
  rw [← ncard_uaRank_zero hc, ← himg]
  exact Set.ncard_image_of_injective _ hinj

theorem exists_PA_conj {i : ℕ} (hi : i < 1395) {c : ℕ} (hc : c = 1 ∨ c = 2 ∨ c = 3)
    {u v : Equiv.Perm (Fin 1953)} (hu : u ∈ uaRank i c) (hv : v ∈ uaRank i c) :
    ∃ g ∈ PA i, g * u * g⁻¹ = v := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have hinv := image_wPlane_inv hW
  have hu' : x⁻¹ * u * x ∈ uaRank 0 c := by
    have h' := conj_mem_uaRank hi (by norm_num) (isTvAut_of_mem hx).inv hinv hc hu
    rwa [inv_inv] at h'
  have hv' : x⁻¹ * v * x ∈ uaRank 0 c := by
    have h' := conj_mem_uaRank hi (by norm_num) (isTvAut_of_mem hx).inv hinv hc hv
    rwa [inv_inv] at h'
  obtain ⟨g, hg, hgu⟩ := exists_PA_conj_zero hc hu' hv'
  refine ⟨x * g * x⁻¹, conj_mem_PA hx hW hg, ?_⟩
  calc x * g * x⁻¹ * u * (x * g * x⁻¹)⁻¹ = x * (g * (x⁻¹ * u * x) * g⁻¹) * x⁻¹ := by group
    _ = x * (x⁻¹ * v * x) * x⁻¹ := by rw [hgu]
    _ = v := by group

theorem orbit_rank_one {i : ℕ} (hi : i < 1395) {O : Set (Equiv.Perm (Fin 1953))} (hO : O ⊆ UA i)
    (h1 : (1 : Equiv.Perm (Fin 1953)) ∉ O) (hne : O.Nonempty)
    (hinv : ∀ g ∈ PA i, ∀ u ∈ O, g * u * g⁻¹ ∈ O) (hdvd : O.ncard ∣ 784) :
    O = tvP '' wPlane i := by
  have hfull : ∀ c, (c = 1 ∨ c = 2 ∨ c = 3) → ∀ u ∈ O, u ∈ uaRank i c → uaRank i c ⊆ O :=
    fun c hc u hu huc v hv => by
      obtain ⟨g, hg, rfl⟩ := exists_PA_conj hi hc huc hv
      exact hinv g hg u hu
  have hx : ∀ c, (c = 1 ∨ c = 2 ∨ c = 3) →
      (O ∩ uaRank i c).ncard = 0 ∨ (O ∩ uaRank i c).ncard = (uaRank i c).ncard := by
    intro c hc
    by_cases h : ∃ u ∈ O, u ∈ uaRank i c
    · obtain ⟨u, hu, huc⟩ := h
      right
      rw [Set.inter_eq_right.2 (hfull c hc u hu huc)]
    · left
      rw [Set.ncard_eq_zero (Set.toFinite _)]
      exact Set.eq_empty_iff_forall_notMem.2 fun u hu => h ⟨u, hu.1, hu.2⟩
  have d12 : Disjoint (uaRank i 1) (uaRank i 2) := Set.disjoint_left.2 fun u a1 a2 => by
    rw [uaRank_one] at a1
    rw [uaRank_two] at a2
    exact a2.1 a1
  have d13 : Disjoint (uaRank i 1) (uaRank i 3) := Set.disjoint_left.2 fun u a1 a3 => by
    rw [uaRank_one] at a1
    rw [uaRank_three] at a3
    exact a3.2 (Or.inl (Or.inr a1))
  have d23 : Disjoint (uaRank i 2) (uaRank i 3) := Set.disjoint_left.2 fun u a2 a3 => by
    rw [uaRank_two] at a2
    rw [uaRank_three] at a3
    exact a3.2 (Or.inr a2)
  have hd : ∀ X Y : Set (Equiv.Perm (Fin 1953)), Disjoint X Y → Disjoint (O ∩ X) (O ∩ Y) :=
    fun X Y hXY => Set.disjoint_left.2 fun u hu hu' => Set.disjoint_left.1 hXY hu.2 hu'.2
  have hcover : O = (O ∩ uaRank i 1) ∪ (O ∩ uaRank i 2) ∪ (O ∩ uaRank i 3) := by
    ext u
    constructor
    · intro hu
      rcases mem_uaRank_cases hi (hO hu) (fun e => h1 (e ▸ hu)) with h | h | h
      · exact Or.inl (Or.inl ⟨hu, h⟩)
      · exact Or.inl (Or.inr ⟨hu, h⟩)
      · exact Or.inr ⟨hu, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  have hsplit : O.ncard = (O ∩ uaRank i 1).ncard + (O ∩ uaRank i 2).ncard +
      (O ∩ uaRank i 3).ncard := by
    conv_lhs => rw [hcover]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hd _ _ d13, hd _ _ d23⟩)
        (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq (hd _ _ d12) (Set.toFinite _) (Set.toFinite _)]
  have hpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have n1 : (uaRank i 1).ncard = 49 :=
    (ncard_uaRank (c := 1) hi (Or.inl rfl)).trans (by norm_num)
  have n2 : (uaRank i 2).ncard = 294 :=
    (ncard_uaRank (c := 2) hi (Or.inr (Or.inl rfl))).trans (by norm_num)
  have n3 : (uaRank i 3).ncard = 168 :=
    (ncard_uaRank (c := 3) hi (Or.inr (Or.inr rfl))).trans (by norm_num)
  have hx1 := hx 1 (Or.inl rfl)
  have hx2 := hx 2 (Or.inr (Or.inl rfl))
  have hx3 := hx 3 (Or.inr (Or.inr rfl))
  rw [n1] at hx1
  rw [n2] at hx2
  rw [n3] at hx3
  have key : (O ∩ uaRank i 1).ncard = 49 ∧ (O ∩ uaRank i 2).ncard = 0 ∧
      (O ∩ uaRank i 3).ncard = 0 := by
    rw [hsplit] at hdvd hpos
    rcases hx1 with e1 | e1 <;> rcases hx2 with e2 | e2 <;> rcases hx3 with e3 | e3 <;>
      rw [e1, e2, e3] at hdvd hpos <;> rw [e1, e2, e3] <;>
      first
        | exact ⟨rfl, rfl, rfl⟩
        | (exfalso; norm_num at hdvd hpos)
        | (exfalso; omega)
  have hB0 : O ∩ uaRank i 2 = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 key.2.1
  have hC0 : O ∩ uaRank i 3 = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 key.2.2
  have hA0 : O ∩ uaRank i 1 = uaRank i 1 := Set.eq_of_subset_of_ncard_le Set.inter_subset_right
    (le_of_eq (by rw [key.1, n1])) (Set.toFinite _)
  rw [hcover, hB0, hC0, hA0, Set.union_empty, Set.union_empty, uaRank_one i]

end General

end CFSG.GF2Type.SmithTypeE.LMod
