module

public import Certificates.Certificate38700

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

theorem lineKeysCheck_holds :
    lineKeys.size = 365211 ∧
      ∀ k < 365211, 0 < (linePair k).1 ∧ (linePair k).1 < (linePair k).2 ∧
        (linePair k).2 < ((linePair k).1 ^^^ (linePair k).2) ∧
        ((linePair k).1 ^^^ (linePair k).2) < 4096 ∧ qf (linePair k).1 = false ∧
        qf (linePair k).2 = false ∧ bf (linePair k).1 (linePair k).2 = false ∧
        lineIdx (linePair k).1 (linePair k).2 = k :=
  Certificates.certificate38700.1

theorem lineCompleteCheck_holds :
    ∀ a ∈ singArr, ∀ b ∈ singArr, a ≠ b → bf a b = false → lineIdx3 a b (a ^^^ b) < 365211 :=
  Certificates.certificate38700.2

theorem nat_xor_eq_zero {p q : ℕ} : p ^^^ q = 0 ↔ p = q := by
  constructor
  · intro h
    calc p = p ^^^ (q ^^^ q) := by rw [Nat.xor_self, Nat.xor_zero]
      _ = (p ^^^ q) ^^^ q := by rw [Nat.xor_assoc]
      _ = q := by rw [h, Nat.zero_xor]
  · rintro rfl
    exact Nat.xor_self p

theorem nat_xor_three {p q r : ℕ} (h : p ^^^ q ^^^ r = 0) : p = q ^^^ r :=
  nat_xor_eq_zero.mp (by rw [← Nat.xor_assoc]; exact h)

theorem sorted_triple_unique {u w x u' w' x' : ℕ} (h1 : u < w) (h2 : w < x) (h1' : u' < w')
    (h2' : w' < x') (h : ({u, w, x} : Finset ℕ) = {u', w', x'}) :
    u = u' ∧ w = w' ∧ x = x' := by
  have hu : u ∈ ({u', w', x'} : Finset ℕ) := by rw [← h]; simp
  have hw : w ∈ ({u', w', x'} : Finset ℕ) := by rw [← h]; simp
  have hx : x ∈ ({u', w', x'} : Finset ℕ) := by rw [← h]; simp
  have hu' : u' ∈ ({u, w, x} : Finset ℕ) := by rw [h]; simp
  have hw' : w' ∈ ({u, w, x} : Finset ℕ) := by rw [h]; simp
  have hx' : x' ∈ ({u, w, x} : Finset ℕ) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw hx hu' hw' hx'
  omega

theorem nat_sort3 {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : a ^^^ b ^^^ c = 0) :
    min a (min b c) < (min a (min b c)) ^^^ (max a (max b c)) ∧
    (min a (min b c)) ^^^ (max a (max b c)) < max a (max b c) ∧
    ({a, b, c} : Finset ℕ) =
      {min a (min b c), (min a (min b c)) ^^^ (max a (max b c)), max a (max b c)} := by
  have hA : a = b ^^^ c := nat_xor_three h
  have hB : b = a ^^^ c := nat_xor_three (by rw [Nat.xor_comm b a]; exact h)
  have hC : c = a ^^^ b := nat_xor_three (by rw [Nat.xor_assoc, Nat.xor_comm c]; exact h)
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  ·
    have hlo : min a (min b c) = a := by omega
    have hhi : max a (max b c) = c := by omega
    rw [hlo, hhi, ← hB]
    exact ⟨h1, h2, rfl⟩
  · exfalso
    omega
  ·
    have hlo : min a (min b c) = a := by omega
    have hhi : max a (max b c) = b := by omega
    rw [hlo, hhi, ← hC]
    exact ⟨h3, by omega, by ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  ·
    have hlo : min a (min b c) = c := by omega
    have hhi : max a (max b c) = b := by omega
    have hm : c ^^^ b = a := by rw [Nat.xor_comm, ← hA]
    rw [hlo, hhi, hm]
    exact ⟨by omega, by omega, by ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  ·
    have hlo : min a (min b c) = b := by omega
    have hhi : max a (max b c) = c := by omega
    rw [hlo, hhi, ← hA]
    exact ⟨by omega, by omega, by ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  ·
    have hlo : min a (min b c) = b := by omega
    have hhi : max a (max b c) = a := by omega
    have hm : b ^^^ a = c := by rw [Nat.xor_comm, ← hC]
    rw [hlo, hhi, hm]
    exact ⟨by omega, by omega, by ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exfalso
    omega
  ·
    have hlo : min a (min b c) = c := by omega
    have hhi : max a (max b c) = a := by omega
    have hm : c ^^^ a = b := by rw [Nat.xor_comm, ← hB]
    rw [hlo, hhi, hm]
    exact ⟨by omega, by omega, by ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

theorem sort_line {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    min x (min y (x ^^^ y)) < (min x (min y (x ^^^ y))) ^^^ (max x (max y (x ^^^ y))) ∧
    (min x (min y (x ^^^ y))) ^^^ (max x (max y (x ^^^ y))) < max x (max y (x ^^^ y)) ∧
    ({x, y, x ^^^ y} : Finset ℕ) =
      {min x (min y (x ^^^ y)), (min x (min y (x ^^^ y))) ^^^ (max x (max y (x ^^^ y))),
        max x (max y (x ^^^ y))} := by
  have hyz : y ≠ x ^^^ y := by
    intro h
    have h2 : x ^^^ y ^^^ y = 0 := by rw [← h, Nat.xor_self]
    exact hx ((nat_xor_three h2).trans (Nat.xor_self y))
  have hxz : x ≠ x ^^^ y := by
    intro h
    have h2 : x ^^^ y ^^^ x = 0 := by rw [← h, Nat.xor_self]
    have h3 : y ^^^ x ^^^ x = 0 := by rw [Nat.xor_comm y x]; exact h2
    exact hy ((nat_xor_three h3).trans (Nat.xor_self x))
  exact nat_sort3 hxy hyz hxz (Nat.xor_self (x ^^^ y))

structure LineFacts : Prop where
  size : lineKeys.size = 365211
  entry : ∀ k < 365211, 0 < (linePair k).1 ∧ (linePair k).1 < (linePair k).2 ∧
    (linePair k).2 < ((linePair k).1 ^^^ (linePair k).2) ∧
      ((linePair k).1 ^^^ (linePair k).2) < 4096 ∧ qf (linePair k).1 = false ∧
        qf (linePair k).2 = false ∧ bf (linePair k).1 (linePair k).2 = false ∧
          lineIdx (linePair k).1 (linePair k).2 = k
  complete : ∀ a ∈ singArr, ∀ b ∈ singArr, a ≠ b → bf a b = false →
    lineIdx3 a b (a ^^^ b) < 365211

theorem lineFacts : LineFacts :=
  ⟨lineKeysCheck_holds.1, lineKeysCheck_holds.2, lineCompleteCheck_holds⟩

theorem mem_singArr {x : ℕ} : x ∈ singArr ↔ x < 4096 ∧ x ≠ 0 ∧ qf x = false := by
  simp only [singArr, List.mem_toArray, List.mem_filter, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, Bool.not_eq_true']

theorem linePair_lineIdx {u w : ℕ} (hu : u < 4096) (hw : w < 4096)
    (h : lineIdx u w < 365211) : linePair (lineIdx u w) = (u, w) := by
  unfold lineIdx at h ⊢
  generalize hk : 4096 * u + w = k at h ⊢
  set i := lowerBoundGo lineKeys k 40 0 lineKeys.size with hi
  by_cases hc : i < 365211 ∧ lineKeys[i]! = k
  · have e : (if i < 365211 && lineKeys[i]! == k then i else 365211) = i := by
      simp [hc.1, hc.2]
    rw [e]
    unfold linePair
    rw [hc.2, ← hk]
    simp only [Prod.mk.injEq]
    omega
  · have e : (if i < 365211 && lineKeys[i]! == k then i else 365211) = 365211 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rw [if_neg hc]
    rw [e] at h
    exact absurd h (lt_irrefl _)

@[expose] def lineOfPair (u w : V12) : Finset V12 := {u, w, u + w}

@[expose] def IsTsLine (s : Finset V12) : Prop :=
  ∃ u w : V12, u ≠ 0 ∧ w ≠ 0 ∧ u ≠ w ∧ TsPair u w ∧ s = lineOfPair u w

@[expose] def TsLine : Type := {s : Finset V12 // IsTsLine s}

@[expose] def lineSet (k : ℕ) : Finset V12 :=
  lineOfPair (dec12 (linePair k).1) (dec12 (linePair k).2)

theorem lineSet_eq (k : ℕ) :
    lineSet k = {dec12 (linePair k).1, dec12 (linePair k).2,
      dec12 ((linePair k).1 ^^^ (linePair k).2)} := by
  rw [lineSet, lineOfPair, dec12_xor]

theorem xor_lt_4096 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) : a ^^^ b < 4096 :=
  Nat.xor_lt_two_pow (n := 12) ha hb

theorem lineSet_lineIdx3 {x y : ℕ} (hx : x < 4096) (hy : y < 4096)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hqx : qf x = false) (hqy : qf y = false) (hxy : x ≠ y)
    (hb : bf x y = false) :
    lineIdx3 x y (x ^^^ y) < 365211 ∧
      lineSet (lineIdx3 x y (x ^^^ y)) = lineOfPair (dec12 x) (dec12 y) := by
  have hF := lineFacts
  have hlt : lineIdx3 x y (x ^^^ y) < 365211 :=
    hF.complete x (mem_singArr.mpr ⟨hx, hx0, hqx⟩) y (mem_singArr.mpr ⟨hy, hy0, hqy⟩) hxy hb
  refine ⟨hlt, ?_⟩
  obtain ⟨hs1, hs2, hs3⟩ := sort_line hx0 hy0 hxy
  have hxy4 : x ^^^ y < 4096 := xor_lt_4096 hx hy
  have hhi : max x (max y (x ^^^ y)) < 4096 := max_lt hx (max_lt hy hxy4)
  have hlo : min x (min y (x ^^^ y)) < 4096 := lt_of_le_of_lt (min_le_left _ _) hx
  have hk : lineIdx3 x y (x ^^^ y) =
      lineIdx (min x (min y (x ^^^ y))) ((min x (min y (x ^^^ y))) ^^^
        (max x (max y (x ^^^ y)))) := rfl
  rw [hk] at hlt ⊢
  have hpair := linePair_lineIdx hlo (by omega) hlt
  rw [lineSet_eq, hpair]
  simp only
  have hc : (min x (min y (x ^^^ y))) ^^^ ((min x (min y (x ^^^ y))) ^^^
      (max x (max y (x ^^^ y)))) = max x (max y (x ^^^ y)) := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hc]
  have himg := congrArg (Finset.image dec12) hs3
  simp only [Finset.image_insert, Finset.image_singleton] at himg
  rw [lineOfPair, ← dec12_xor, himg]

theorem dec12_ne_zero {a : ℕ} (ha : a < 4096) (ha0 : a ≠ 0) : dec12 a ≠ 0 := fun h =>
  ha0 (eq_of_dec12_eq ha (by norm_num) (h.trans dec12_zero.symm))

theorem isTsLine_lineSet {k : ℕ} (hk : k < 365211) :
    IsTsLine (lineSet k) := by
  obtain ⟨h0, h1, h2, h3, hq1, hq2, hb, -⟩ := lineFacts.entry k hk
  refine ⟨dec12 (linePair k).1, dec12 (linePair k).2, dec12_ne_zero (by omega) (by omega),
    dec12_ne_zero (by omega) (by omega), fun h => ?_, tsPair_dec12 hq1 hq2 hb, rfl⟩
  have := eq_of_dec12_eq (by omega) (by omega) h
  omega

theorem finset_codes_eq {a b c a' b' c' : ℕ} (ha : a < 4096) (hb : b < 4096) (hc : c < 4096)
    (ha' : a' < 4096) (hb' : b' < 4096) (hc' : c' < 4096)
    (h : ({dec12 a, dec12 b, dec12 c} : Finset V12) = {dec12 a', dec12 b', dec12 c'}) :
    ({a, b, c} : Finset ℕ) = {a', b', c'} := by
  have := congrArg (Finset.image enc12) h
  simpa only [Finset.image_insert, Finset.image_singleton, enc12_dec12 ha, enc12_dec12 hb,
    enc12_dec12 hc, enc12_dec12 ha', enc12_dec12 hb', enc12_dec12 hc'] using this

theorem lineSet_injective {k l : ℕ} (hk : k < 365211)
    (hl : l < 365211) (h : lineSet k = lineSet l) : k = l := by
  obtain ⟨a0, a1, a2, a3, -, -, -, ak⟩ := lineFacts.entry k hk
  obtain ⟨b0, b1, b2, b3, -, -, -, bl⟩ := lineFacts.entry l hl
  rw [lineSet_eq, lineSet_eq] at h
  have hset := finset_codes_eq (by omega) (by omega) a3 (by omega) (by omega) b3 h
  obtain ⟨e1, e2, -⟩ := sorted_triple_unique a1 a2 b1 b2 hset
  rw [← ak, ← bl, e1, e2]

theorem exists_lineSet_eq {s : Finset V12} (hs : IsTsLine s) :
    ∃ k < 365211, lineSet k = s := by
  obtain ⟨u, w, hu0, hw0, huw, hts, rfl⟩ := hs
  obtain ⟨hqu, hqw, hbuw⟩ := hts
  set a := enc12 u with ha
  set b := enc12 w with hb
  have hau : dec12 a = u := dec12_enc12 u
  have hbw : dec12 b = w := dec12_enc12 w
  have ha4 : a < 4096 := enc12_lt u
  have hb4 : b < 4096 := enc12_lt w
  have ha0 : a ≠ 0 := fun h => hu0 (by rw [← hau, h, dec12_zero])
  have hb0 : b ≠ 0 := fun h => hw0 (by rw [← hbw, h, dec12_zero])
  have hab : a ≠ b := fun h => huw (by rw [← hau, ← hbw, h])
  have hqa : qf a = false := by
    have := q12_dec12 a
    rw [hau, hqu] at this
    cases h : qf a
    · rfl
    · rw [h] at this; simp [bit] at this
  have hqb : qf b = false := by
    have := q12_dec12 b
    rw [hbw, hqw] at this
    cases h : qf b
    · rfl
    · rw [h] at this; simp [bit] at this
  have hbf : bf a b = false := by
    have := B12_dec12 a b
    rw [hau, hbw, hbuw] at this
    cases h : bf a b
    · rfl
    · rw [h] at this; simp [bit] at this
  obtain ⟨hlt, hset⟩ := lineSet_lineIdx3 ha4 hb4 ha0 hb0 hqa hqb hab hbf
  exact ⟨_, hlt, by rw [hset, hau, hbw]⟩

@[expose] def lineOfIdx (k : Fin 365211) : TsLine :=
  ⟨lineSet k.val, isTsLine_lineSet k.2⟩

theorem lineOfIdx_bijective : Function.Bijective lineOfIdx := by
  constructor
  · intro k l h
    exact Fin.ext (lineSet_injective k.2 l.2 (congrArg Subtype.val h))
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk, hks⟩ := exists_lineSet_eq hs
    exact ⟨⟨k, hk⟩, Subtype.ext hks⟩

@[expose] noncomputable def lineEquiv : Fin 365211 ≃ TsLine :=
  Equiv.ofBijective lineOfIdx lineOfIdx_bijective

end CFSG.GF2Type.SmithTypeE.DMod
