module

public import CFSG.Blueprint.ChevalleyStrings
public import CFSG.Blueprint.ChevalleySimpleRootOperators

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint

open CFSG.Blueprint.Chevalley Module


@[expose] def rt (k : ℕ) : Fin Tag.F4.rank → ℤ := Tag.F4.rootCertificate.root k

theorem certRoots_length : Tag.F4.rootCertificate.roots.length = 48 := by
  rw [Tag.rootCertificate_length]; rfl

theorem isRoot_rt {k : ℕ} (hk : k < 48) : IsRoot Tag.F4 (rt k) :=
  RootCertificate.isRoot_root Tag.F4.rootCertificate_check k (by rw [certRoots_length]; exact hk)

@[expose] def lab (q : Fin 52) : Label Tag.F4 :=
  if h : (q : ℕ) < 4 then Sum.inl ⟨q, h⟩ else Sum.inr ⟨rt ((q : ℕ) - 4), isRoot_rt (by omega)⟩

theorem lab_of_lt {q : Fin 52} (h : (q : ℕ) < 4) : lab q = Sum.inl ⟨q, h⟩ := dite_eq_left h

theorem lab_of_ge {q : Fin 52} (h : ¬(q : ℕ) < 4) :
    lab q = Sum.inr ⟨rt ((q : ℕ) - 4), isRoot_rt (by omega)⟩ := dite_eq_right h

theorem lab_surjective : Function.Surjective lab := by
  rintro (i | ⟨α, hα⟩)
  · exact ⟨⟨i, lt_trans i.2 (by decide)⟩, lab_of_lt i.2⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.F4.rootCertificate_check hα
    rw [certRoots_length] at hk
    refine ⟨⟨k + 4, by omega⟩, ?_⟩
    rw [lab_of_ge (by simp)]
    simp [rt]

@[expose] def rIdx (v : Fin Tag.F4.rank → ℤ) : ℕ :=
  (List.range 48).findIdx fun k => decide (rt k = v)

theorem rIdx_spec {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot Tag.F4 v) :
    rIdx v < 48 ∧ rt (rIdx v) = v := by
  obtain ⟨k, hk, hkv⟩ := RootCertificate.exists_root_eq Tag.F4.rootCertificate_check hv
  rw [certRoots_length] at hk
  have hex : ∃ x ∈ List.range 48, decide (rt x = v) = true :=
    ⟨k, List.mem_range.2 hk, decide_eq_true (by simpa [rt] using hkv)⟩
  have hlt : rIdx v < (List.range 48).length := List.findIdx_lt_length_of_exists hex
  rw [List.length_range] at hlt
  refine ⟨hlt, ?_⟩
  have := List.findIdx_getElem (w := by rwa [List.length_range])
  simpa [rIdx] using this

theorem lab_rIdx {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot Tag.F4 v) :
    lab ⟨4 + rIdx v, by have := (rIdx_spec hv).1; omega⟩ = Sum.inr ⟨v, hv⟩ := by
  rw [lab_of_ge (by simp)]
  have h := (rIdx_spec hv).2
  simp only [Nat.add_sub_cancel_left]
  congr 1
  exact Subtype.ext h


variable (R : Type*) [CommRing R]

@[expose] def toVec (m : ℕ) : RootModule Tag.F4 R :=
  ∑ k : Fin 52, if m.testBit k then Finsupp.single (lab k) 1 else 0

@[expose] def lvec (L : List ℕ) : RootModule Tag.F4 R :=
  (L.map fun l => toVec R (1 <<< l)).sum

variable {R}

theorem toVec_zero : toVec R 0 = 0 := by
  simp [toVec]

theorem toVec_xor [CharP R 2] (m n : ℕ) : toVec R (m ^^^ n) = toVec R m + toVec R n := by
  simp only [toVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases n.testBit k <;>
    simp [← Finsupp.single_add, one_add_one_eq_two, CharTwo.two_eq_zero]

theorem toVec_one_shiftLeft (k : Fin 52) : toVec R (1 <<< (k : ℕ)) = Finsupp.single (lab k) 1 := by
  rw [toVec, Finset.sum_eq_single k]
  · simp [Nat.one_shiftLeft]
  · intro j _ hj
    have hj' : (k : ℕ) ≠ j := fun h => hj (Fin.ext h).symm
    simp [Nat.one_shiftLeft, hj']
  · simp

theorem toVec_one_shiftLeft' {l : ℕ} (hl : l < 52) :
    toVec R (1 <<< l) = Finsupp.single (lab ⟨l, hl⟩) 1 :=
  toVec_one_shiftLeft ⟨l, hl⟩

theorem lvec_cons (l : ℕ) (L : List ℕ) : lvec R (l :: L) = toVec R (1 <<< l) + lvec R L := by
  simp [lvec]

theorem lvec_nil : lvec R [] = 0 := by
  simp [lvec]

theorem lvec_append (L M : List ℕ) : lvec R (L ++ M) = lvec R L + lvec R M := by
  simp [lvec, List.map_append, List.sum_append]

theorem lvec_singleton {b : ℕ} (hb : b < 52) :
    lvec R [b] = Finsupp.single (lab ⟨b, hb⟩) 1 := by
  rw [lvec_cons, lvec_nil, add_zero, toVec_one_shiftLeft' hb]

@[expose] def xorMap (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | l :: L => f l ^^^ xorMap f L

@[expose] def idxMask (L : List ℕ) : ℕ := xorMap (fun l => 1 <<< l) L

theorem toVec_xorMap [CharP R 2] (f : ℕ → ℕ) (L : List ℕ) :
    toVec R (xorMap f L) = (L.map fun l => toVec R (f l)).sum := by
  induction L with
  | nil => simp [xorMap, toVec_zero]
  | cons l L ih => rw [xorMap, toVec_xor, ih, List.map_cons, List.sum_cons]

theorem toVec_idxMask [CharP R 2] (L : List ℕ) : toVec R (idxMask L) = lvec R L := by
  rw [idxMask, toVec_xorMap]
  rfl

theorem card_label_F4 : Fintype.card (Label Tag.F4) = 52 := by
  rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

theorem lab_bijective : Function.Bijective lab :=
  (Fintype.bijective_iff_surjective_and_card lab).2
    ⟨lab_surjective, by rw [Fintype.card_fin, card_label_F4]⟩

theorem toVec_apply_lab (m : ℕ) (q : Fin 52) :
    toVec R m (lab q) = if m.testBit q then 1 else 0 := by
  rw [toVec, Finsupp.finsetSum_apply, Finset.sum_eq_single q]
  · split_ifs <;> simp
  · intro k _ hk
    split_ifs
    · rw [Finsupp.single_apply, ite_eq_right_iff]
      intro h
      exact absurd (lab_bijective.1 h) hk
    · rfl
  · simp


@[expose] def cartanOdd (b : ℕ) (i : Fin Tag.F4.rank) : Bool :=
  if h : b < 4 then decide ((Tag.cartan Tag.F4 ⟨b, h⟩ i).natAbs % 2 = 1) else false

@[expose] def xCol (i : Fin Tag.F4.rank) (b : ℕ) : List ℕ :=
  if b < 4 then b :: (if cartanOdd b i then [4 + rIdx (Pi.single i 1)] else [])
  else if rt (b - 4) = Pi.single i 1 then [b]
  else if rt (b - 4) = -Pi.single i 1 then [b, i, 4 + rIdx (Pi.single i 1)]
  else (List.range (Tag.F4.stringData.up (b - 4) i + 1)).flatMap fun m =>
    if (Nat.choose (Tag.F4.stringData.down (b - 4) i + m) m) % 2 = 1 then
      [4 + rIdx (rt (b - 4) + (m : ℤ) • Pi.single i 1)] else []

@[expose] def yCol (i : Fin Tag.F4.rank) (b : ℕ) : List ℕ :=
  if b < 4 then b :: (if cartanOdd b i then [4 + rIdx (-Pi.single i 1)] else [])
  else if rt (b - 4) = -Pi.single i 1 then [b]
  else if rt (b - 4) = Pi.single i 1 then [b, i, 4 + rIdx (-Pi.single i 1)]
  else (List.range (Tag.F4.stringData.down (b - 4) i + 1)).flatMap fun m =>
    if (Nat.choose (Tag.F4.stringData.up (b - 4) i + m) m) % 2 = 1 then
      [4 + rIdx (rt (b - 4) - (m : ℤ) • Pi.single i 1)] else []


theorem natCast_eq_ite [CharP R 2] (n : ℕ) : (n : R) = if n % 2 = 1 then 1 else 0 := by
  have h2 : ((2 : ℕ) : R) = 0 := by exact_mod_cast (CharTwo.two_eq_zero : (2 : R) = 0)
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [Nat.cast_add, Nat.cast_mul, h2, zero_mul, zero_add]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem single_lab_ge {b : Fin 52} (hb : ¬(b : ℕ) < 4) :
    Finsupp.single (lab b) (1 : R) = rootVec Tag.F4 R (rt ((b : ℕ) - 4)) := by
  rw [lab_of_ge hb, rootVec_eq_basisVec_of_isRoot (isRoot_rt (by omega))]

theorem rootVec_eq_lvec {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot Tag.F4 v) :
    rootVec Tag.F4 R v = lvec R [4 + rIdx v] := by
  have hlt := (rIdx_spec hv).1
  rw [lvec_singleton (by omega), lab_rIdx hv, rootVec_eq_basisVec_of_isRoot hv]

theorem string_eq {k : ℕ} (hk : k < 48) (i : Fin Tag.F4.rank) (h₁ : rt k ≠ Pi.single i 1)
    (h₂ : rt k ≠ -Pi.single i 1) :
    stringUp Tag.F4 i (rt k) = Tag.F4.stringData.up k i ∧
      stringDown Tag.F4 i (rt k) = Tag.F4.stringData.down k i := by
  have hk' : k < Tag.F4.rootCertificate.roots.length := by rw [certRoots_length]; exact hk
  have hα := isRoot_rt hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨-, h'⟩ := StringData.isRoot_root_add_iff Tag.F4.rootCertificate_check
    Tag.F4.stringData_check hk' i h₁ h₂
  have h'' : ∀ m : ℤ, IsRoot Tag.F4 (rt k + m • Pi.single i 1) ↔
      -(Tag.F4.stringData.down k i : ℤ) ≤ m ∧ m ≤ Tag.F4.stringData.up k i := h'
  have e : ∀ m : ℤ, (-(stringDown Tag.F4 i (rt k) : ℤ) ≤ m ∧ m ≤ stringUp Tag.F4 i (rt k)) ↔
      (-(Tag.F4.stringData.down k i : ℤ) ≤ m ∧ m ≤ Tag.F4.stringData.up k i) := fun m => by
    rw [← h, h'']
  have a1 := (e (stringUp Tag.F4 i (rt k))).1 ⟨by omega, le_rfl⟩
  have a2 := (e (Tag.F4.stringData.up k i)).2 ⟨by omega, le_rfl⟩
  have a3 := (e (-(stringDown Tag.F4 i (rt k) : ℤ))).1 ⟨le_rfl, by omega⟩
  have a4 := (e (-(Tag.F4.stringData.down k i : ℤ))).2 ⟨le_rfl, by omega⟩
  omega

theorem lvec_flatMap_range (n : ℕ) (g : ℕ → List ℕ) :
    lvec R ((List.range n).flatMap g) = ∑ m ∈ Finset.range n, lvec R (g m) := by
  induction n with
  | zero => simp [lvec_nil]
  | succ n ih => rw [List.range_succ, List.flatMap_append, lvec_append, ih, Finset.sum_range_succ,
      List.flatMap_singleton]


theorem isRoot_string {k : ℕ} (hk : k < 48) (i : Fin Tag.F4.rank) (h₁ : rt k ≠ Pi.single i 1)
    (h₂ : rt k ≠ -Pi.single i 1) (m : ℤ) :
    IsRoot Tag.F4 (rt k + m • Pi.single i 1) ↔
      -(Tag.F4.stringData.down k i : ℤ) ≤ m ∧ m ≤ Tag.F4.stringData.up k i := by
  have hk' : k < Tag.F4.rootCertificate.roots.length := by rw [certRoots_length]; exact hk
  obtain ⟨-, h'⟩ := StringData.isRoot_root_add_iff Tag.F4.rootCertificate_check
    Tag.F4.stringData_check hk' i h₁ h₂
  exact h' m

variable [CharP R 2]

theorem cartan_term (i : Fin Tag.F4.rank) (b : Fin 52) (hb : (b : ℕ) < 4) :
    ((((Tag.cartan Tag.F4 ⟨b, hb⟩ i).natAbs : ℕ) : R) * 1) • rootVec Tag.F4 R (Pi.single i 1) =
      lvec R (if cartanOdd b i then [4 + rIdx (Pi.single i 1)] else []) := by
  by_cases hodd : (Tag.cartan Tag.F4 ⟨b, hb⟩ i).natAbs % 2 = 1
  · have hc : cartanOdd b i = true := by simp [cartanOdd, hb, hodd]
    rw [hc, if_pos rfl, natCast_eq_ite, if_pos hodd, mul_one, one_smul,
      rootVec_eq_lvec (isRoot_single Tag.F4 i)]
  · have hc : cartanOdd b i = false := by simp [cartanOdd, hb, hodd]
    rw [hc, natCast_eq_ite, if_neg hodd, zero_mul, zero_smul]
    simp [lvec_nil]

theorem xOp_one_single (i : Fin Tag.F4.rank) (b : Fin 52) :
    xOp Tag.F4 R i 1 (Finsupp.single (lab b) 1) = lvec R (xCol i b) := by
  by_cases hb : (b : ℕ) < 4
  · have hx : xCol i b = (b : ℕ) :: (if cartanOdd b i then [4 + rIdx (Pi.single i 1)] else []) := by
      simp [xCol, hb]
    rw [hx, lvec_cons, toVec_one_shiftLeft b, ← cartan_term i b hb, lab_of_lt hb]
    change xOp Tag.F4 R i 1 (hVec Tag.F4 R ⟨b, hb⟩) = _
    rw [xOp_apply_hVec]
    rfl
  · have hk : (b : ℕ) - 4 < 48 := by have := b.2; omega
    have hv := isRoot_rt hk
    have hb1 : lvec R [(b : ℕ)] = rootVec Tag.F4 R (rt ((b : ℕ) - 4)) := by
      rw [lvec_singleton b.2]
      exact single_lab_ge hb
    rw [single_lab_ge hb]
    by_cases h1 : rt ((b : ℕ) - 4) = Pi.single i 1
    · have hx : xCol i b = [(b : ℕ)] := by simp [xCol, hb, h1]
      rw [hx, hb1, h1, xOp_apply_rootVec_single]
    · by_cases h2 : rt ((b : ℕ) - 4) = -Pi.single i 1
      · have hx : xCol i b = [(b : ℕ), (i : ℕ), 4 + rIdx (Pi.single i 1)] := by
          simp [xCol, hb, h2, (single_ne_neg_single i).symm]
        have hi52 : (i : ℕ) < 52 := lt_of_lt_of_le i.2 (by decide)
        have hr52 : 4 + rIdx (Pi.single i 1) < 52 := by
          have := (rIdx_spec (isRoot_single Tag.F4 i)).1; omega
        have e1 : (Finsupp.single (lab b) 1 : RootModule Tag.F4 R) =
            rootVec Tag.F4 R (-Pi.single i 1) := by rw [single_lab_ge hb, h2]
        have e2 : (Finsupp.single (lab ⟨i, hi52⟩) 1 : RootModule Tag.F4 R) = hVec Tag.F4 R i := by
          rw [lab_of_lt i.2]; rfl
        have e3 : (Finsupp.single (lab ⟨4 + rIdx (Pi.single i 1), hr52⟩) 1 : RootModule Tag.F4 R) =
            rootVec Tag.F4 R (Pi.single i 1) := by
          rw [← lvec_singleton hr52, ← rootVec_eq_lvec (isRoot_single Tag.F4 i)]
        rw [hx, lvec_cons, lvec_cons, lvec_cons, lvec_nil, add_zero,
          toVec_one_shiftLeft b, toVec_one_shiftLeft' hi52, toVec_one_shiftLeft' hr52,
          e1, e2, e3, h2, xOp_apply_rootVec_neg_single, one_smul, one_pow, one_smul, add_assoc]
      · have hx : xCol i b = (List.range (Tag.F4.stringData.up ((b : ℕ) - 4) i + 1)).flatMap
            (fun m => if (Nat.choose (Tag.F4.stringData.down ((b : ℕ) - 4) i + m) m) % 2 = 1 then
              [4 + rIdx (rt ((b : ℕ) - 4) + (m : ℤ) • Pi.single i 1)] else []) := by
          simp [xCol, hb, h1, h2]
        rw [hx, lvec_flatMap_range, xOp_apply_rootVec_of_ne i 1 hv h1 h2,
          (string_eq hk i h1 h2).1, (string_eq hk i h1 h2).2]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmu : m ≤ Tag.F4.stringData.up ((b : ℕ) - 4) i := by
          have := Finset.mem_range.1 hm; omega
        have hroot : IsRoot Tag.F4 (rt ((b : ℕ) - 4) + (m : ℤ) • Pi.single i 1) :=
          (isRoot_string hk i h1 h2 m).2 ⟨by omega, by exact_mod_cast hmu⟩
        rw [one_pow, mul_one, natCast_eq_ite]
        by_cases hodd : (Nat.choose (Tag.F4.stringData.down ((b : ℕ) - 4) i + m) m) % 2 = 1
        · rw [if_pos hodd, if_pos hodd, one_smul, rootVec_eq_lvec hroot]
        · rw [if_neg hodd, if_neg hodd, zero_smul, lvec_nil]


theorem cartan_term_y (i : Fin Tag.F4.rank) (b : Fin 52) (hb : (b : ℕ) < 4) :
    ((((Tag.cartan Tag.F4 ⟨b, hb⟩ i).natAbs : ℕ) : R) * 1) • rootVec Tag.F4 R (-Pi.single i 1) =
      lvec R (if cartanOdd b i then [4 + rIdx (-Pi.single i 1)] else []) := by
  by_cases hodd : (Tag.cartan Tag.F4 ⟨b, hb⟩ i).natAbs % 2 = 1
  · have hc : cartanOdd b i = true := by simp [cartanOdd, hb, hodd]
    rw [hc, if_pos rfl, natCast_eq_ite, if_pos hodd, mul_one, one_smul,
      rootVec_eq_lvec (isRoot_neg_single Tag.F4 i)]
  · have hc : cartanOdd b i = false := by simp [cartanOdd, hb, hodd]
    rw [hc, natCast_eq_ite, if_neg hodd, zero_mul, zero_smul]
    simp [lvec_nil]

theorem yOp_one_single (i : Fin Tag.F4.rank) (b : Fin 52) :
    yOp Tag.F4 R i 1 (Finsupp.single (lab b) 1) = lvec R (yCol i b) := by
  by_cases hb : (b : ℕ) < 4
  · have hx : yCol i b = (b : ℕ) :: (if cartanOdd b i then [4 + rIdx (-Pi.single i 1)] else []) := by
      simp [yCol, hb]
    rw [hx, lvec_cons, toVec_one_shiftLeft b, ← cartan_term_y i b hb, lab_of_lt hb]
    change yOp Tag.F4 R i 1 (hVec Tag.F4 R ⟨b, hb⟩) = _
    rw [yOp_apply_hVec]
    rfl
  · have hk : (b : ℕ) - 4 < 48 := by have := b.2; omega
    have hv := isRoot_rt hk
    have hb1 : lvec R [(b : ℕ)] = rootVec Tag.F4 R (rt ((b : ℕ) - 4)) := by
      rw [lvec_singleton b.2]
      exact single_lab_ge hb
    rw [single_lab_ge hb]
    by_cases h1 : rt ((b : ℕ) - 4) = -Pi.single i 1
    · have hx : yCol i b = [(b : ℕ)] := by simp [yCol, hb, h1]
      rw [hx, hb1, h1, yOp_apply_rootVec_neg_single]
    · by_cases h2 : rt ((b : ℕ) - 4) = Pi.single i 1
      · have hx : yCol i b = [(b : ℕ), (i : ℕ), 4 + rIdx (-Pi.single i 1)] := by
          simp [yCol, hb, h2, (single_ne_neg_single i)]
        have hi52 : (i : ℕ) < 52 := lt_of_lt_of_le i.2 (by decide)
        have hr52 : 4 + rIdx (-Pi.single i 1) < 52 := by
          have := (rIdx_spec (isRoot_neg_single Tag.F4 i)).1; omega
        have e1 : (Finsupp.single (lab b) 1 : RootModule Tag.F4 R) =
            rootVec Tag.F4 R (Pi.single i 1) := by rw [single_lab_ge hb, h2]
        have e2 : (Finsupp.single (lab ⟨i, hi52⟩) 1 : RootModule Tag.F4 R) = hVec Tag.F4 R i := by
          rw [lab_of_lt i.2]; rfl
        have e3 : (Finsupp.single (lab ⟨4 + rIdx (-Pi.single i 1), hr52⟩) 1 :
            RootModule Tag.F4 R) = rootVec Tag.F4 R (-Pi.single i 1) := by
          rw [← lvec_singleton hr52, ← rootVec_eq_lvec (isRoot_neg_single Tag.F4 i)]
        rw [hx, lvec_cons, lvec_cons, lvec_cons, lvec_nil, add_zero,
          toVec_one_shiftLeft b, toVec_one_shiftLeft' hi52, toVec_one_shiftLeft' hr52,
          e1, e2, e3, h2, yOp_apply_rootVec_single, one_smul, one_pow, one_smul, add_assoc]
      · have hx : yCol i b = (List.range (Tag.F4.stringData.down ((b : ℕ) - 4) i + 1)).flatMap
            (fun m => if (Nat.choose (Tag.F4.stringData.up ((b : ℕ) - 4) i + m) m) % 2 = 1 then
              [4 + rIdx (rt ((b : ℕ) - 4) - (m : ℤ) • Pi.single i 1)] else []) := by
          simp [yCol, hb, h1, h2]
        rw [hx, lvec_flatMap_range, yOp_apply_rootVec_of_ne i 1 hv h2 h1,
          (string_eq hk i h2 h1).1, (string_eq hk i h2 h1).2]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmu : m ≤ Tag.F4.stringData.down ((b : ℕ) - 4) i := by
          have := Finset.mem_range.1 hm; omega
        have hroot : IsRoot Tag.F4 (rt ((b : ℕ) - 4) - (m : ℤ) • Pi.single i 1) := by
          have := (isRoot_string hk i h2 h1 (-(m : ℤ))).2 ⟨by omega, by omega⟩
          rwa [neg_smul, ← sub_eq_add_neg] at this
        rw [one_pow, mul_one, natCast_eq_ite]
        by_cases hodd : (Nat.choose (Tag.F4.stringData.up ((b : ℕ) - 4) i + m) m) % 2 = 1
        · rw [if_pos hodd, if_pos hodd, one_smul, rootVec_eq_lvec hroot]
        · rw [if_neg hodd, if_neg hodd, zero_smul, lvec_nil]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint
