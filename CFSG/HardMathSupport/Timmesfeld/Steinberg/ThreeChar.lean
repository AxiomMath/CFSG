module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

@[expose] def Z3 : Type := Multiplicative (ZMod 3)

instance : CommGroup Z3 := inferInstanceAs (CommGroup (Multiplicative (ZMod 3)))

@[expose] def Z3.ofAdd (x : ZMod 3) : Z3 := Multiplicative.ofAdd x

@[expose] def Z3.toAdd (x : Z3) : ZMod 3 := Multiplicative.toAdd x

theorem Z3.ofAdd_add (x y : ZMod 3) : Z3.ofAdd (x + y) = Z3.ofAdd x * Z3.ofAdd y := rfl

theorem Z3.ofAdd_zero : Z3.ofAdd 0 = 1 := rfl

theorem Z3.toAdd_ofAdd (x : ZMod 3) : Z3.toAdd (Z3.ofAdd x) = x := rfl

theorem Z3.ofAdd_toAdd (x : Z3) : Z3.ofAdd (Z3.toAdd x) = x := rfl

theorem Z3.ofAdd_eq_ofAdd_iff {x y : ZMod 3} : Z3.ofAdd x = Z3.ofAdd y ↔ x = y :=
  ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]⟩

theorem Z3.ofAdd_eq_one {x : ZMod 3} : Z3.ofAdd x = 1 ↔ x = 0 :=
  ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]; rfl⟩

@[expose] def triPairing (b : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) : ZMod 3 :=
  ∑ j, b j * ((v j : ℤ) : ZMod 3)

theorem triPairing_add (b : Fin τ.rank → ZMod 3) (u v : Fin τ.rank → ℤ) :
    triPairing b (u + v) = triPairing b u + triPairing b v := by
  simp only [triPairing, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem triPairing_zero (b : Fin τ.rank → ZMod 3) : triPairing b 0 = 0 := by
  simp [triPairing]

theorem triPairing_zsmul_single (b : Fin τ.rank → ZMod 3) (c : ℤ) (k : Fin τ.rank) :
    triPairing b (c • (Pi.single k 1 : Fin τ.rank → ℤ)) = b k * (c : ZMod 3) := by
  rw [triPairing, Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

@[expose] def triChar (b : Fin τ.rank → ZMod 3) :
    Multiplicative (Fin τ.rank → ℤ) →* Z3 where
  toFun v := Z3.ofAdd (triPairing b (Multiplicative.toAdd v))
  map_one' := by simp [triPairing_zero, Z3.ofAdd_zero]
  map_mul' u v := by simp [triPairing_add, Z3.ofAdd_add]

theorem triChar_apply (b : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    triChar b (Multiplicative.ofAdd v) = Z3.ofAdd (triPairing b v) :=
  rfl

theorem eq_triChar (χ : Multiplicative (Fin τ.rank → ℤ) →* Z3) :
    χ = triChar fun j => Z3.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1))) := by
  refine lattice_hom_ext fun j => ?_
  rw [triChar_apply]
  have h := triPairing_zsmul_single
    (fun k => Z3.toAdd (χ (Multiplicative.ofAdd (Pi.single k 1)))) 1 j
  rw [one_smul] at h
  rw [h]
  simp [Z3.ofAdd_toAdd]

theorem mem_kernelRoots_triChar {b : Fin τ.rank → ZMod 3} {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots (triChar b) ↔ IsRoot τ α ∧ triPairing b α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [triChar_apply, Z3.ofAdd_eq_one]

@[expose] def triReflect (i : Fin τ.rank) (b : Fin τ.rank → ZMod 3) : Fin τ.rank → ZMod 3 :=
  fun j => b j - (τ.cartan i j : ZMod 3) * b i

@[expose] def charComp {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (w : WeylGroup τ) :
    Multiplicative (Fin τ.rank → ℤ) →* M :=
  χ.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom _ w))

theorem charComp_apply
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (w : WeylGroup τ)
    (v : Fin τ.rank → ℤ) :
    charComp χ w (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (w • v)) :=
  rfl

theorem triChar_triReflect
    (i : Fin τ.rank) (b : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    triChar (triReflect i b) (Multiplicative.ofAdd v) =
      triChar b (Multiplicative.ofAdd (simple τ i • v)) := by
  rw [← charComp_apply]
  refine congrArg (fun f => f (Multiplicative.ofAdd v)) (lattice_hom_ext
    (f := triChar (triReflect i b)) (g := charComp (triChar b) (simple τ i)) fun j => ?_)
  rw [charComp_apply, simple_smul, triChar_apply, triChar_apply]
  have hs : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  have hr : reflect τ i (Pi.single j 1) = (1 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) +
      (-τ.cartan i j) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [reflect, hs, one_smul, neg_smul, ← sub_eq_add_neg]
  have h1 : triPairing (triReflect i b) (Pi.single j 1) = triReflect i b j := by
    have := triPairing_zsmul_single (triReflect i b) 1 j
    rwa [one_smul, Int.cast_one, mul_one] at this
  rw [h1, hr, triPairing_add, triPairing_zsmul_single, triPairing_zsmul_single]
  congr 1
  simp only [triReflect, Int.cast_one, mul_one, Int.cast_neg]
  ring

@[expose] def triAct (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod 3) : Fin τ.rank → ZMod 3 :=
  ω.foldr triReflect b

theorem triChar_triAct
    (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    triChar (triAct ω b) (Multiplicative.ofAdd v) =
      triChar b (Multiplicative.ofAdd (((coxeterSystem τ).wordProd ω)⁻¹ • v)) := by
  induction ω generalizing v with
  | nil => simp [triAct]
  | cons i ω ih =>
    change triChar (triReflect i (triAct ω b)) (Multiplicative.ofAdd v) = _
    rw [triChar_triReflect, ih, CoxeterSystem.wordProd_cons, _root_.mul_inv_rev, mul_smul,
      (coxeterSystem τ).inv_simple]

@[expose] def vec3 (l : List ℕ) : Fin τ.rank → ZMod 3 :=
  fun j => ((l.getD j 0 : ℕ) : ZMod 3)

@[expose] def toFinWord3 (ω : List ℕ) : List (Fin τ.rank) :=
  ω.filterMap fun i => if h : i < τ.rank then some ⟨i, h⟩ else none

@[expose] def vec3OfIndex (n : ℕ) : Fin τ.rank → ZMod 3 :=
  fun j => ((n / 3 ^ (j : ℕ) % 3 : ℕ) : ZMod 3)

theorem exists_vec3OfIndex (b : Fin τ.rank → ZMod 3) :
    ∃ n < 3 ^ τ.rank, vec3OfIndex n = b := by
  let f : Fin τ.rank → Fin 3 := fun j => ⟨(b j).val, ZMod.val_lt (b j)⟩
  refine ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).2, ?_⟩
  funext j
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) j
  rw [Equiv.symm_apply_apply] at h
  simp only [vec3OfIndex]
  rw [← h]
  simp [f]

theorem getD_range_map' {α : Type*} (f : ℕ → α) (d : α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

@[expose] def digits3 (τ : Tag) (n : ℕ) : List ℕ :=
  (List.range τ.rank).map fun j => n / 3 ^ j % 3

@[expose] def negCartanRow (τ : Tag) (i : ℕ) : List ℕ :=
  (List.finRange τ.rank).map fun j =>
    if h : i < τ.rank then ((-(τ.cartan ⟨i, h⟩ j)) % 3).toNat else 0

@[expose] def negCartanRows (τ : Tag) : List (List ℕ) := (List.range τ.rank).map (negCartanRow τ)

@[expose] def reflAux (bi : ℕ) (b row : List ℕ) : List ℕ :=
  List.zipWith (fun bj cj => (bj + cj * bi) % 3) b row

@[expose] def reflL (rows : List (List ℕ)) (i : ℕ) (b : List ℕ) : List ℕ :=
  reflAux (b.getD i 0) b (rows.getD i [])

@[expose] def actL (rows : List (List ℕ)) (word : List ℕ) (b : List ℕ) : List ℕ :=
  word.foldr (reflL rows) b

theorem length_negCartanRow (τ : Tag) (i : ℕ) : (negCartanRow τ i).length = τ.rank := by
  simp [negCartanRow]

theorem negCartanRows_getD {i : ℕ} (hi : i < τ.rank) :
    (negCartanRows τ).getD i [] = negCartanRow τ i := getD_range_map' _ _ hi

theorem length_reflL {i : ℕ} (hi : i < τ.rank) {b : List ℕ} (hb : b.length = τ.rank) :
    (reflL (negCartanRows τ) i b).length = τ.rank := by
  rw [reflL, reflAux, List.length_zipWith, negCartanRows_getD hi, length_negCartanRow, hb,
    min_self]

theorem length_actL {word : List ℕ} (hw : ∀ i ∈ word, i < τ.rank) {b : List ℕ}
    (hb : b.length = τ.rank) : (actL (negCartanRows τ) word b).length = τ.rank := by
  induction word with
  | nil => simpa [actL] using hb
  | cons i w ih =>
    have hi : i < τ.rank := hw i (by simp)
    have := ih (fun k hk => hw k (by simp [hk]))
    simpa [actL] using length_reflL hi (by simpa [actL] using this)

theorem aux_ring {R : Type*} [CommRing R] (x A y : R) : x + -A * y = x - A * y := by ring

theorem zmod3_aux (A : ℤ) (x y : ℕ) :
    ((((x + ((-A) % 3).toNat * y) % 3 : ℕ)) : ZMod 3) = (x : ZMod 3) - (A : ZMod 3) * (y : ZMod 3) := by
  have hmod : (((-A) % 3 : ℤ) : ZMod 3) = -((A : ℤ) : ZMod 3) := by
    have := ZMod.intCast_mod (-A) 3
    rw [Int.cast_neg] at this
    exact this
  have key : ((((-A) % 3).toNat : ℕ) : ZMod 3) = -((A : ℤ) : ZMod 3) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)), hmod]
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, key]
  exact aux_ring (R := ZMod 3) _ _ _

theorem vec3_reflL (i : Fin τ.rank) {b : List ℕ} (hb : b.length = τ.rank) :
    vec3 (τ := τ) (reflL (negCartanRows τ) i b) = triReflect i (vec3 (τ := τ) b) := by
  funext j
  simp only [vec3, triReflect, reflL, reflAux, negCartanRows_getD i.2]
  have hj : (j : ℕ) < (negCartanRow τ i).length := by rw [length_negCartanRow]; exact j.2
  have hj' : (j : ℕ) < b.length := by rw [hb]; exact j.2
  rw [List.getD_eq_getElem _ _ (by simp [hj, hj']), List.getElem_zipWith,
    ← List.getD_eq_getElem _ 0 hj', ← List.getD_eq_getElem _ 0 hj]
  have hneg : (negCartanRow τ i).getD j 0 = ((-(τ.cartan i j)) % 3).toNat := by
    simp only [negCartanRow]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
    simp [i.2]
  rw [hneg]
  exact zmod3_aux (τ.cartan i j) _ _

theorem vec3_actL {word : List ℕ} (hw : ∀ i ∈ word, i < τ.rank) {b : List ℕ}
    (hb : b.length = τ.rank) :
    vec3 (τ := τ) (actL (negCartanRows τ) word b) = triAct (toFinWord3 word) (vec3 (τ := τ) b) := by
  induction word with
  | nil => simp [actL, toFinWord3, triAct]
  | cons i w ih =>
    have hi : i < τ.rank := hw i (by simp)
    have hw' : ∀ k ∈ w, k < τ.rank := fun k hk => hw k (by simp [hk])
    have h1 := ih hw'
    have hlen := length_actL hw' hb
    simp only [actL, List.foldr_cons] at *
    rw [vec3_reflL ⟨i, hi⟩ hlen, h1]
    simp [toFinWord3, hi, triAct]

theorem vec3_digits3 (n : ℕ) : vec3 (τ := τ) (digits3 τ n) = vec3OfIndex n := by
  funext j
  simp only [vec3, vec3OfIndex, digits3]
  rw [List.getD_eq_getElem _ _ (by simp [j.2])]
  simp

theorem length_digits3 (n : ℕ) : (digits3 τ n).length = τ.rank := by simp [digits3]

@[expose] def decodeWord9 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % 9 - 1) :: decodeWord9 fuel (n / 9)

@[expose] def entryRep (e : ℕ) : ℕ := e % 8

@[expose] def entryWord (e : ℕ) : List ℕ := decodeWord9 128 (e / 8)

@[expose] def orbitAux3 (τ : Tag) (rows : List (List ℕ)) (reps : List (List ℕ)) :
    ℕ → List ℕ → Bool
  | _, [] => true
  | n, e :: es =>
    (decide (entryRep e < reps.length) &&
      (entryWord e).all (fun i => decide (i < τ.rank)) &&
      (actL rows (entryWord e) (reps.getD (entryRep e) []) == digits3 τ n)) &&
      orbitAux3 τ rows reps (n + 1) es

@[expose] def orbitCheck3 (τ : Tag) (reps : List (List ℕ)) (entries : List ℕ) : Bool :=
  decide (entries.length = 3 ^ τ.rank) && reps.all (fun b => decide (b.length = τ.rank)) &&
    orbitAux3 τ (negCartanRows τ) reps 0 entries

theorem orbitAux3_spec {reps : List (List ℕ)} (hreps : ∀ b ∈ reps, b.length = τ.rank) :
    ∀ (es : List ℕ) (m : ℕ), orbitAux3 τ (negCartanRows τ) reps m es = true →
      ∀ k (hk : k < es.length), entryRep (es[k]) < reps.length ∧
        triAct (toFinWord3 (entryWord (es[k]))) (vec3 (τ := τ) (reps.getD (entryRep (es[k])) [])) =
          vec3OfIndex (m + k) := by
  intro es
  induction es with
  | nil => intro m _ k hk; exact absurd hk (by simp)
  | cons e es ih =>
    intro m h k hk
    simp only [orbitAux3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, hw⟩, h2⟩, h3⟩ := h
    cases k with
    | zero =>
      refine ⟨h1, ?_⟩
      have hb : (reps.getD (entryRep e) []).length = τ.rank := by
        rw [List.getD_eq_getElem _ _ h1]
        exact hreps _ (List.getElem_mem _)
      have := congrArg (vec3 (τ := τ)) h2
      rw [vec3_actL (fun i hi => by simpa using hw i hi) hb, vec3_digits3] at this
      simpa using this
    | succ k =>
      have := ih (m + 1) h3 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using this

theorem exists_word_of_orbitCheck3 {reps : List (List ℕ)} {entries : List ℕ}
    (h : orbitCheck3 τ reps entries = true) (b : Fin τ.rank → ZMod 3) :
    ∃ ρ < reps.length, ∃ ω : List ℕ, triAct (toFinWord3 ω) (vec3 (τ := τ) (reps.getD ρ [])) = b := by
  simp only [orbitCheck3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hreps⟩, hc⟩ := h
  obtain ⟨n, hn, rfl⟩ := exists_vec3OfIndex b
  have := orbitAux3_spec (fun b hb => by simpa using hreps b hb) entries 0 hc n (by omega)
  rw [Nat.zero_add] at this
  exact ⟨_, this.1, _, this.2⟩

theorem exists_isCharConj_of_orbitCheck3
    {reps : List (List ℕ)} {entries : List ℕ} (h : orbitCheck3 τ reps entries = true)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Z3) :
    ∃ ρ < reps.length, ∃ t : WeylGroup τ,
      IsCharConj (triChar (vec3 (τ := τ) (reps.getD ρ []))) χ t := by
  rw [eq_triChar χ]
  obtain ⟨ρ, hρ, ω, hω⟩ := exists_word_of_orbitCheck3 h
    (fun j => Z3.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1))))
  refine ⟨ρ, hρ, (coxeterSystem τ).wordProd (toFinWord3 ω), fun v => ?_⟩
  rw [← hω, triChar_triAct]

inductive KTree
  | nil : KTree
  | node : KTree → ℕ → KTree → KTree

namespace KTree

@[expose] def mem (x : ℕ) : KTree → Bool
  | nil => false
  | node l k r => if x < k then l.mem x else if k < x then r.mem x else true

@[expose] def toList : KTree → List ℕ
  | nil => []
  | node l k r => l.toList ++ k :: r.toList

theorem mem_toList {x : ℕ} : ∀ {t : KTree}, t.mem x = true → x ∈ t.toList
  | nil, h => by simp [mem] at h
  | node l k r, h => by
    by_cases h1 : x < k
    · simp only [mem, h1, ↓reduceIte] at h
      simp [toList, mem_toList h]
    · by_cases h2 : k < x
      · simp only [mem, h1, h2, ↓reduceIte] at h
        simp [toList, mem_toList h]
      · have : x = k := by omega
        simp [toList, this]

@[expose] def ofSortedAux : ℕ → List ℕ → KTree
  | 0, _ => nil
  | fuel + 1, l =>
    match l.drop (l.length / 2) with
    | [] => nil
    | k :: rest => node (ofSortedAux fuel (l.take (l.length / 2))) k (ofSortedAux fuel rest)

@[expose] def ofSorted (l : List ℕ) : KTree := ofSortedAux l.length l

theorem mem_of_mem_ofSortedAux {x : ℕ} :
    ∀ (fuel : ℕ) (l : List ℕ), (ofSortedAux fuel l).mem x = true → x ∈ l := by
  intro fuel
  induction fuel with
  | zero => intro l h; simp [ofSortedAux, mem] at h
  | succ fuel ih =>
    intro l h
    simp only [ofSortedAux] at h
    split at h
    · simp [mem] at h
    · rename_i k rest hk
      by_cases h1 : x < k
      · simp only [mem, h1, ↓reduceIte] at h
        exact List.mem_of_mem_take (ih _ h)
      · by_cases h2 : k < x
        · simp only [mem, h1, h2, ↓reduceIte] at h
          have := ih _ h
          exact List.mem_of_mem_drop (by rw [hk]; exact List.mem_cons_of_mem _ this)
        · have : x = k := by omega
          subst this
          exact List.mem_of_mem_drop (by rw [hk]; exact List.mem_cons_self)

theorem mem_of_mem_ofSorted {x : ℕ} {l : List ℕ} (h : (ofSorted l).mem x = true) : x ∈ l :=
  mem_of_mem_ofSortedAux _ _ h

end KTree

@[expose] def decodeT (r : ℕ) (k : ℕ) : List ℕ := (List.range r).map fun j => k / 256 ^ j % 256

@[expose] def encodeT (t : List ℕ) : ℕ := t.foldr (fun x acc => x + 256 * acc) 0

open RootCertificate

theorem height_sum_smul {n : ℕ} (c : Fin n → ℤ) (v : Fin n → (Fin τ.rank → ℤ)) :
    height (∑ j, c j • v j) = ∑ j, c j * height (v j) := by
  simp only [height, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

structure RootTables where
  vecs : List (List ℤ)
  hts : List ℤ
  imgs : List (List ℕ)

@[expose] def RootTables.ofCert (C : RootCertificate τ) : RootTables where
  vecs := (List.range C.roots.length).map fun k => List.ofFn (C.root k)
  hts := (List.range C.roots.length).map fun k => height (C.root k)
  imgs := (List.range τ.rank).map fun i =>
    (List.range C.roots.length).map fun k => C.table.getD k 0 / 256 ^ i % 256

@[expose] def dotL (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).sum

@[expose] def imgL (T : RootTables) (i : ℕ) (t : List ℕ) : List ℕ :=
  t.map fun k => (T.imgs.getD i []).getD k 0

@[expose] def hsL (T : RootTables) (t : List ℕ) : List ℤ := t.map fun k => T.hts.getD k 0

@[expose] def dTestL (Δv : List (List ℤ)) (hs : List ℤ) : Bool :=
  Δv.all fun bv => decide (0 < dotL bv hs)

theorem sum_zipWith_ofFn_left : ∀ {n : ℕ} (f : Fin n → ℤ) (b : List ℤ),
    (List.zipWith (· * ·) (List.ofFn f) b).sum = ∑ j : Fin n, f j * b.getD j 0
  | 0, f, b => by simp
  | n + 1, f, b => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases b with
    | nil =>
      simp only [List.zipWith_nil_right, List.sum_nil, List.getD_nil, mul_zero, Finset.sum_const_zero,
        add_zero]
    | cons y b' =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [sum_zipWith_ofFn_left (fun j => f j.succ) b']
      simp [Fin.val_succ]

theorem getD_map_natCast (l : List ℕ) (x : ℕ) :
    (l.map fun y : ℕ => (y : ℤ)).getD x 0 = ((l.getD x 0 : ℕ) : ℤ) := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    cases x with
    | zero => rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
    | succ x => rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]; exact ih x

section Tables

variable (C : RootCertificate τ)

theorem vecs_getD {β : ℕ} (hβ : β < C.roots.length) :
    (RootTables.ofCert C).vecs.getD β [] = List.ofFn (C.root β) :=
  getD_range_map' _ _ hβ

theorem hts_getD {k : ℕ} (hk : k < C.roots.length) :
    (RootTables.ofCert C).hts.getD k 0 = height (C.root k) :=
  getD_range_map' _ _ hk

theorem imgs_getD {i : ℕ} (hi : i < τ.rank) {k : ℕ} (hk : k < C.roots.length) :
    ((RootTables.ofCert C).imgs.getD i []).getD k 0 = C.image k ⟨i, hi⟩ := by
  have h1 : (RootTables.ofCert C).imgs.getD i [] =
      (List.range C.roots.length).map fun k => C.table.getD k 0 / 256 ^ i % 256 :=
    getD_range_map' (fun i => (List.range C.roots.length).map fun k => C.table.getD k 0 / 256 ^ i % 256)
      [] hi
  rw [h1, getD_range_map' _ _ hk]
  rfl

theorem imgL_eq {i : ℕ} (hi : i < τ.rank) {t : List ℕ} (ht : ∀ k ∈ t, k < C.roots.length) :
    imgL (RootTables.ofCert C) i t = C.tupleImage ⟨i, hi⟩ t := by
  unfold imgL tupleImage
  exact List.map_congr_left fun k hk => imgs_getD C hi (ht k hk)

theorem dotL_eq_height {t : List ℕ} {w : WeylGroup τ} (h : C.Represents t w) {β : ℕ}
    (hβ : β < C.roots.length) :
    dotL ((RootTables.ofCert C).vecs.getD β []) (hsL (RootTables.ofCert C) t) =
      height (w • C.root β) := by
  rw [vecs_getD C hβ, dotL, sum_zipWith_ofFn_left, ← tupleVec_eq h, tupleVec, height_sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hj : (j : ℕ) < t.length := by rw [h.1]; exact j.2
  rw [hsL, List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hj]
  exact hts_getD C (h.2 j).1

end Tables

@[expose] def chiTestL (τ : Tag) (T : RootTables) (vec : List ℕ) (t : List ℕ) : Bool :=
  (List.range τ.rank).all fun j =>
    decide ((dotL (T.vecs.getD (t.getD j 0) []) (vec.map fun x : ℕ => (x : ℤ)) -
      ((vec.getD j 0 : ℕ) : ℤ)) % 3 = 0)

structure StabCert3 where
  vec : List ℕ
  simple : List ℕ
  keys : List ℕ

namespace StabCert3

variable
  (C : RootCertificate τ) (S : StabCert3)

@[expose] def elems (τ : Tag) (S : StabCert3) : List (List ℕ) :=
  S.keys.map (decodeT τ.rank)

@[expose] def passingWith (τ : Tag) (T : RootTables) : List (List ℕ) :=
  (S.elems τ).filter (chiTestL τ T S.vec)

@[expose] def passing : List (List ℕ) :=
  S.passingWith τ (RootTables.ofCert C)

@[expose] def stepAux (τ : Tag) (T : RootTables) (Δv : List (List ℤ)) (tree : KTree) (img : List ℕ) : Bool :=
  !(dTestL Δv (hsL T img)) ||
    (decide (decodeT τ.rank (encodeT img) = img) && tree.mem (encodeT img))

@[expose] def checkWith (T : RootTables) (Δv : List (List ℤ)) (tree : KTree) : Bool :=
  tree.mem (encodeT (List.range τ.rank)) &&
  decide (decodeT τ.rank (encodeT (List.range τ.rank)) = List.range τ.rank) &&
  S.simple.all (fun β => decide (β < C.roots.length) && decide (0 < height (C.root β)) &&
    decide (triPairing (vec3 (τ := τ) S.vec) (C.root β) = 0)) &&
  S.keys.all fun k => (List.range τ.rank).all fun i =>
    stepAux τ T Δv tree (imgL T i (decodeT τ.rank k))

@[expose] def check : Bool :=
  S.checkWith C (RootTables.ofCert C) (S.simple.map fun β => (RootTables.ofCert C).vecs.getD β [])
    (KTree.ofSorted S.keys)

variable {C S}

theorem mem_elems {t : List ℕ} :
    t ∈ S.elems τ ↔ ∃ k ∈ S.keys, decodeT τ.rank k = t := by
  simp [elems]

theorem exists_represents_of_check
    (hC : C.check = true) (hS : S.check C = true)
    (w : WeylGroup τ) (hw : ∀ β ∈ S.simple, 0 < height (w • C.root β)) :
    ∃ t ∈ S.elems τ, C.Represents t w := by
  simp only [check, checkWith, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨hid, hdec⟩, hsimple⟩, hclosed⟩ := hS
  have hid' : List.range τ.rank ∈ S.elems τ :=
    mem_elems.2 ⟨_, KTree.mem_of_mem_ofSorted hid, hdec⟩
  suffices key : ∀ n : ℕ, ∀ w : WeylGroup τ, (coxeterSystem τ).length w = n →
      (∀ β ∈ S.simple, 0 < height (w • C.root β)) → ∃ t ∈ S.elems τ, C.Represents t w from
    key _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw
    by_cases h1 : w = 1
    · subst h1
      exact ⟨_, hid', represents_one hC⟩
    obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_leftDescent_of_ne_one h1
    have hlen : (coxeterSystem τ).length (CFSG.LieType.Chevalley.simple τ i * w) < n := by
      rw [← hn]
      exact hi
    have hneg : w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) ≤ 0 := by
      have := (CFSG.LieType.RootSystem.isRightDescent_iff (isFiniteType_cartan τ) w⁻¹ i).1
        ((coxeterSystem τ).isRightDescent_inv_iff.2 hi)
      exact this
    have hw' : ∀ β ∈ S.simple, 0 < height ((CFSG.LieType.Chevalley.simple τ i * w) • C.root β) := by
      intro β hβ
      have hβ' := hsimple β hβ
      have hr : IsRoot τ (C.root β) := RootCertificate.isRoot_root hC β hβ'.1.1
      have hr' : IsRoot τ (w • C.root β) := IsRoot.smul hr w
      have hne : w • C.root β ≠ Pi.single i 1 := by
        intro e
        have : C.root β = w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [← e, inv_smul_smul]
        have hpos := hβ'.1.2
        rw [this] at hpos
        have : height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) ≤ 0 :=
          Finset.sum_nonpos fun j _ => hneg j
        omega
      rw [mul_smul, simple_smul]
      exact height_reflect_pos hr' (hw β hβ) hne
    obtain ⟨t, ht, hrep⟩ := ih _ hlen _ rfl hw'
    have hrep' := represents_tupleImage hC hrep i
    rw [← mul_assoc, (coxeterSystem τ).simple_mul_simple_self, one_mul] at hrep'
    obtain ⟨k, hk, rfl⟩ := mem_elems.1 ht
    have hvalid : ∀ x ∈ decodeT τ.rank k, x < C.roots.length := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem.1 hx
      have hjlt : j < τ.rank := by
        have := hj.1
        simpa [hrep.1] using this
      have := (hrep.2 ⟨j, hjlt⟩).1
      rw [List.getD_eq_getElem _ _ hj.1] at this
      rw [← hj.2]
      exact this
    have himg := imgL_eq C i.2 hvalid
    have hstep := hclosed k hk i (by simp [i.2])
    rw [himg] at hstep
    unfold stepAux at hstep
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at hstep
    have hd : dTestL (S.simple.map fun β => (RootTables.ofCert C).vecs.getD β [])
        (hsL (RootTables.ofCert C) (C.tupleImage i (decodeT τ.rank k))) = true := by
      simp only [dTestL, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        decide_eq_true_eq]
      rintro bv β hβ rfl
      have hβ' := hsimple β hβ
      rw [dotL_eq_height C hrep' hβ'.1.1]
      exact hw β hβ
    rcases hstep with h | ⟨h1, h2⟩
    · rw [hd] at h
      exact absurd h (by decide)
    · exact ⟨_, mem_elems.2 ⟨_, KTree.mem_of_mem_ofSorted h2, h1⟩, hrep'⟩

theorem simple_mem_posRoots (hC : C.check = true) (hS : S.check C = true) {β : ℕ}
    (hβ : β ∈ S.simple) :
    C.root β ∈ posRoots (kernelRoots (triChar (vec3 (τ := τ) S.vec))) := by
  simp only [check, checkWith, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨-, -⟩, hsimple⟩, -⟩ := hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hsimple β hβ
  exact ⟨mem_kernelRoots_triChar.2 ⟨RootCertificate.isRoot_root hC β h1, h3⟩, h2⟩

theorem chiTestL_of_pairing {t : List ℕ} {w : WeylGroup τ} (hrep : C.Represents t w)
    (h : ∀ j : Fin τ.rank,
      triPairing (vec3 (τ := τ) S.vec) (C.root (t.getD j 0)) = vec3 (τ := τ) S.vec j) :
    chiTestL τ (RootTables.ofCert C) S.vec t = true := by
  simp only [chiTestL, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro j hj
  have hk := (hrep.2 ⟨j, hj⟩).1
  rw [vecs_getD C hk, dotL, sum_zipWith_ofFn_left]
  have hpair := h ⟨j, hj⟩
  simp only [triPairing, vec3] at hpair
  apply Int.emod_eq_zero_of_dvd
  have hgd : ∀ x : Fin τ.rank, (S.vec.map fun y : ℕ => (y : ℤ)).getD x 0 = ((S.vec.getD x 0 : ℕ) : ℤ) :=
    fun x => getD_map_natCast S.vec x
  simp only [hgd]
  have hcast : ((((∑ x : Fin τ.rank, C.root (t.getD j 0) x * ((S.vec.getD x 0 : ℕ) : ℤ)) -
      ((S.vec.getD j 0 : ℕ) : ℤ) : ℤ)) : ZMod 3) = 0 := by
    rw [Int.cast_sub, sub_eq_zero, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [← hpair]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hcast

theorem exists_passing_of_mem (hC : C.check = true) (hS : S.check C = true) {ω : WeylGroup τ}
    (hω : ω ∈ kernelPosStabilizer (triChar (vec3 (τ := τ) S.vec))) :
    ∃ t ∈ S.passing C, C.Represents t ω := by
  obtain ⟨hχ, himg⟩ := hω
  have hpos : ∀ β ∈ S.simple, 0 < height (ω • C.root β) := by
    intro β hβ
    have h := simple_mem_posRoots hC hS hβ
    have : ω • C.root β ∈ posRoots (kernelRoots (triChar (vec3 (τ := τ) S.vec))) := by
      rw [← himg]
      exact ⟨_, h, rfl⟩
    exact this.2
  obtain ⟨t, ht, hrep⟩ := exists_represents_of_check hC hS ω hpos
  refine ⟨t, List.mem_filter.2 ⟨ht, chiTestL_of_pairing hrep fun j => ?_⟩, hrep⟩
  rw [(hrep.2 j).2]
  have h := hχ (Pi.single j 1)
  rw [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff] at h
  have hpair : triPairing (vec3 (τ := τ) S.vec) (Pi.single j 1) = vec3 (τ := τ) S.vec j := by
    have := triPairing_zsmul_single (vec3 (τ := τ) S.vec) 1 j
    rwa [one_smul, Int.cast_one, mul_one] at this
  rw [hpair] at h
  exact h

theorem card_kernelPosStabilizer_le (hC : C.check = true) (hS : S.check C = true) :
    Nat.card (kernelPosStabilizer (triChar (vec3 (τ := τ) S.vec))) ≤ (S.passing C).length := by
  classical
  have key : ∀ ω : kernelPosStabilizer (triChar (vec3 (τ := τ) S.vec)),
      ∃ t ∈ (S.passing C).toFinset, C.Represents t ω := fun ω => by
    obtain ⟨t, ht, hrep⟩ := exists_passing_of_mem hC hS ω.2
    exact ⟨t, List.mem_toFinset.2 ht, hrep⟩
  choose f hf hrep using key
  have hinj : Function.Injective fun ω => (⟨f ω, hf ω⟩ : (S.passing C).toFinset) := by
    intro ω ω' h
    have h' : f ω = f ω' := congrArg Subtype.val h
    exact Subtype.ext (represents_unique (hrep ω) (h' ▸ hrep ω'))
  calc Nat.card (kernelPosStabilizer (triChar (vec3 (τ := τ) S.vec)))
      ≤ Nat.card (S.passing C).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (S.passing C).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (S.passing C).length := List.toFinset_card_le _

end StabCert3

end CFSG.HardMathSupport.Timmesfeld.Steinberg
