module

public import CFSG.Timmesfeld.Orders.ExceptionalWeyl
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeSplit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld.ExceptionalOrders CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Timmesfeld.Co1Leaf
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

set_option linter.unusedSectionVars false

namespace Native

@[expose] def dotZ (x y : List ℤ) : ℤ := ((x.zip y).map fun p => p.1 * p.2).sum

@[expose] def dotN (b : List ℕ) (v : List ℤ) : ℤ := ((b.zip v).map fun p => (p.1 : ℤ) * p.2).sum

@[expose] def fibL (kb : List (List ℕ)) (v : List ℤ) : List ℤ := kb.map fun b => dotN b v % 3

@[expose] def gramL (τ : Tag) : List (List ℤ) :=
  (List.finRange τ.rank).map fun i => (List.finRange τ.rank).map fun j => τ.symmetrizedCartan i j

@[expose] def formB (B : List (List ℤ)) (u v : List ℤ) : ℤ :=
  ((B.zip u).map fun p => p.2 * dotZ p.1 v).sum

@[expose] def simpleL (τ : Tag) : List (List ℤ) :=
  (List.finRange τ.rank).map fun i => List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)

@[expose] def rootsN (τ : Tag) : List (List ℤ × ℤ) :=
  (rootList τ).map fun β => (List.ofFn β, iform β β)

@[expose] def fibRoots (RN : List (List ℤ × ℤ)) (kb : List (List ℕ)) :
    List (List ℤ × ℤ × List ℤ) :=
  RN.map fun p => (p.1, p.2, fibL kb p.1)

@[expose] def kerRootsL (FR : List (List ℤ × ℤ × List ℤ)) (z : List ℤ) : List (List ℤ) :=
  (FR.filter fun p => p.2.2 == z).map Prod.fst

@[expose] def candL (FR : List (List ℤ × ℤ × List ℤ)) (fe : List ℤ) (ne : ℤ) : List (List ℤ) :=
  (FR.filter fun p => p.2.1 == ne && p.2.2 == fe).map Prod.fst

@[expose] def tuplesL (B : List (List ℤ)) (FR : List (List ℤ × ℤ × List ℤ)) (E : List (List ℤ))
    (FE : List (List ℤ)) (NE : List ℤ) : List (List (List ℤ)) :=
  (List.range E.length).foldl (fun acc i => acc.flatMap fun t =>
    ((candL FR (FE.getD i []) (NE.getD i 0)).filter fun β =>
      (List.range i).all fun j =>
        formB B (t.getD j []) β == formB B (E.getD j []) (E.getD i [])).map
          fun β => t ++ [β]) [[]]

@[expose] def reflB (B : List (List ℤ)) (α v : List ℤ) : List ℤ :=
  (v.zip α).map fun p => p.1 - 2 * formB B α v / formB B α α * p.2

@[expose] def famOK (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (kb : List (List ℕ)) : Bool :=
  let FR := fibRoots RN kb
  let T := tuplesL B FR E (E.map (fibL kb)) NE
  match kerRootsL FR (kb.map fun _ => 0) with
  | [] => T.all (· == E)
  | [α, β] => β == α.map (- ·) && T.all fun t => t == E || t == E.map (reflB B α)
  | _ => false

@[expose] def famOK0 (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (kb : List (List ℕ)) : Bool :=
  let FR := fibRoots RN kb
  (kerRootsL FR (kb.map fun _ => 0)).isEmpty && (tuplesL B FR E (E.map (fibL kb)) NE).all (· == E)

@[expose] def stdBasis (r : ℕ) : List (List ℕ) :=
  (List.range r).map fun i => (List.range r).map fun j => if j = i then 1 else 0

@[expose] def hypOK (τ : Tag) : Bool :=
  let B := gramL τ
  let RN := rootsN τ
  let E := simpleL τ
  let NE := E.map fun e => formB B e e
  (normVecs 3 τ.rank).all (fun fl => famOK B RN E NE (kerBasis 3 fl)) &&
    famOK0 B RN E NE (stdBasis τ.rank)

@[expose] def kerNonemptyOK (τ : Tag) : Bool :=
  let R := (rootList τ).map List.ofFn
  (expVecs 3 τ.rank).all fun x => x.all (· == 0) || R.any fun β => dotN x β % 3 == 0

end Native

section Lists

open Native

variable {τ : Tag}

theorem zip_ofFn {n : ℕ} {α β : Type*} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun i => (f i, g i) := by
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp

theorem dotZ_ofFn {n : ℕ} (x y : Fin n → ℤ) :
    dotZ (List.ofFn x) (List.ofFn y) = ∑ i, x i * y i := by
  rw [dotZ, zip_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

theorem ofFn_getD_eq {n : ℕ} {b : List ℕ} (hb : b.length = n) :
    List.ofFn (fun i : Fin n => b.getD i 0) = b := by
  refine List.ext_getElem (by simp [hb]) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

theorem dotN_ofFn {n : ℕ} {b : List ℕ} (hb : b.length = n) (v : Fin n → ℤ) :
    dotN b (List.ofFn v) = ∑ i : Fin n, (b.getD i.val 0 : ℤ) * v i := by
  conv_lhs => rw [← ofFn_getD_eq hb]
  rw [dotN, zip_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

theorem formB_gramL (u v : Fin τ.rank → ℤ) :
    formB (gramL τ) (List.ofFn u) (List.ofFn v) = iform u v := by
  rw [formB, gramL, ← List.ofFn_eq_map, zip_ofFn, List.map_ofFn, List.sum_ofFn, iform]
  refine Finset.sum_congr rfl fun i _ => ?_
  change u i * dotZ ((List.finRange τ.rank).map fun j => τ.symmetrizedCartan i j) (List.ofFn v) = _
  rw [← List.ofFn_eq_map, dotZ_ofFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem simpleL_eq (τ : Tag) :
    simpleL τ = List.ofFn fun i => List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ) := by
  rw [simpleL, List.ofFn_eq_map]

theorem length_simpleL (τ : Tag) : (simpleL τ).length = τ.rank := by
  simp [simpleL]

theorem getD_simpleL {τ : Tag} (i : Fin τ.rank) :
    (simpleL τ).getD i [] = List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ) := by
  rw [simpleL_eq, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem mem_rootsN {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (List.ofFn β, iform β β) ∈ rootsN τ :=
  List.mem_map.2 ⟨β, mem_rootList.2 hβ, rfl⟩

theorem isRoot_of_mem_rootsN {p : List ℤ × ℤ} (hp : p ∈ rootsN τ) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ p = (List.ofFn β, iform β β) := by
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hp
  exact ⟨β, mem_rootList.1 hβ, rfl⟩

end Lists

section Characters

open Native

variable {τ : Tag}

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]

variable {K : Type} [Field K]

@[expose] def torV (ω : Kˣ) (x : Fin τ.rank → ZMod 3) : Fin τ.rank → Kˣ :=
  fun i => ω ^ (x i).val

theorem rootChar_torV (ω : Kˣ) (x : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    rootChar (torV ω x) v = ω ^ (∑ i, ((x i).val : ℤ) * v i) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [torV, ← zpow_natCast, ← zpow_mul]

theorem val_listVec {b : List ℕ} (hb : ∀ x ∈ b, x < 3) (i : Fin τ.rank) :
    ((listVec τ.rank b i).val : ℤ) = b.getD i 0 := by
  have hlt : b.getD i 0 < 3 := by
    by_cases hi : i.val < b.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hb _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  rw [listVec, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

@[expose] def famV (ω : Kˣ) (kb : List (List ℕ)) : Fin kb.length → Fin τ.rank → Kˣ :=
  fun j => torV ω (listVec τ.rank (kb.get j))

variable {ω : Kˣ} {kb : List (List ℕ)}

theorem rootChar_famV (hlen : ∀ b ∈ kb, b.length = τ.rank) (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3)
    (j : Fin kb.length) (v : Fin τ.rank → ℤ) :
    rootChar (famV ω kb j) v = ω ^ dotN (kb.get j) (List.ofFn v) := by
  rw [famV, rootChar_torV, dotN_ofFn (hlen _ (List.get_mem kb j))]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [val_listVec (hlt _ (List.get_mem kb j))]

theorem fibL_eq_iff {u v : Fin τ.rank → ℤ} :
    fibL kb (List.ofFn u) = fibL kb (List.ofFn v) ↔
      ∀ j : Fin kb.length,
        dotN (kb.get j) (List.ofFn u) % 3 = dotN (kb.get j) (List.ofFn v) % 3 := by
  rw [fibL, fibL, List.map_inj_left]
  constructor
  · intro h j
    exact h _ (List.get_mem kb j)
  · intro h b hb
    obtain ⟨j, rfl⟩ := List.get_of_mem hb
    exact h j

theorem mem_familyKernel_famV (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3) {α : Fin τ.rank → ℤ} :
    α ∈ familyKernel (famV ω kb) ↔ IsRoot τ α ∧ fibL kb (List.ofFn α) = kb.map fun _ => 0 := by
  rw [familyKernel, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  rw [fibL, List.map_inj_left]
  constructor
  · intro h b hb
    obtain ⟨j, rfl⟩ := List.get_of_mem hb
    have h1 := h j
    rw [rootChar_famV hlen hlt, ← orderOf_dvd_iff_zpow_eq_one, hω] at h1
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast h1)
  · intro h j
    rw [rootChar_famV hlen hlt, ← orderOf_dvd_iff_zpow_eq_one, hω]
    exact_mod_cast Int.dvd_of_emod_eq_zero (h _ (List.get_mem kb j))

theorem fibL_smul_of_mem_familyStabilizer (hω : orderOf ω = 3)
    (hlen : ∀ b ∈ kb, b.length = τ.rank) (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3) {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer (famV (τ := τ) ω kb)) (v : Fin τ.rank → ℤ) :
    fibL kb (List.ofFn (w • v)) = fibL kb (List.ofFn v) := by
  rw [fibL_eq_iff]
  intro j
  have h1 : rootChar (famV ω kb j) (w • v) = rootChar (famV ω kb j) v := hw j v
  rw [rootChar_famV hlen hlt, rootChar_famV hlen hlt, zpow_eq_zpow_iff_modEq, hω] at h1
  exact h1

end Characters

section Search

open Native

variable {τ : Tag}

theorem getD_take_of_lt {T : List (List ℤ)} {n i : ℕ} (h : i < n) :
    (T.take n).getD i [] = T.getD i [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

theorem mem_foldl_extend {C : ℕ → List (List ℤ)} {P : ℕ → List (List ℤ) → List ℤ → Bool} :
    ∀ (n : ℕ) (T : List (List ℤ)), T.length = n →
      (∀ i < n, T.getD i [] ∈ C i ∧ P i (T.take i) (T.getD i []) = true) →
      T ∈ (List.range n).foldl (fun acc i => acc.flatMap fun t =>
        ((C i).filter (P i t)).map fun β => t ++ [β]) [[]]
  | 0, T, hT, _ => by
    rw [List.length_eq_zero_iff.1 hT]
    simp
  | n + 1, T, hT, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.mem_flatMap]
    refine ⟨T.take n, mem_foldl_extend n _ (by simp [hT]) fun i hi => ?_, ?_⟩
    · have hi' := h i (by omega)
      rw [getD_take_of_lt hi, List.take_take, Nat.min_eq_left hi.le]
      exact hi'
    · rw [List.mem_map]
      have hn := h n (by omega)
      refine ⟨T.getD n [], List.mem_filter.2 ⟨hn.1, hn.2⟩, ?_⟩
      have hd : T.drop n = [T.getD n []] := by
        have hl : (T.drop n).length = 1 := by simp [hT]
        obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
        rw [hx]
        have h0 : (T.drop n).getD 0 [] = x := by rw [hx]; rfl
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero,
          ← List.getD_eq_getElem?_getD] at h0
        rw [h0]
      calc T.take n ++ [T.getD n []] = T.take n ++ T.drop n := by rw [hd]
        _ = T := List.take_append_drop n T


@[expose] noncomputable def imgTuple (w : WeylGroup τ) : List (List ℤ) :=
  List.ofFn fun i : Fin τ.rank => List.ofFn (w • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem getD_imgTuple (w : WeylGroup τ) (i : Fin τ.rank) :
    (imgTuple w).getD i [] = List.ofFn (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rw [imgTuple, List.getD_eq_getElem _ _ (by simp)]
  simp

variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

theorem imgTuple_mem_tuplesL (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3) {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer (famV (τ := τ) ω kb)) :
    imgTuple w ∈ tuplesL (gramL τ) (fibRoots (rootsN τ) kb) (simpleL τ)
      ((simpleL τ).map (fibL kb)) ((simpleL τ).map fun e => formB (gramL τ) e e) := by
  rw [tuplesL, length_simpleL]
  refine mem_foldl_extend τ.rank (imgTuple w) (by simp [imgTuple]) fun i hi => ⟨?_, ?_⟩
  · set i' : Fin τ.rank := ⟨i, hi⟩
    have hgi : (imgTuple w).getD i [] = List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) :=
      getD_imgTuple w i'
    rw [hgi, candL, List.mem_map]
    have hroot : IsRoot τ (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) :=
      IsRoot.smul (isRoot_single τ i') w
    refine ⟨(List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)),
      iform (w • (Pi.single i' 1 : Fin τ.rank → ℤ)) (w • (Pi.single i' 1 : Fin τ.rank → ℤ)),
      fibL kb (List.ofFn (w • (Pi.single i' 1 : Fin τ.rank → ℤ)))), List.mem_filter.2 ⟨?_, ?_⟩,
      rfl⟩
    · rw [fibRoots, List.mem_map]
      exact ⟨_, mem_rootsN hroot, rfl⟩
    · have hE : (simpleL τ).getD i [] = List.ofFn (Pi.single i' 1 : Fin τ.rank → ℤ) :=
        getD_simpleL i'
      have h1 : ((simpleL τ).map fun e => formB (gramL τ) e e).getD i 0 =
          formB (gramL τ) ((simpleL τ).getD i []) ((simpleL τ).getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      have h2 : ((simpleL τ).map (fibL kb)).getD i [] = fibL kb ((simpleL τ).getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      rw [h1, h2, hE, formB_gramL, iform_smul, fibL_smul_of_mem_familyStabilizer hω hlen hlt hw]
      simp
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    set i' : Fin τ.rank := ⟨i, hi⟩
    set j' : Fin τ.rank := ⟨j, by omega⟩
    rw [getD_take_of_lt hj, getD_imgTuple w j', getD_imgTuple w i', getD_simpleL j',
      getD_simpleL i', formB_gramL, formB_gramL, iform_smul]
    simp

end Search

section Data

open Native

variable {τ : Tag}
  {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

theorem reflB_ofFn {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (v : Fin τ.rank → ℤ) :
    reflB (gramL τ) (List.ofFn α) (List.ofFn v) = List.ofFn (rootReflection α • v) := by
  rw [reflB, zip_ofFn, List.map_ofFn, formB_gramL, formB_gramL, rootReflection_smul hα]
  rfl

theorem eq_of_imgTuple_eq {w w' : WeylGroup τ} (h : imgTuple w = imgTuple w') : w = w' := by
  refine ext_single fun i => ?_
  have h1 := congrArg (fun T => T.getD i []) h
  simp only [getD_imgTuple] at h1
  exact List.ofFn_injective h1

theorem imgTuple_one : imgTuple (1 : WeylGroup τ) = simpleL τ := by
  rw [imgTuple, simpleL_eq]
  simp

theorem imgTuple_rootReflection {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    imgTuple (rootReflection α) = (simpleL τ).map (reflB (gramL τ) (List.ofFn α)) := by
  rw [imgTuple, simpleL_eq, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [reflB_ofFn hα]

theorem famData_of_famOK (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3)
    (h : famOK (gramL τ) (rootsN τ) (simpleL τ) ((simpleL τ).map fun e => formB (gramL τ) e e)
      kb = true) :
    (familyKernel (famV (τ := τ) ω kb) = ∅ ∧ ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α := by
  have hT := fun {w : WeylGroup τ} (hw : w ∈ familyStabilizer (famV (τ := τ) ω kb)) =>
    imgTuple_mem_tuplesL hω hlen hlt hw
  have hker : ∀ γ : Fin τ.rank → ℤ, γ ∈ familyKernel (famV (τ := τ) ω kb) ↔
      List.ofFn γ ∈ kerRootsL (fibRoots (rootsN τ) kb) (kb.map fun _ => 0) ∧ IsRoot τ γ := by
    intro γ
    rw [mem_familyKernel_famV hω hlen hlt, kerRootsL, List.mem_map]
    constructor
    · rintro ⟨hγ, hf⟩
      refine ⟨⟨(List.ofFn γ, iform γ γ, fibL kb (List.ofFn γ)),
        List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩, hγ⟩
      · rw [fibRoots, List.mem_map]
        exact ⟨_, mem_rootsN hγ, rfl⟩
      · simpa using hf
    · rintro ⟨⟨p, hp, hpγ⟩, hγ⟩
      rw [List.mem_filter, fibRoots, List.mem_map] at hp
      obtain ⟨⟨q, hq, rfl⟩, hz⟩ := hp
      refine ⟨hγ, ?_⟩
      simp only at hpγ hz
      rw [← hpγ]
      simpa using hz
  have hkerRoot : ∀ x ∈ kerRootsL (fibRoots (rootsN τ) kb) (kb.map fun _ => 0),
      ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ x = List.ofFn γ := by
    intro x hx
    rw [kerRootsL, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [List.mem_filter, fibRoots, List.mem_map] at hp
    obtain ⟨⟨q, hq, rfl⟩, -⟩ := hp
    obtain ⟨γ, hγ, rfl⟩ := isRoot_of_mem_rootsN hq
    exact ⟨γ, hγ, rfl⟩
  unfold famOK at h
  simp only at h
  split at h
  · rename_i hK
    left
    refine ⟨Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_, fun w hw => ?_⟩
    · have := ((hker γ).1 hγ).1
      rw [hK] at this
      exact List.not_mem_nil this
    · rw [List.all_eq_true] at h
      have h1 := h _ (hT hw)
      rw [beq_iff_eq] at h1
      exact eq_of_imgTuple_eq (h1.trans imgTuple_one.symm)
  · rename_i α' β' hK
    rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hβ, hall⟩ := h
    obtain ⟨α, hα, rfl⟩ := hkerRoot α' (by rw [hK]; exact List.mem_cons_self)
    have hβ' : β' = List.ofFn (-α) := by
      rw [hβ, List.map_ofFn]
      rfl
    right
    refine ⟨α, hα, Set.ext fun γ => ?_, fun w hw => ?_⟩
    · rw [hker γ, hK, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_cons,
        hβ']
      constructor
      · rintro ⟨h1 | h1 | h1, -⟩
        · exact Or.inl (List.ofFn_injective h1)
        · exact Or.inr (List.ofFn_injective h1)
        · exact absurd h1 List.not_mem_nil
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hα⟩
        · exact ⟨Or.inr (Or.inl rfl), IsRoot.neg hα⟩
    · have h1 := hall _ (hT hw)
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (eq_of_imgTuple_eq (h1.trans imgTuple_one.symm))
      · exact Or.inr (eq_of_imgTuple_eq (h1.trans (imgTuple_rootReflection hα).symm))
  · exact absurd h (by simp)

theorem famData0_of_famOK0 (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = τ.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3)
    (h : famOK0 (gramL τ) (rootsN τ) (simpleL τ) ((simpleL τ).map fun e => formB (gramL τ) e e)
      kb = true) :
    familyKernel (famV (τ := τ) ω kb) = ∅ ∧ ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 := by
  unfold famOK0 at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hK, hall⟩ := h
  refine ⟨Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_, fun w hw => ?_⟩
  · rw [mem_familyKernel_famV hω hlen hlt] at hγ
    have hmem : List.ofFn γ ∈ kerRootsL (fibRoots (rootsN τ) kb) (kb.map fun _ => 0) := by
      rw [kerRootsL, List.mem_map]
      refine ⟨(List.ofFn γ, iform γ γ, fibL kb (List.ofFn γ)), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
      · rw [fibRoots, List.mem_map]
        exact ⟨_, mem_rootsN hγ.1, rfl⟩
      · simpa using hγ.2
    rw [hK] at hmem
    exact List.not_mem_nil hmem
  · exact eq_of_imgTuple_eq ((hall _ (imgTuple_mem_tuplesL hω hlen hlt hw)).trans
      imgTuple_one.symm)

theorem famOK_of_hypOK (h : hypOK τ = true) {fl : List ℕ} (hfl : fl ∈ normVecs 3 τ.rank) :
    famOK (gramL τ) (rootsN τ) (simpleL τ) ((simpleL τ).map fun e => formB (gramL τ) e e)
      (kerBasis 3 fl) = true := by
  simp only [hypOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 fl hfl

theorem famOK_std_of_hypOK (h : hypOK τ = true) :
    famOK0 (gramL τ) (rootsN τ) (simpleL τ) ((simpleL τ).map fun e => formB (gramL τ) e e)
      (stdBasis τ.rank) = true := by
  simp only [hypOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

theorem length_of_mem_kerBasis {fl : List ℕ} (hfl : fl ∈ normVecs 3 τ.rank) :
    ∀ b ∈ kerBasis 3 fl, b.length = τ.rank := by
  intro b hb
  obtain ⟨j, -, -, rfl⟩ := mem_kerBasis hb
  rw [kerVec_length, (normVecs_pivot hfl).1]

theorem lt_of_mem_kerBasis {fl : List ℕ} : ∀ b ∈ kerBasis 3 fl, ∀ x ∈ b, x < 3 := by
  intro b hb
  obtain ⟨j, -, -, rfl⟩ := mem_kerBasis hb
  exact kerVec_lt fl j

theorem length_of_mem_stdBasis : ∀ b ∈ stdBasis τ.rank, b.length = τ.rank := by
  intro b hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
  simp

theorem lt_of_mem_stdBasis : ∀ b ∈ stdBasis τ.rank, ∀ x ∈ b, x < 3 := by
  intro b hb x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  split_ifs <;> norm_num

theorem exists_kernelRoot_of_kerNonemptyOK (h : kerNonemptyOK τ = true) {K : Type} [Field K]
    {ω : Kˣ} (hω : orderOf ω = 3) {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0) :
    ∃ β, IsRoot τ β ∧ rootChar (torV ω x) β = 1 := by
  simp only [kerNonemptyOK, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  rcases h (vecList x) (vecList_mem_expVecs x) with h0 | ⟨b, hb, hb0⟩
  · exfalso
    apply hx
    funext i
    have h1 := h0 ((vecList x).getD i 0) (by
      rw [List.getD_eq_getElem _ _ (by rw [vecList_length]; exact i.2)]
      exact List.getElem_mem _)
    rw [vecList_getD, ZMod.val_eq_zero] at h1
    exact h1
  · obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hb
    refine ⟨β, mem_rootList.1 hβ, ?_⟩
    rw [rootChar_torV, ← orderOf_dvd_iff_zpow_eq_one, hω]
    rw [dotN_ofFn (vecList_length x)] at hb0
    have e : ∑ i, ((vecList x).getD i.val 0 : ℤ) * β i = ∑ i, ((x i).val : ℤ) * β i :=
      Finset.sum_congr rfl fun i _ => by rw [vecList_getD]
    rw [e] at hb0
    exact_mod_cast Int.dvd_of_emod_eq_zero hb0

end Data



end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
