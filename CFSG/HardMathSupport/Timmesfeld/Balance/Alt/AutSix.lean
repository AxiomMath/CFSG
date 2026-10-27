module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.List.GetD

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv Subgroup

@[expose] def autSixA : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def autSixB : Perm (Fin 6) := swap 0 2 * (swap 1 5 * swap 1 4 * swap 1 3)

@[expose] def autSixSteps : List (Bool × ℕ) := [
  (false, 0), (true, 0), (true, 1), (false, 2), (true, 2), (false, 3), (true, 3), (true, 4),
  (false, 5), (true, 5), (true, 6), (false, 7), (true, 7), (false, 8), (true, 8), (true, 9),
  (false, 10), (false, 11), (true, 11), (true, 12), (false, 13), (true, 14), (false, 15),
  (true, 15), (false, 16), (true, 16), (true, 17), (true, 18), (false, 19), (true, 19),
  (false, 20), (true, 20), (true, 21), (false, 22), (true, 22), (true, 23), (false, 24),
  (true, 25), (false, 26), (true, 26), (false, 27), (true, 27), (false, 28), (true, 28),
  (true, 29), (false, 30), (true, 31), (false, 32), (true, 32), (false, 33), (true, 33),
  (false, 35), (true, 35), (false, 36), (true, 36), (true, 37), (false, 38), (true, 38),
  (true, 39), (false, 40), (true, 41), (false, 42), (false, 44), (true, 44), (false, 45),
  (true, 45), (true, 46), (false, 47), (true, 47), (true, 48), (false, 49), (true, 50),
  (false, 51), (true, 52), (false, 53), (true, 54), (false, 55), (true, 55), (false, 56),
  (true, 56), (false, 58), (true, 58), (false, 59), (true, 60), (false, 61), (true, 61),
  (true, 62), (true, 63), (false, 64), (true, 65), (false, 66), (true, 66), (false, 67),
  (true, 67), (false, 69), (true, 69), (false, 70), (true, 71), (false, 72), (true, 72),
  (true, 73), (false, 74), (true, 74), (true, 75), (false, 76), (true, 76), (true, 77),
  (false, 78), (true, 79), (false, 80), (true, 81), (false, 82), (true, 83), (false, 84),
  (true, 84), (false, 86), (true, 86), (false, 87), (false, 88), (true, 88), (true, 89),
  (false, 90), (true, 90), (true, 91), (false, 92), (true, 93), (false, 94), (true, 95),
  (false, 96), (true, 97), (false, 98), (true, 98), (false, 100), (true, 100), (false, 101),
  (true, 102), (false, 103), (true, 103), (false, 104), (true, 104), (false, 106), (true, 106),
  (false, 107), (true, 108), (false, 109), (true, 109), (true, 110), (false, 111), (true, 111),
  (true, 112), (false, 113), (true, 113), (true, 114), (false, 115), (true, 116), (false, 117),
  (true, 118), (false, 120), (true, 120), (false, 121), (true, 121), (false, 123), (true, 123),
  (true, 125), (false, 126), (true, 126), (true, 127), (false, 128), (true, 128), (true, 129),
  (false, 130), (true, 130), (true, 131), (false, 132), (true, 133), (false, 134), (true, 135),
  (true, 136), (true, 137), (false, 138), (true, 139), (false, 140), (true, 141), (false, 142),
  (true, 143), (false, 144), (true, 144), (false, 146), (true, 146), (false, 147), (true, 148),
  (false, 149), (true, 149), (false, 150), (true, 150), (false, 152), (true, 152), (false, 153),
  (true, 153), (true, 154), (false, 155), (true, 155), (true, 156), (false, 157), (true, 157),
  (true, 158), (false, 159), (true, 160), (true, 162), (false, 163), (false, 164), (true, 164),
  (false, 166), (true, 166), (false, 167), (true, 168), (false, 169), (true, 169), (false, 170),
  (true, 170), (false, 172), (true, 173), (true, 174), (false, 175), (true, 176), (false, 177),
  (true, 177), (false, 178), (true, 178), (false, 181), (true, 181), (true, 182), (false, 183),
  (true, 183), (true, 184), (false, 185), (true, 185), (true, 186), (false, 187), (true, 188),
  (true, 191), (true, 192), (false, 193), (true, 194), (false, 195), (true, 196), (false, 199),
  (true, 199), (false, 200), (true, 201), (true, 202), (true, 203), (false, 205), (true, 205),
  (false, 208), (true, 208), (false, 209), (true, 209), (true, 210), (true, 211), (false, 212),
  (true, 213), (true, 216), (true, 217), (false, 218), (true, 219), (false, 220), (true, 221),
  (false, 222), (true, 222), (false, 223), (true, 224), (true, 225), (false, 227), (true, 227),
  (false, 229), (false, 231), (true, 231), (false, 232), (false, 234), (true, 234), (false, 235),
  (true, 235), (false, 237), (true, 239), (false, 240), (false, 241), (true, 241), (false, 244),
  (false, 246), (true, 246), (true, 247), (true, 250), (false, 251), (false, 252), (true, 253),
  (false, 256), (true, 256), (false, 258), (true, 258), (false, 259), (true, 259), (true, 261),
  (false, 262), (false, 263), (true, 263), (false, 266), (false, 268), (true, 268), (true, 269),
  (true, 272), (false, 273), (true, 274), (true, 276), (true, 277), (true, 280), (false, 281),
  (true, 282), (false, 283), (true, 284), (false, 285), (true, 286), (false, 288), (true, 291),
  (false, 292), (false, 293), (false, 296), (true, 296), (true, 297), (true, 299), (false, 300),
  (true, 301), (false, 302), (false, 303), (true, 304), (false, 306), (true, 309), (false, 310),
  (false, 311), (false, 313), (true, 313), (false, 314), (true, 314), (false, 315), (false, 318),
  (false, 320), (true, 320), (true, 322), (true, 323), (false, 324), (true, 325), (false, 329),
  (false, 332), (true, 335), (true, 336), (false, 348), (false, 349), (true, 349), (true, 351)
]

@[expose] def autSixGen (c : Bool) : Perm (Fin 6) := if c then autSixB else autSixA

@[expose] def autSixBuild (L : List (Perm (Fin 6))) : List (Bool × ℕ) → List (Perm (Fin 6))
  | [] => L
  | (c, j) :: t => autSixBuild (L ++ [autSixGen c * L.getD j 1]) t

@[expose] def autSixEnc (x : Perm (Fin 6)) : List ℕ := List.ofFn fun i => (x i : ℕ)

@[expose] def autSixComp (l m : List ℕ) : List ℕ := m.map fun i => l.getD i 0

@[expose] def autSixSq (l : List ℕ) : List ℕ := autSixComp l l

@[expose] def autSixId : List ℕ := List.ofFn fun i : Fin 6 => (i : ℕ)

theorem autSixEnc_inj : Function.Injective autSixEnc := fun _ _ h =>
  Equiv.ext fun i => Fin.ext (congrFun (List.ofFn_injective h) i)

private theorem autSixEnc_length (x : Perm (Fin 6)) : (autSixEnc x).length = 6 :=
  List.length_ofFn

private theorem autSixEnc_getElem (x : Perm (Fin 6)) (i : ℕ) (h : i < (autSixEnc x).length) :
    (autSixEnc x)[i] = (x ⟨i, by simpa [autSixEnc_length] using h⟩ : ℕ) :=
  List.getElem_ofFn ..

private theorem autSixEnc_getD (x : Perm (Fin 6)) (j : Fin 6) :
    (autSixEnc x).getD (j : ℕ) 0 = (x j : ℕ) := by
  rw [List.getD_eq_getElem _ _ (by simp [autSixEnc_length])]
  rw [autSixEnc_getElem]

private theorem autSixEnc_mul (x y : Perm (Fin 6)) :
    autSixEnc (x * y) = autSixComp (autSixEnc x) (autSixEnc y) := by
  refine List.ext_getElem (by simp [autSixEnc_length, autSixComp]) fun i h1 h2 => ?_
  rw [autSixEnc_getElem]
  simp only [autSixComp]
  rw [List.getElem_map, autSixEnc_getElem, autSixEnc_getD]
  rfl

private theorem autSixEnc_one : autSixEnc 1 = autSixId := rfl

private theorem autSixEnc_sq (x : Perm (Fin 6)) : autSixSq (autSixEnc x) = autSixEnc (x ^ 2) := by
  rw [autSixSq, ← autSixEnc_mul, sq]

private theorem autSixEnc_pow4 (x : Perm (Fin 6)) :
    autSixSq (autSixSq (autSixEnc x)) = autSixEnc (x ^ 4) := by
  rw [autSixEnc_sq, autSixEnc_sq, ← pow_mul]

private theorem autSixEnc_pow5 (x : Perm (Fin 6)) :
    autSixComp (autSixSq (autSixSq (autSixEnc x))) (autSixEnc x) = autSixEnc (x ^ 5) := by
  rw [autSixEnc_pow4, ← autSixEnc_mul, ← pow_succ]

@[expose] def autSixBuildE (L : List (List ℕ)) : List (Bool × ℕ) → List (List ℕ)
  | [] => L
  | (c, j) :: t =>
    autSixBuildE (L ++ [autSixComp (autSixEnc (autSixGen c)) (L.getD j autSixId)]) t

private theorem autSixBuildE_eq (s : List (Bool × ℕ)) : ∀ L : List (Perm (Fin 6)),
    autSixBuildE (L.map autSixEnc) s = (autSixBuild L s).map autSixEnc := by
  induction s with
  | nil => intro L; rfl
  | cons cj t ih =>
    intro L
    obtain ⟨c, j⟩ := cj
    simp only [autSixBuildE, autSixBuild]
    rw [← ih, List.map_append, List.map_singleton, autSixEnc_mul, ← autSixEnc_one,
      List.getD_map]

private theorem autSixBuild_mem (L : List (Perm (Fin 6)))
    (hL : ∀ x ∈ L, x ∈ closure ({autSixA, autSixB} : Set (Perm (Fin 6)))) :
    ∀ s : List (Bool × ℕ), ∀ x ∈ autSixBuild L s,
      x ∈ closure ({autSixA, autSixB} : Set (Perm (Fin 6))) := by
  intro s
  induction s generalizing L with
  | nil => exact hL
  | cons cj t ih =>
    obtain ⟨c, j⟩ := cj
    refine ih _ ?_
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hL x hx
    · refine mul_mem ?_ ?_
      · exact subset_closure (by cases c <;> simp [autSixGen])
      · by_cases hj : j < L.length
        · refine hL _ ?_
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          exact one_mem _

private theorem autSixBuildE_nodup : (autSixBuildE [autSixEnc 1] autSixSteps).Nodup := by
  decide +kernel

private theorem autSixBuildE_length : (autSixBuildE [autSixEnc 1] autSixSteps).length = 360 := by
  decide +kernel

private theorem autSixBuild_nodup : (autSixBuild [1] autSixSteps).Nodup := by
  have h := autSixBuildE_nodup
  rw [show [autSixEnc 1] = ([1] : List (Perm (Fin 6))).map autSixEnc from rfl,
    autSixBuildE_eq] at h
  exact List.Nodup.of_map _ h

private theorem autSixBuild_length : (autSixBuild [1] autSixSteps).length = 360 := by
  have h := autSixBuildE_length
  rw [show [autSixEnc 1] = ([1] : List (Perm (Fin 6))).map autSixEnc from rfl,
    autSixBuildE_eq, List.length_map] at h
  exact h

private theorem autSix_sign_a : Perm.sign autSixA = 1 := by decide +kernel
private theorem autSix_sign_b : Perm.sign autSixB = 1 := by decide +kernel

private theorem autSix_closure :
    closure ({autSixA, autSixB} : Set (Perm (Fin 6))) = alternatingGroup (Fin 6) := by
  have hle : closure ({autSixA, autSixB} : Set (Perm (Fin 6))) ≤ alternatingGroup (Fin 6) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact Perm.mem_alternatingGroup.2 autSix_sign_a
    · exact Perm.mem_alternatingGroup.2 autSix_sign_b
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hsub : ((autSixBuild [1] autSixSteps).toFinset : Set (Perm (Fin 6))) ⊆
      closure ({autSixA, autSixB} : Set (Perm (Fin 6))) := fun x hx =>
    autSixBuild_mem [1] (by simp [one_mem]) autSixSteps x (List.mem_toFinset.1 hx)
  calc Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    _ = ((autSixBuild [1] autSixSteps).toFinset : Set (Perm (Fin 6))).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup autSixBuild_nodup,
          autSixBuild_length]
    _ ≤ (closure ({autSixA, autSixB} : Set (Perm (Fin 6))) : Set (Perm (Fin 6))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (closure ({autSixA, autSixB} : Set (Perm (Fin 6)))) :=
        (Nat.card_coe_set_eq _).symm

private theorem autSix_centralizer (x : Perm (Fin 6)) (ha : x * autSixA = autSixA * x)
    (hb : x * autSixB = autSixB * x) : x = 1 := by
  revert x
  unfold autSixA autSixB
  decide +kernel

@[expose] def autSixEven : Finset (List ℕ) :=
  (Finset.univ.filter fun x : Perm (Fin 6) => Perm.sign x = 1).map ⟨autSixEnc, autSixEnc_inj⟩

@[expose] def autSixI : Finset (List ℕ) :=
  autSixEven.filter fun l => autSixSq l = autSixId ∧ l ≠ autSixId

@[expose] def autSixJ : Finset (List ℕ) :=
  autSixEven.filter fun l => autSixSq (autSixSq l) = autSixId ∧ autSixSq l ≠ autSixId

@[expose] def autSixPairs : Finset (List ℕ × List ℕ) :=
  (autSixI ×ˢ autSixJ).filter fun q =>
    autSixComp (autSixSq (autSixSq (autSixComp q.1 q.2))) (autSixComp q.1 q.2) = autSixId ∧
      autSixComp q.1 q.2 ≠ autSixId

private theorem autSixPairs_card : autSixPairs.card ≤ 1440 := by
  decide +kernel

private theorem autSix_rel_a : autSixA ^ 2 = 1 := by decide +kernel
private theorem autSix_ne_a : autSixA ≠ 1 := by decide +kernel
private theorem autSix_rel_b : autSixB ^ 4 = 1 := by decide +kernel
private theorem autSix_ne_b : autSixB ^ 2 ≠ 1 := by decide +kernel
private theorem autSix_rel_ab : (autSixA * autSixB) ^ 5 = 1 := by decide +kernel
private theorem autSix_ne_ab : autSixA * autSixB ≠ 1 := by decide +kernel

private theorem autSixEnc_mem_pairs {x y : Perm (Fin 6)} (hx : Perm.sign x = 1)
    (hy : Perm.sign y = 1) (h1 : x ^ 2 = 1) (h2 : x ≠ 1) (h3 : y ^ 4 = 1) (h4 : y ^ 2 ≠ 1)
    (h5 : (x * y) ^ 5 = 1) (h6 : x * y ≠ 1) : (autSixEnc x, autSixEnc y) ∈ autSixPairs := by
  have hxA : autSixEnc x ∈ autSixEven :=
    Finset.mem_map.2 ⟨x, by simpa using hx, rfl⟩
  have hyA : autSixEnc y ∈ autSixEven :=
    Finset.mem_map.2 ⟨y, by simpa using hy, rfl⟩
  simp only [autSixPairs, autSixI, autSixJ, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨⟨hxA, ?_, ?_⟩, hyA, ?_, ?_⟩, ?_, ?_⟩
  · rw [autSixEnc_sq, h1, autSixEnc_one]
  · intro h
    exact h2 (autSixEnc_inj (h.trans autSixEnc_one.symm))
  · rw [autSixEnc_pow4, h3, autSixEnc_one]
  · intro h
    exact h4 (autSixEnc_inj ((autSixEnc_sq y).symm.trans (h.trans autSixEnc_one.symm)))
  · rw [← autSixEnc_mul, autSixEnc_pow5, h5, autSixEnc_one]
  · intro h
    rw [← autSixEnc_mul] at h
    exact h6 (autSixEnc_inj (h.trans autSixEnc_one.symm))

private theorem coe_mulAut_pow_eq_one_iff {P : Type*} [Group P] {H : Subgroup P} (σ : MulAut H)
    (g : H) (n : ℕ) : ((σ g : H) : P) ^ n = 1 ↔ (g : P) ^ n = 1 := by
  rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one,
    OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

private theorem closure_subtype_eq_top {P : Type*} [Group P] {H : Subgroup P} {a b : H}
    (h : closure ({(a : P), (b : P)} : Set P) = H) : closure ({a, b} : Set H) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
  exact h

private theorem autSix_mem_a : autSixA ∈ alternatingGroup (Fin 6) :=
  Perm.mem_alternatingGroup.2 autSix_sign_a

private theorem autSix_mem_b : autSixB ∈ alternatingGroup (Fin 6) :=
  Perm.mem_alternatingGroup.2 autSix_sign_b

set_option maxRecDepth 100000 in
theorem finite_and_card_mulAut_alternatingGroup_six_le :
    Finite (MulAut (alternatingGroup (Fin 6))) ∧
      Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ 1440 := by
  set a : alternatingGroup (Fin 6) := ⟨autSixA, autSix_mem_a⟩ with ha
  set b : alternatingGroup (Fin 6) := ⟨autSixB, autSix_mem_b⟩ with hb
  have hgen : closure ({a, b} : Set (alternatingGroup (Fin 6))) = ⊤ :=
    closure_subtype_eq_top autSix_closure
  have hS : ∀ σ : MulAut (alternatingGroup (Fin 6)),
      (autSixEnc ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)),
        autSixEnc ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6))) ∈ autSixPairs := by
    intro σ
    have hmul : ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) *
        ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          ((σ (a * b) : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [map_mul, Subgroup.coe_mul]
    have h1 : ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 2 = 1 :=
      (coe_mulAut_pow_eq_one_iff σ a 2).2 autSix_rel_a
    have h2 : ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h => autSix_ne_a (by
      have := (coe_mulAut_pow_eq_one_iff σ a 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one] at this)
    have h3 : ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 4 = 1 :=
      (coe_mulAut_pow_eq_one_iff σ b 4).2 autSix_rel_b
    have h4 : ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 2 ≠ 1 := fun h =>
      autSix_ne_b ((coe_mulAut_pow_eq_one_iff σ b 2).1 h)
    have h5 : (((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) *
        ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6))) ^ 5 = 1 := by
      rw [hmul]
      exact (coe_mulAut_pow_eq_one_iff σ (a * b) 5).2 (by rw [Subgroup.coe_mul]; exact autSix_rel_ab)
    have h6 : ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) *
        ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h => autSix_ne_ab (by
      rw [hmul] at h
      have := (coe_mulAut_pow_eq_one_iff σ (a * b) 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one, Subgroup.coe_mul] at this)
    exact autSixEnc_mem_pairs (Perm.mem_alternatingGroup.1 (σ a).2)
      (Perm.mem_alternatingGroup.1 (σ b).2) h1 h2 h3 h4 h5 h6
  let F : MulAut (alternatingGroup (Fin 6)) → autSixPairs := fun σ =>
    ⟨(autSixEnc ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)),
      autSixEnc ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6))), hS σ⟩
  have hF : Function.Injective F := by
    intro σ τ h
    have h1 : σ a = τ a :=
      Subtype.ext (autSixEnc_inj (congrArg (fun q : autSixPairs => q.1.1) h))
    have h2 : σ b = τ b :=
      Subtype.ext (autSixEnc_inj (congrArg (fun q : autSixPairs => q.1.2) h))
    have hst : σ.toMonoidHom = τ.toMonoidHom := MonoidHom.eq_of_eqOn_dense hgen (by
      rintro x (rfl | rfl)
      · exact h1
      · exact h2)
    exact MulEquiv.ext fun x => DFunLike.congr_fun hst x
  refine ⟨Finite.of_injective F hF, ?_⟩
  calc Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ Nat.card autSixPairs :=
        Nat.card_le_card_of_injective F hF
    _ = autSixPairs.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 1440 := autSixPairs_card

private theorem autSix_conj_injective :
    Function.Injective (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have key : ∀ g : alternatingGroup (Fin 6), x * (g : Perm (Fin 6)) = (g : Perm (Fin 6)) * x := by
    intro g
    have h1 := congrArg (fun e : MulAut (alternatingGroup (Fin 6)) =>
      ((e g : alternatingGroup (Fin 6)) : Perm (Fin 6))) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * (g : Perm (Fin 6)) = x * (g : Perm (Fin 6)) * x⁻¹ * x := by group
      _ = (g : Perm (Fin 6)) * x := by rw [h1]
  exact Subgroup.mem_bot.2 (autSix_centralizer x (key ⟨autSixA, autSix_mem_a⟩)
    (key ⟨autSixB, autSix_mem_b⟩))

private theorem autSix_dvd : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
  have h := Subgroup.card_subgroup_dvd_card
    (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6))))
  have hc : Nat.card (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6)))) =
      720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective autSix_conj_injective).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rwa [hc] at h

theorem no_elemAbelian_cube_mulAut_alternating_six
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (alternatingGroup (Fin 6)))) :
    ¬ (IsMulCommutative D ∧ (∀ x ∈ D, x ^ p = 1) ∧ Nat.card D = p ^ 3) := by
  rintro ⟨-, -, hD⟩
  obtain ⟨hfin, hle⟩ := finite_and_card_mulAut_alternatingGroup_six_le
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  have h1 : p ^ 3 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    rw [← hD]
    exact Subgroup.card_subgroup_dvd_card D
  have h2 : Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440 := by
    obtain ⟨k, hk⟩ := autSix_dvd
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  have h3 : p ^ 3 ∣ 2 ^ 5 * 3 ^ 2 * 5 := h1.trans h2
  have h4 : p ∣ 2 ^ 5 * 3 ^ 2 * 5 := (dvd_pow_self p (by norm_num)).trans h3
  rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
  · rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h6))
    · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h6)
      subst this
      omega
  · have : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
    subst this
    omega

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
