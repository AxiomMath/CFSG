module

public import Certificates.Data.Kernel.D4SylK
public import CFSG.Certificates.Kernel.D42KSound

public section

namespace CFSG.KC.D4SylK

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D42K

theorem wordK_eq (w : List Nat) : wordK w = encM (wordArr w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    unfold wordK at *
    rw [List.foldr_cons, ih, wordArr_cons, encM_mulArr]
    rfl

theorem aK_eq : aK = encM genA := wordK_eq wordA

theorem bK_eq : bK = encM genB := wordK_eq wordB

theorem foldl_bfsStepK (A B : Array GF8) (par : List (Nat × Bool)) (acc : List (Array GF8)) :
    par.foldl (bfsStepK (encM A) (encM B)) (acc.map encM) =
      (par.foldl (bfsStep A B) acc).map encM := by
  induction par generalizing acc with
  | nil => rfl
  | cons p par ih =>
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    unfold bfsStepK bfsStep
    rw [List.map_append, List.map_singleton, encM_mulArr, oneK, List.getD_map]
    cases p.2 <;> rfl

theorem bfsK_encM (A B : Array GF8) (par : List (Nat × Bool)) :
    bfsK (encM A) (encM B) par = (bfsElems A B par).map encM :=
  foldl_bfsStepK A B par [oneArr]

theorem foldl_bfsStep_append (A B : Array GF8) (par : List (Nat × Bool)) (acc : List (Array GF8)) :
    ∃ R, par.foldl (bfsStep A B) acc = acc ++ R := by
  induction par generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons p par ih =>
    obtain ⟨R, hR⟩ := ih (bfsStep A B acc p)
    refine ⟨mulArr (acc.getD p.1 oneArr) (if p.2 then A else B) :: R, ?_⟩
    rw [List.foldl_cons, hR, bfsStep, List.append_assoc, List.singleton_append]

theorem oneArr_mem_bfsElems' (A B : Array GF8) (par : List (Nat × Bool)) :
    oneArr ∈ bfsElems A B par := by
  obtain ⟨R, hR⟩ := foldl_bfsStep_append A B par [oneArr]
  rw [bfsElems, hR]
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem length_foldl_bfsStep (A B : Array GF8) (par : List (Nat × Bool)) (acc : List (Array GF8)) :
    (par.foldl (bfsStep A B) acc).length = acc.length + par.length := by
  induction par generalizing acc with
  | nil => simp
  | cons p par ih =>
    rw [List.foldl_cons, ih, bfsStep, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem length_bfsElems (A B : Array GF8) (par : List (Nat × Bool)) :
    (bfsElems A B par).length = par.length + 1 := by
  rw [bfsElems, length_foldl_bfsStep, List.length_singleton]
  omega

theorem getD_bfsElems (A B : Array GF8) (par : List (Nat × Bool)) (k : Nat) (hk : k < par.length)
    (hp : par[k].1 ≤ k) :
    (bfsElems A B par).getD (k + 1) oneArr =
      mulArr ((bfsElems A B par).getD par[k].1 oneArr) (if par[k].2 then A else B) := by
  have hsplit : par = par.take k ++ par[k] :: par.drop (k + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  set Y := (par.take k).foldl (bfsStep A B) [oneArr] with hYdef
  have hY : Y.length = k + 1 := by
    rw [hYdef, length_foldl_bfsStep, List.length_take, List.length_singleton]
    omega
  have hfin : bfsElems A B par = (par.drop (k + 1)).foldl (bfsStep A B) (bfsStep A B Y par[k]) := by
    unfold bfsElems
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  obtain ⟨R, hR⟩ := foldl_bfsStep_append A B (par.drop (k + 1)) (bfsStep A B Y par[k])
  set new := mulArr (Y.getD par[k].1 oneArr) (if par[k].2 then A else B) with hnew
  rw [hfin, hR, bfsStep]
  have hl : (Y ++ [new]).length = k + 2 := by
    rw [List.length_append, hY, List.length_singleton]
  have e1 : (Y ++ [new] ++ R).getD (k + 1) oneArr = new := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_append_right (by omega), hY, Nat.sub_self]
    rfl
  have e2 : (Y ++ [new] ++ R).getD par[k].1 oneArr = Y.getD par[k].1 oneArr := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  rw [e1, e2]

theorem size_of_mem_foldl (A B : Array GF8) (par : List (Nat × Bool)) (acc : List (Array GF8))
    (h : ∀ x ∈ acc, x.size = 64) : ∀ x ∈ par.foldl (bfsStep A B) acc, x.size = 64 := by
  induction par generalizing acc with
  | nil => exact h
  | cons p par ih =>
    refine ih _ fun x hx => ?_
    rw [bfsStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact size_mulArr _ _

theorem size_of_mem_bfsElems' (A B : Array GF8) (par : List (Nat × Bool)) :
    ∀ x ∈ bfsElems A B par, x.size = 64 :=
  size_of_mem_foldl A B par [oneArr] (by simpa using size_oneArr)

theorem getD_of_edgeK {A B C : Array GF8} {par : List (Nat × Bool)} {g : Bool}
    (hC : (if g then A else B) = C) (hlen : (bfsElems A B par).length = 81) {i t : Nat}
    (h : edgeK ((bfsElems A B par).map encM) par (encM C) i t g = true) :
    t < 81 ∧ (bfsElems A B par).getD t oneArr = mulArr ((bfsElems A B par).getD i oneArr) C := by
  have hpar : par.length = 80 := by
    have := length_bfsElems A B par
    omega
  unfold edgeK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨ht, (⟨⟨ht0, hit⟩, hp⟩ | hp)⟩ := h
  · rw [List.getD_eq_getElem _ _ (by omega)] at hp
    have e := getD_bfsElems A B par (t - 1) (by omega) (by rw [hp]; omega)
    rw [hp, Nat.sub_add_cancel ht0, hC] at e
    exact ⟨ht, e⟩
  · rw [oneK, List.getD_map, List.getD_map, ← encM_mulArr] at hp
    have hs : ((bfsElems A B par).getD t oneArr).size = 64 := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact size_of_mem_bfsElems' A B par _ (List.getElem_mem _)
    exact ⟨ht, encM_inj hs (size_mulArr _ _) hp⟩

@[expose] def IsNxtTable (X : List (Array GF8)) (A B : Array GF8) (nxt : List (Nat × Nat)) : Prop :=
  ∀ i < 81, (nxt.getD i (0, 0)).1 < 81 ∧
    X.getD (nxt.getD i (0, 0)).1 oneArr = mulArr (X.getD i oneArr) A ∧
    (nxt.getD i (0, 0)).2 < 81 ∧ X.getD (nxt.getD i (0, 0)).2 oneArr = mulArr (X.getD i oneArr) B

theorem enum_spec {A B : Array GF8} {par : List (Nat × Bool)} {nxt : List (Nat × Nat)}
    (h : enumCheckK (encM A) (encM B) par nxt = true) :
    (bfsElems A B par).length = 81 ∧ (bfsElems A B par).Nodup ∧
      IsNxtTable (bfsElems A B par) A B nxt := by
  unfold enumCheckK at h
  rw [bfsK_encM] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.length_map] at h
  obtain ⟨⟨hlen, hnd⟩, hcl⟩ := h
  refine ⟨hlen, hnd.of_map _, fun i hi => ?_⟩
  obtain ⟨ha, hb⟩ := hcl i hi
  obtain ⟨ha1, ha2⟩ := getD_of_edgeK (g := true) rfl hlen ha
  obtain ⟨hb1, hb2⟩ := getD_of_edgeK (g := false) rfl hlen hb
  exact ⟨ha1, ha2, hb1, hb2⟩

theorem closed_of_table {A B : Array GF8} {par : List (Nat × Bool)} {nxt : List (Nat × Nat)}
    (hlen : (bfsElems A B par).length = 81) (ht : IsNxtTable (bfsElems A B par) A B nxt) :
    ∀ x ∈ bfsElems A B par, mulArr x A ∈ bfsElems A B par ∧ mulArr x B ∈ bfsElems A B par := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hD : (bfsElems A B par).getD i oneArr = (bfsElems A B par)[i] := List.getD_eq_getElem _ _ hi
  obtain ⟨ha1, ha2, hb1, hb2⟩ := ht i (by omega)
  have mem : ∀ t < 81, (bfsElems A B par).getD t oneArr ∈ bfsElems A B par := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [← hD, ← ha2, ← hb2]
  exact ⟨mem _ ha1, mem _ hb1⟩

@[expose] def wordFold {M : Type*} (m : M → M → M) (g h u : M) (w : List Bool) : M :=
  w.foldl (fun v c => m v (if c then g else h)) u

theorem wordFold_cons {M : Type*} (m : M → M → M) (g h u : M) (c : Bool) (w : List Bool) :
    wordFold m g h u (c :: w) = wordFold m g h (m u (if c then g else h)) w := rfl

theorem walkK_cons (nxt : List (Nat × Nat)) (i : Nat) (c : Bool) (w : List Bool) :
    walkK nxt i (c :: w) =
      walkK nxt (if c then (nxt.getD i (0, 0)).1 else (nxt.getD i (0, 0)).2) w := rfl

theorem getD_walkK {A B : Array GF8} {X : List (Array GF8)} {nxt : List (Nat × Nat)}
    (ht : IsNxtTable X A B nxt) (w : List Bool) {i : Nat} (hi : i < 81) :
    walkK nxt i w < 81 ∧ X.getD (walkK nxt i w) oneArr = wordFold mulArr A B (X.getD i oneArr) w := by
  induction w generalizing i with
  | nil => exact ⟨hi, rfl⟩
  | cons c w ih =>
    obtain ⟨ha1, ha2, hb1, hb2⟩ := ht i hi
    rw [walkK_cons, wordFold_cons]
    cases c
    · obtain ⟨h1, h2⟩ := ih hb1
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ← hb2]
      exact ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := ih ha1
      rw [if_pos rfl, if_pos rfl, ← ha2]
      exact ⟨h1, h2⟩

theorem coe_wordFold {A B x : Array GF8} {g h u : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    (hu : (u : Matrix (Fin 8) (Fin 8) GF8) = toMat x) (w : List Bool) :
    ((wordFold (· * ·) g h u w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      toMat (wordFold mulArr A B x w) := by
  induction w generalizing u x with
  | nil => exact hu
  | cons c w ih =>
    rw [wordFold_cons, wordFold_cons]
    refine ih ?_
    cases c
    · rw [Units.val_mul, hu, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hh, toMat_mulArr]
    · rw [Units.val_mul, hu, if_pos rfl, if_pos rfl, hg, toMat_mulArr]

theorem getD_zero_bfsElems (A B : Array GF8) (par : List (Nat × Bool)) :
    (bfsElems A B par).getD 0 oneArr = oneArr := by
  obtain ⟨R, hR⟩ := foldl_bfsStep_append A B par [oneArr]
  rw [bfsElems, hR]
  rfl

theorem coe_wordFold_one {A B : Array GF8} {par : List (Nat × Bool)} {nxt : List (Nat × Nat)}
    {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    (ht : IsNxtTable (bfsElems A B par) A B nxt) (w : List Bool) :
    walkK nxt 0 w < 81 ∧ ((wordFold (· * ·) g h 1 w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      toMat ((bfsElems A B par).getD (walkK nxt 0 w) oneArr) := by
  obtain ⟨h1, h2⟩ := getD_walkK ht w (by omega : 0 < 81)
  refine ⟨h1, ?_⟩
  rw [h2, getD_zero_bfsElems]
  exact coe_wordFold hg hh (by rw [oneArr, toMat_ofMat]; rfl) w

theorem ne_of_walkK {A B : Array GF8} {par : List (Nat × Bool)} {nxt : List (Nat × Nat)}
    {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    (hlen : (bfsElems A B par).length = 81) (hnd : (bfsElems A B par).Nodup)
    (ht : IsNxtTable (bfsElems A B par) A B nxt) {v w : List Bool}
    (hvw : walkK nxt 0 v ≠ walkK nxt 0 w) :
    wordFold (· * ·) g h 1 v ≠ wordFold (· * ·) g h 1 w := by
  intro e
  obtain ⟨hv1, hv2⟩ := coe_wordFold_one (par := par) hg hh ht v
  obtain ⟨hw1, hw2⟩ := coe_wordFold_one (par := par) hg hh ht w
  have hm := congrArg (fun u : GL (Fin 8) GF8 => (u : Matrix (Fin 8) (Fin 8) GF8)) e
  rw [hv2, hw2, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hm
  have hx := eq_of_toMat_eq (size_of_mem_bfsElems' A B par _ (List.getElem_mem _))
    (size_of_mem_bfsElems' A B par _ (List.getElem_mem _)) hm
  exact hvw ((hnd.getElem_inj_iff).1 hx)

theorem wit_spec {A B : Array GF8} {par : List (Nat × Bool)} {nxt : List (Nat × Nat)}
    {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    (hlen : (bfsElems A B par).length = 81) (hnd : (bfsElems A B par).Nodup)
    (ht : IsNxtTable (bfsElems A B par) A B nxt) (hw : witCheckK nxt witWords = true) :
    g * (g ^ 2 * h ^ 2 * g * h) ≠ g ^ 2 * h ^ 2 * g * h * g ∧
      h * (g ^ 2 * h ^ 2 * g * h) ≠ g ^ 2 * h ^ 2 * g * h * h ∧
      g * h * (g ^ 2 * h ^ 2 * g * h) ≠ g ^ 2 * h ^ 2 * g * h * (g * h) ∧
      (g * h ^ 2) ^ 3 ≠ 1 := by
  unfold witCheckK at hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
  obtain ⟨⟨⟨w1, w2⟩, w3⟩, w4⟩ := hw
  have n1 : wordFold (· * ·) g h 1 [true, true, true, false, false, true, false] ≠
      wordFold (· * ·) g h 1 [true, true, false, false, true, false, true] :=
    ne_of_walkK hg hh hlen hnd ht w1
  have n2 : wordFold (· * ·) g h 1 [false, true, true, false, false, true, false] ≠
      wordFold (· * ·) g h 1 [true, true, false, false, true, false, false] :=
    ne_of_walkK hg hh hlen hnd ht w2
  have n3 : wordFold (· * ·) g h 1 [true, false, true, true, false, false, true, false] ≠
      wordFold (· * ·) g h 1 [true, true, false, false, true, false, true, false] :=
    ne_of_walkK hg hh hlen hnd ht w3
  have n4 : wordFold (· * ·) g h 1 [true, false, false, true, false, false, true, false, false] ≠
      wordFold (· * ·) g h 1 [] :=
    ne_of_walkK hg hh hlen hnd ht w4
  simp only [wordFold, List.foldl_cons, List.foldl_nil, ↓reduceIte, Bool.false_eq_true,
    one_mul] at n1 n2 n3 n4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pow_two, mul_assoc] using n1
  · simpa only [pow_two, mul_assoc] using n2
  · simpa only [pow_two, mul_assoc] using n3
  · simpa only [pow_two, pow_three', mul_assoc] using n4

theorem exists_mem_closure_of_mem {A B : Array GF8} {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    (par : List (Nat × Bool)) : ∀ x ∈ bfsElems A B par, ∃ u ∈ Subgroup.closure {g, h},
      ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  unfold bfsElems
  suffices H : ∀ (acc : List (Array GF8)), (∀ x ∈ acc, ∃ u ∈ Subgroup.closure {g, h},
      ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x) →
      ∀ x ∈ par.foldl (bfsStep A B) acc, ∃ u ∈ Subgroup.closure {g, h},
        ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x by
    refine H _ fun x hx => ⟨1, one_mem _, ?_⟩
    rw [List.mem_singleton] at hx
    rw [hx, oneArr, toMat_ofMat]
    rfl
  induction par with
  | nil => exact fun acc hacc => hacc
  | cons p par ih =>
    intro acc hacc
    refine ih _ fun x hx => ?_
    rw [bfsStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hacc x hx
    · obtain ⟨u, hu, hux⟩ : ∃ u ∈ Subgroup.closure {g, h},
          ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (acc.getD p.1 oneArr) := by
        by_cases hi : p.1 < acc.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hacc _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega), oneArr, toMat_ofMat]
          exact ⟨1, one_mem _, rfl⟩
      cases hp : p.2
      · refine ⟨u * h, mul_mem hu (Subgroup.subset_closure (by simp)), ?_⟩
        rw [Units.val_mul, hux, hh, ← toMat_mulArr]
        rfl
      · refine ⟨u * g, mul_mem hu (Subgroup.subset_closure (by simp)), ?_⟩
        rw [Units.val_mul, hux, hg, ← toMat_mulArr]
        rfl

theorem mem_of_mem_closure {A B : Array GF8} {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    {par : List (Nat × Bool)}
    (hcl : ∀ x ∈ bfsElems A B par, mulArr x A ∈ bfsElems A B par ∧ mulArr x B ∈ bfsElems A B par)
    (u : GL (Fin 8) GF8) (hu : u ∈ Subgroup.closure {g, h}) :
    ∃ x ∈ bfsElems A B par, ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  have key : ∀ u : GL (Fin 8) GF8, u ∈ Submonoid.closure {g, h} →
      ∃ x ∈ bfsElems A B par, ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
    intro u hu'
    induction hu' using Submonoid.closure_induction_right with
    | one => exact ⟨oneArr, oneArr_mem_bfsElems' _ _ _, by rw [oneArr, toMat_ofMat]; rfl⟩
    | mul_right x hx y hy ih =>
      obtain ⟨xa, hxa, hxe⟩ := ih
      rcases hy with rfl | rfl
      · exact ⟨mulArr xa A, (hcl xa hxa).1, by rw [Units.val_mul, hxe, hg, toMat_mulArr]⟩
      · exact ⟨mulArr xa B, (hcl xa hxa).2, by rw [Units.val_mul, hxe, hh, toMat_mulArr]⟩
  apply key
  rw [← Subgroup.closure_toSubmonoid_of_finite]
  exact hu

theorem card_closure {A B : Array GF8} {g h : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat A) (hh : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat B)
    {par : List (Nat × Bool)} (hnd : (bfsElems A B par).Nodup)
    (hcl : ∀ x ∈ bfsElems A B par, mulArr x A ∈ bfsElems A B par ∧ mulArr x B ∈ bfsElems A B par) :
    Nat.card (Subgroup.closure ({g, h} : Set (GL (Fin 8) GF8))) = (bfsElems A B par).length := by
  set X := bfsElems A B par
  have himg : ((↑) : GL (Fin 8) GF8 → Matrix (Fin 8) (Fin 8) GF8) ''
      (Subgroup.closure ({g, h} : Set (GL (Fin 8) GF8)) : Set _) =
      toMat '' (X.toFinset : Set (Array GF8)) := by
    ext M
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, hux⟩ := mem_of_mem_closure hg hh hcl u hu
      exact ⟨x, by simpa using hx, hux.symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hux⟩ := exists_mem_closure_of_mem hg hh par x (by simpa using hx)
      exact ⟨u, hu, hux⟩
  have hinj : Set.InjOn toMat (X.toFinset : Set (Array GF8)) := fun x hx y hy hxy =>
    eq_of_toMat_eq (size_of_mem_bfsElems' A B par x (by simpa using hx))
      (size_of_mem_bfsElems' A B par y (by simpa using hy)) hxy
  calc Nat.card (Subgroup.closure ({g, h} : Set (GL (Fin 8) GF8)))
        = (Subgroup.closure ({g, h} : Set (GL (Fin 8) GF8)) : Set (GL (Fin 8) GF8)).ncard :=
        (Nat.card_coe_set_eq _).symm
    _ = (((↑) : GL (Fin 8) GF8 → Matrix (Fin 8) (Fin 8) GF8) ''
          (Subgroup.closure ({g, h} : Set (GL (Fin 8) GF8)) : Set _)).ncard :=
        (Set.ncard_image_of_injective _ Units.val_injective).symm
    _ = (toMat '' (X.toFinset : Set (Array GF8))).ncard := by rw [himg]
    _ = (X.toFinset : Set (Array GF8)).ncard := hinj.ncard_image
    _ = X.toFinset.card := Set.ncard_coe_finset _
    _ = X.length := List.toFinset_card_of_nodup hnd

end CFSG.KC.D4SylK

end
