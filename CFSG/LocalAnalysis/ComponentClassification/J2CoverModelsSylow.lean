module

public import CFSG.Sporadic.J2.Simple
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsCheck

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

abbrev Perm315 : Type := Equiv.Perm (Fin 315)

theorem ofFn_getElem! {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

@[expose, irreducible] noncomputable def gA : Perm315 := MulAction.toPerm CFSG.Sporadic.J2.a

@[expose, irreducible] noncomputable def gB : Perm315 := MulAction.toPerm CFSG.Sporadic.J2.b

@[expose, irreducible] noncomputable def P : Subgroup Perm315 := Subgroup.closure {gA, gB}

theorem gA_eq : gA = MulAction.toPerm CFSG.Sporadic.J2.a := by rw [gA]

theorem gB_eq : gB = MulAction.toPerm CFSG.Sporadic.J2.b := by rw [gB]

theorem P_eq : P = Subgroup.closure {gA, gB} := by rw [P]

theorem gA_mem : gA ∈ P := by
  rw [P_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem gB_mem : gB ∈ P := by
  rw [P_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def letter (k : ℕ) : Perm315 := if k = 0 then gA else gB

theorem letter_mem (k : ℕ) : letter k ∈ P := by
  unfold letter
  split_ifs
  exacts [gA_mem, gB_mem]

theorem gA_mul_gA : gA * gA = 1 := by
  have h := congrArg (MulAction.toPermHom CFSG.Sporadic.J2.J (Fin 315)) CFSG.Sporadic.J2.a_sq
  rw [map_pow, map_one, pow_two] at h
  rw [gA_eq]
  exact h

theorem gB_mul_gB_mul_gB : gB * gB * gB = 1 := by
  have h := congrArg (MulAction.toPermHom CFSG.Sporadic.J2.J (Fin 315)) CFSG.Sporadic.J2.b_cube
  rw [map_pow, map_one, pow_three, ← mul_assoc] at h
  rw [gB_eq]
  exact h

theorem gA_inv : gA⁻¹ = gA := inv_eq_of_mul_eq_one_right gA_mul_gA

theorem gB_inv : gB⁻¹ = gB * gB := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact
  gB_mul_gB_mul_gB)

theorem P_eq_range : P = (MulAction.toPermHom CFSG.Sporadic.J2.J (Fin 315)).range := by
  rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.J2.closure_ab, MonoidHom.map_closure,
    Set.image_pair, P_eq, gA_eq, gB_eq]
  rfl

theorem card_P : Nat.card P = 604800 := by
  rw [P_eq_range, ← CFSG.Sporadic.J2.card_J]
  exact Nat.card_congr (MonoidHom.ofInjective (f := MulAction.toPermHom CFSG.Sporadic.J2.J
    (Fin 315)) MulAction.toPerm_injective).toEquiv.symm

theorem alphaArr_get {i : ℕ} (hi : i < 315) :
    alphaArr[i]! = ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i := by
  unfold alphaArr
  exact ofFn_getElem! _ hi

theorem betaArr_get {i : ℕ} (hi : i < 315) :
    betaArr[i]! = ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i := by
  unfold betaArr
  exact ofFn_getElem! _ hi

theorem rep_alphaArr : Rep 315 alphaArr gA := fun x => by
  have h := CFSG.Sporadic.J2.rep_alpha x.val x.isLt
  rw [CFSG.Sporadic.Th.idx_of_lt _ x.isLt] at h
  rw [gA_eq]
  exact (alphaArr_get x.isLt).trans h

theorem rep_betaArr : Rep 315 betaArr gB := fun x => by
  have h := CFSG.Sporadic.J2.rep_beta x.val x.isLt
  rw [CFSG.Sporadic.Th.idx_of_lt _ x.isLt] at h
  rw [gB_eq]
  exact (betaArr_get x.isLt).trans h

theorem rep_letterArr (k : ℕ) : Rep 315 (letterArr k) (letter k) := by
  unfold letterArr letter
  split_ifs
  exacts [rep_alphaArr, rep_betaArr]

@[expose] noncomputable def wordPerm (w : List ℕ) : Perm315 := (w.map letter).prod

theorem wordPerm_mem (w : List ℕ) : wordPerm w ∈ P :=
  list_prod_mem fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact letter_mem k

theorem wordPerm_nil : wordPerm [] = 1 := rfl

theorem wordArr_cons (k : ℕ) (w : List ℕ) :
    wordArr (k :: w) = compA 315 (letterArr k) (wordArr w) := by
  rw [wordArr, wordArr, List.foldr_cons]

theorem wordPerm_cons (k : ℕ) (w : List ℕ) : wordPerm (k :: w) = letter k * wordPerm w := by
  rw [wordPerm, wordPerm, List.map_cons, List.prod_cons]

theorem rep_wordArr : ∀ w : List ℕ, Rep 315 (wordArr w) (wordPerm w)
  | [] => by rw [wordArr, List.foldr_nil, wordPerm_nil]; exact rep_idA
  | k :: w => by
    rw [wordArr_cons, wordPerm_cons]
    exact rep_compA (rep_letterArr k) (rep_wordArr w)

@[expose, irreducible] noncomputable def y (k : ℕ) : Perm315 := wordPerm (nth [] yWords k)

@[expose, irreducible] noncomputable def S : Subgroup Perm315 := Subgroup.closure {y 0, y 1, y 2}

theorem y_eq (k : ℕ) : y k = wordPerm (nth [] yWords k) := by rw [y]

theorem S_eq : S = Subgroup.closure {y 0, y 1, y 2} := by rw [S]

theorem y_mem_P (k : ℕ) : y k ∈ P := by
  rw [y_eq]
  exact wordPerm_mem _

theorem S_le_P : S ≤ P := by
  rw [S_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro σ (rfl | rfl | rfl) <;> exact y_mem_P _

theorem y_zero_mem : y 0 ∈ S := by
  rw [S_eq]
  exact Subgroup.subset_closure (by simp)

theorem y_one_mem : y 1 ∈ S := by
  rw [S_eq]
  exact Subgroup.subset_closure (by simp)

theorem y_two_mem : y 2 ∈ S := by
  rw [S_eq]
  exact Subgroup.subset_closure (by simp)

@[expose] noncomputable def yS (k : ℕ) : S :=
  if k = 0 then ⟨y 0, y_zero_mem⟩ else if k = 1 then ⟨y 1, y_one_mem⟩ else ⟨y 2, y_two_mem⟩

theorem yArrs_get {k : ℕ} (hk : k < 3) : yArrs[k]! = wordArr (nth [] yWords k) := by
  unfold yArrs
  exact ofFn_getElem! _ hk

theorem yS_coe {k : ℕ} (hk : k < 3) : (yS k : Perm315) = y k := by
  unfold yS
  interval_cases k <;> rfl

theorem rep_yArrs {k : ℕ} (hk : k < 3) : Rep 315 yArrs[k]! (yS k : Perm315) := by
  rw [yArrs_get hk, yS_coe hk, y_eq]
  exact rep_wordArr _

@[expose] def treeCheck : Bool :=
  (List.range 128).all fun x => x == 0 || (decide (par x < x) && decide (gen x < 3))

theorem treeCheck_eq : treeCheck = true := by decide +kernel

theorem nth_of_length_le {α : Type} (d : α) :
    ∀ (l : List α) (k : ℕ), l.length ≤ k → nth d l k = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: l, k + 1, h => nth_of_length_le d l k (by simpa using h)

theorem tree_spec {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) : par x < x ∧ gen x < 3 := by
  have h := treeCheck_eq
  simp only [treeCheck, List.all_eq_true, List.mem_range] at h
  have := h x hx
  simp only [Bool.or_eq_true, beq_iff_eq, hx0, false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact this

theorem parT_length : parT.length = 128 := by decide +kernel

theorem genT_length : genT.length = 128 := by decide +kernel

theorem par_lt {x : ℕ} (hx0 : x ≠ 0) : par x < x := by
  by_cases hx : x < 128
  · exact (tree_spec hx0 hx).1
  · rw [par, nth_of_length_le _ _ _ (by rw [parT_length]; omega)]
    omega

theorem gen_lt (x : ℕ) : gen x < 3 := by
  by_cases hx : x < 128
  · by_cases hx0 : x = 0
    · subst hx0; decide
    · exact (tree_spec hx0 hx).2
  · rw [gen, nth_of_length_le _ _ _ (by rw [genT_length]; omega)]
    omega

theorem pathAux_succ {n x : ℕ} (hx : x ≠ 0) : pathAux (n + 1) x = x :: pathAux n (par x) := by
  simp only [pathAux, hx, ↓reduceIte]

theorem pathAux_stable : ∀ n x, x < n → pathAux (n + 1) x = pathAux n x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, h => by
    by_cases hx : x = 0
    · simp [pathAux, hx]
    · rw [pathAux_succ hx, pathAux_succ hx,
        pathAux_stable n (par x) (by have := par_lt hx; omega)]

theorem path_zero : path 0 = [] := by simp [path, pathAux]

theorem path_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) : path x = x :: path (par x) := by
  have hp := par_lt hx0
  rw [path, path, pathAux_stable 127 (par x) (by omega), pathAux_succ hx0]

theorem mem_pathAux : ∀ {n x z : ℕ}, z ∈ pathAux n x → z ≠ 0 ∧ z ≤ x
  | 0, _, _, h => by simp [pathAux] at h
  | n + 1, x, z, h => by
    by_cases hx : x = 0
    · simp [pathAux, hx] at h
    · rw [pathAux_succ hx, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨hx, le_rfl⟩
      · obtain ⟨h1, h2⟩ := mem_pathAux h
        exact ⟨h1, h2.trans (par_lt hx).le⟩

@[expose, irreducible] noncomputable def elt (x : ℕ) : S := ((path x).map fun z => yS (gen z)).prod

theorem elt_def (x : ℕ) : elt x = ((path x).map fun z => yS (gen z)).prod := by rw [elt]

theorem elt_zero : elt 0 = 1 := by rw [elt_def, path_zero, List.map_nil, List.prod_nil]

theorem elt_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) : elt x = yS (gen x) * elt (par x) := by
  rw [elt_def, elt_def (par x), path_cons hx0 hx, List.map_cons, List.prod_cons]

theorem rep_eltArr_aux : ∀ l : List ℕ, Rep 315
    (l.foldr (fun z acc => compA 315 yArrs[gen z]! acc) (idA 315))
    (((l.map fun z => yS (gen z)).prod : S) : Perm315)
  | [] => by rw [List.foldr_nil, List.map_nil, List.prod_nil]; exact rep_idA
  | z :: l => by
    rw [List.foldr_cons, List.map_cons, List.prod_cons, Subgroup.coe_mul]
    exact rep_compA (rep_yArrs (gen_lt z)) (rep_eltArr_aux l)

theorem rep_eltArr (x : ℕ) : Rep 315 (eltArr x) (elt x : Perm315) := by
  rw [eltArr, elt_def]
  exact rep_eltArr_aux (path x)

theorem eltArrs_get {x : ℕ} (hx : x < 128) : eltArrs[x]! = eltArr x := by
  unfold eltArrs
  exact ofFn_getElem! _ hx

theorem rep_eltArrs {x : ℕ} (hx : x < 128) : Rep 315 eltArrs[x]! (elt x : Perm315) := by
  rw [eltArrs_get hx]
  exact rep_eltArr x

theorem sCheck_parts :
    (∀ k < 3, ∀ b < 128, lmul k b < 128 ∧
      eqA 315 eltArrs[lmul k b]! (compA 315 yArrs[k]! eltArrs[b]!) = true) ∧
    (∀ a < 128, ∀ b < 128, a ≠ b → eqA 315 eltArrs[a]! eltArrs[b]! = false) ∧
    (∀ a < 128, invIdx a < 128 ∧ (mulTab[a]!)[invIdx a]! = 0) := by
  have h := sCheck_eq
  simp only [sCheck, Bool.and_eq_true, allLt_iff, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun a ha b hb hab => (h2 a ha b hb).resolve_left hab, h3⟩

theorem lmul_spec {k b : ℕ} (hk : k < 3) (hb : b < 128) :
    lmul k b < 128 ∧ elt (lmul k b) = yS k * elt b := by
  obtain ⟨hlt, he⟩ := sCheck_parts.1 k hk b hb
  refine ⟨hlt, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul]
  exact eq_of_eqA (rep_eltArrs hlt) (rep_compA (rep_yArrs hk) (rep_eltArrs hb)) he

theorem foldr_lmul_spec : ∀ (l : List ℕ), ∀ b, b < 128 →
    l.foldr (fun z acc => lmul (gen z) acc) b < 128 ∧
      elt (l.foldr (fun z acc => lmul (gen z) acc) b) = (l.map fun z => yS (gen z)).prod * elt b
  | [], b, hb => ⟨hb, by simp⟩
  | z :: l, b, hb => by
    obtain ⟨h1, h2⟩ := foldr_lmul_spec l b hb
    obtain ⟨h3, h4⟩ := lmul_spec (gen_lt z) h1
    refine ⟨h3, ?_⟩
    rw [List.foldr_cons, h4, h2, List.map_cons, List.prod_cons, mul_assoc]

theorem mulIdx_spec {a b : ℕ} (hb : b < 128) :
    mulIdx a b < 128 ∧ elt (mulIdx a b) = elt a * elt b := by
  rw [mulIdx, elt_def a]
  exact foldr_lmul_spec (path a) b hb

theorem mulTab_get {a d : ℕ} (ha : a < 128) (hd : d < 128) : (mulTab[a]!)[d]! = mulIdx a d := by
  unfold mulTab
  exact (congrArg (·[d]!) (ofFn_getElem! _ ha)).trans (ofFn_getElem! _ hd)

theorem lmulTab_get {k b : ℕ} (hk : k < 3) (hb : b < 128) : (lmulTab[k]!)[b]! = lmul k b := by
  unfold lmulTab
  exact (congrArg (·[b]!) (ofFn_getElem! _ hk)).trans (ofFn_getElem! _ hb)

theorem elt_injective {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : elt a = elt b) : a = b := by
  by_contra hab
  have h1 := sCheck_parts.2.1 a ha b hb hab
  rw [(eqA_iff (rep_eltArrs ha) (rep_eltArrs hb)).2 (congrArg Subtype.val h)] at h1
  exact Bool.noConfusion h1

theorem elt_inv {a : ℕ} (ha : a < 128) : invIdx a < 128 ∧ (elt a)⁻¹ = elt (invIdx a) := by
  obtain ⟨hlt, h0⟩ := sCheck_parts.2.2 a ha
  refine ⟨hlt, inv_eq_of_mul_eq_one_right ?_⟩
  rw [← (mulIdx_spec hlt).2, ← mulTab_get ha hlt, h0, elt_zero]

theorem gen_par_succ {k : ℕ} (hk : k < 3) : gen (k + 1) = k ∧ par (k + 1) = 0 := by
  interval_cases k <;> decide +kernel

theorem elt_succ {k : ℕ} (hk : k < 3) : elt (k + 1) = yS k := by
  rw [elt_cons (by omega) (by omega), (gen_par_succ hk).1, (gen_par_succ hk).2, elt_zero,
    mul_one]

theorem exists_elt {σ : Perm315} (hσ : σ ∈ S) : ∃ x, x < 128 ∧ (elt x : Perm315) = σ := by
  rw [S_eq] at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
    rcases hσ with rfl | rfl | rfl
    · exact ⟨1, by norm_num, by rw [elt_succ (k := 0) (by norm_num)]; rfl⟩
    · exact ⟨2, by norm_num, by rw [elt_succ (k := 1) (by norm_num)]; rfl⟩
    · exact ⟨3, by norm_num, by rw [elt_succ (k := 2) (by norm_num)]; rfl⟩
  | one => exact ⟨0, by norm_num, by rw [elt_zero]; rfl⟩
  | mul σ τ _ _ hσ hτ =>
    obtain ⟨a, -, rfl⟩ := hσ
    obtain ⟨b, hb, rfl⟩ := hτ
    exact ⟨mulIdx a b, (mulIdx_spec hb).1, by rw [(mulIdx_spec hb).2, Subgroup.coe_mul]⟩
  | inv σ _ hσ =>
    obtain ⟨a, ha, rfl⟩ := hσ
    exact ⟨invIdx a, (elt_inv ha).1, by rw [← (elt_inv ha).2, Subgroup.coe_inv]⟩

theorem elt_surjective (s : S) : ∃ x, x < 128 ∧ elt x = s := by
  obtain ⟨x, hx, h⟩ := exists_elt s.2
  exact ⟨x, hx, Subtype.ext h⟩

@[expose] noncomputable def eltEquiv : Fin 128 ≃ S :=
  Equiv.ofBijective (fun x => elt x) ⟨fun a b h => Fin.ext (elt_injective a.2 b.2 h), fun s => by
    obtain ⟨x, hx, h⟩ := elt_surjective s
    exact ⟨⟨x, hx⟩, h⟩⟩

@[expose] noncomputable def idx (s : S) : ℕ := (eltEquiv.symm s : ℕ)

theorem idx_lt (s : S) : idx s < 128 := (eltEquiv.symm s).isLt

theorem elt_idx (s : S) : elt (idx s) = s := eltEquiv.apply_symm_apply s

theorem idx_elt {x : ℕ} (hx : x < 128) : idx (elt x) = x :=
  elt_injective (idx_lt _) hx (elt_idx _)

theorem card_S : Nat.card S = 128 := by
  rw [← Nat.card_congr eltEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]


@[expose, irreducible] noncomputable def rep (i : ℕ) : Perm315 := wordPerm (cosetWord i)

theorem rep_eq (i : ℕ) : rep i = wordPerm (cosetWord i) := by rw [rep]

theorem rep_mem (i : ℕ) : rep i ∈ P := by
  rw [rep_eq]
  exact wordPerm_mem _

theorem rep_zero : rep 0 = 1 := by
  rw [rep, cosetWord, cosetWordAux]
  simp only [↓reduceIte, wordPerm_nil]

theorem repArrs_get {i : ℕ} (hi : i < 4725) : repArrs[i]! = wordArr (cosetWord i) := by
  unfold repArrs
  exact ofFn_getElem! _ hi

theorem rep_repArrs {i : ℕ} (hi : i < 4725) : Rep 315 repArrs[i]! (rep i) := by
  rw [repArrs_get hi, rep_eq]
  exact rep_wordArr _

theorem cosetCheck_parts {i j : ℕ} (hi : i < 4725) (hj : j < 2) :
    actT j i < 4725 ∧ witT j i < 128 ∧
      eqA 315 (compA 315 repArrs[i]! (letterArr j))
        (compA 315 eltArrs[witT j i]! repArrs[actT j i]!) = true := by
  have h := allLt_spec (allLt_spec cosetCheck_eq hi) hj
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rep_mul_letter {i j : ℕ} (hi : i < 4725) (hj : j < 2) :
    actT j i < 4725 ∧ witT j i < 128 ∧
      rep i * letter j = (elt (witT j i) : Perm315) * rep (actT j i) := by
  obtain ⟨h1, h2, h3⟩ := cosetCheck_parts hi hj
  exact ⟨h1, h2, eq_of_eqA (rep_compA (rep_repArrs hi) (rep_letterArr j))
    (rep_compA (rep_eltArrs h2) (rep_repArrs h1)) h3⟩

@[expose] noncomputable def tv (ki : Fin 128 × Fin 4725) : P :=
  ⟨elt ki.1 * rep ki.2, mul_mem (S_le_P (elt ki.1).2) (rep_mem _)⟩

theorem tv_coe (ki : Fin 128 × Fin 4725) : (tv ki : Perm315) = elt ki.1 * rep ki.2 := rfl

theorem tv_step (ki : Fin 128 × Fin 4725) {j : ℕ} (hj : j < 2) :
    ∃ ki' : Fin 128 × Fin 4725, (tv ki' : Perm315) = tv ki * letter j := by
  obtain ⟨h1, h2, h3⟩ := rep_mul_letter ki.2.isLt hj
  obtain ⟨hm, he⟩ := mulIdx_spec (a := ki.1) h2
  refine ⟨(⟨mulIdx ki.1 (witT j ki.2), hm⟩, ⟨actT j ki.2, h1⟩), ?_⟩
  rw [tv_coe, tv_coe, mul_assoc, h3, ← mul_assoc]
  simp only
  rw [he, Subgroup.coe_mul]

theorem tv_step_gA (ki : Fin 128 × Fin 4725) :
    ∃ ki' : Fin 128 × Fin 4725, (tv ki' : Perm315) = tv ki * gA :=
  tv_step ki (j := 0) (by norm_num)

theorem tv_step_gB (ki : Fin 128 × Fin 4725) :
    ∃ ki' : Fin 128 × Fin 4725, (tv ki' : Perm315) = tv ki * gB :=
  tv_step ki (j := 1) (by norm_num)

theorem tv_surjective : Function.Surjective tv := by
  have key : ∀ σ ∈ P, ∃ ki : Fin 128 × Fin 4725, (tv ki : Perm315) = σ := by
    intro σ hσ
    rw [P_eq] at hσ
    induction hσ using Subgroup.closure_induction_right with
    | one => exact ⟨(0, 0), by rw [tv_coe]; simp [elt_zero, rep_zero]⟩
    | mul_right x _ y hy ih =>
      obtain ⟨ki, rfl⟩ := ih
      rcases hy with rfl | rfl
      · exact tv_step_gA ki
      · exact tv_step_gB ki
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨ki, rfl⟩ := ih
      rcases hy with rfl | rfl
      · rw [gA_inv]
        exact tv_step_gA ki
      · rw [gB_inv, ← mul_assoc]
        obtain ⟨ki', h'⟩ := tv_step_gB ki
        obtain ⟨ki'', h''⟩ := tv_step_gB ki'
        exact ⟨ki'', by rw [h'', h']⟩
  intro g
  obtain ⟨ki, h⟩ := key g g.2
  exact ⟨ki, Subtype.ext h⟩

theorem tv_bijective : Function.Bijective tv :=
  tv_surjective.bijective_of_nat_card_le (by
    rw [card_P, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])

@[expose] noncomputable def decomp : P ≃ Fin 128 × Fin 4725 :=
  (Equiv.ofBijective tv tv_bijective).symm

theorem tv_decomp (g : P) : tv (decomp g) = g :=
  (Equiv.ofBijective tv tv_bijective).apply_symm_apply g

@[expose] noncomputable def repP (i : ℕ) : P := ⟨rep i, rep_mem i⟩

@[expose] noncomputable def cosetAct (i : Fin 4725) (g : P) : Fin 4725 := (decomp (repP i * g)).2

@[expose] noncomputable def factor (i : Fin 4725) (g : P) : S := elt (decomp (repP i * g)).1

theorem rep_mul_eq (i : Fin 4725) (g : P) :
    rep i * (g : Perm315) = (factor i g : Perm315) * rep (cosetAct i g) := by
  have h := congrArg Subtype.val (tv_decomp (repP i * g))
  rw [tv_coe, Subgroup.coe_mul] at h
  exact h.symm

theorem tv_injective {k k' : Fin 128} {i i' : Fin 4725}
    (h : (elt k : Perm315) * rep i = (elt k' : Perm315) * rep i') : k = k' ∧ i = i' := by
  have := tv_bijective.1 (a₁ := (k, i)) (a₂ := (k', i')) (Subtype.ext h)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem decomp_unique {i : Fin 4725} {g : P} {s : S} {k : Fin 4725}
    (h : rep i * (g : Perm315) = (s : Perm315) * rep k) : factor i g = s ∧ cosetAct i g = k := by
  have h' : (elt (decomp (repP i * g)).1 : Perm315) * rep (decomp (repP i * g)).2 =
      (elt (⟨idx s, idx_lt s⟩ : Fin 128) : Perm315) * rep k := by
    rw [show (elt ((⟨idx s, idx_lt s⟩ : Fin 128) : ℕ)) = s from elt_idx s, ← h]
    exact (rep_mul_eq i g).symm
  obtain ⟨h1, h2⟩ := tv_injective h'
  refine ⟨?_, h2⟩
  rw [factor, h1]
  exact elt_idx s

theorem cosetAct_one (i : Fin 4725) : cosetAct i 1 = i :=
  (decomp_unique (s := 1) (by simp)).2

theorem factor_one (i : Fin 4725) : factor i 1 = 1 :=
  (decomp_unique (s := 1) (k := i) (by simp)).1

theorem cosetAct_mul (i : Fin 4725) (g h : P) :
    cosetAct i (g * h) = cosetAct (cosetAct i g) h := by
  refine (decomp_unique (s := factor i g * factor (cosetAct i g) h) ?_).2
  rw [Subgroup.coe_mul, ← mul_assoc, rep_mul_eq, mul_assoc, rep_mul_eq, Subgroup.coe_mul,
    mul_assoc]

theorem factor_mul (i : Fin 4725) (g h : P) :
    factor i (g * h) = factor i g * factor (cosetAct i g) h := by
  refine (decomp_unique (k := cosetAct (cosetAct i g) h) ?_).1
  rw [Subgroup.coe_mul, ← mul_assoc, rep_mul_eq, mul_assoc, rep_mul_eq, Subgroup.coe_mul,
    mul_assoc]

@[expose] noncomputable def cosetPerm (g : P) : Equiv.Perm (Fin 4725) where
  toFun i := cosetAct i g
  invFun i := cosetAct i g⁻¹
  left_inv i := by
    change cosetAct (cosetAct i g) g⁻¹ = i
    rw [← cosetAct_mul, mul_inv_cancel, cosetAct_one]
  right_inv i := by
    change cosetAct (cosetAct i g⁻¹) g = i
    rw [← cosetAct_mul, inv_mul_cancel, cosetAct_one]

theorem cosetPerm_apply (g : P) (i : Fin 4725) : cosetPerm g i = cosetAct i g := rfl

@[expose] noncomputable def letterP (j : ℕ) : P := ⟨letter j, letter_mem j⟩

theorem cosetAct_letter (i : Fin 4725) {j : ℕ} (hj : j < 2) :
    (cosetAct i (letterP j) : ℕ) = actT j i ∧ factor i (letterP j) = elt (witT j i) := by
  obtain ⟨h1, -, h3⟩ := rep_mul_letter i.isLt hj
  have := decomp_unique (i := i) (g := letterP j) (k := ⟨actT j i, h1⟩) h3
  exact ⟨congrArg Fin.val this.2, this.1⟩

theorem actT_bijective {j : ℕ} (hj : j < 2) :
    Function.Bijective fun i : Fin 4725 =>
      (⟨actT j i, (rep_mul_letter i.isLt hj).1⟩ : Fin 4725) := by
  have he : (fun i : Fin 4725 => (⟨actT j i, (rep_mul_letter i.isLt hj).1⟩ : Fin 4725)) =
      cosetPerm (letterP j) := by
    funext i
    exact Fin.ext (cosetAct_letter i hj).1.symm
  rw [he]
  exact (cosetPerm (letterP j)).bijective

@[expose] noncomputable def incl : S →* P := Subgroup.inclusion S_le_P

@[simp] theorem incl_coe (s : S) : (incl s : Perm315) = s := Subgroup.coe_inclusion S_le_P s

theorem sDecompCheck_parts {i a : ℕ} (hi : i < 4725) (ha : a < 128) :
    pTab i a < 128 ∧ iTab i a < 4725 ∧
      eqA 315 (compA 315 repArrs[i]! eltArrs[a]!)
        (compA 315 eltArrs[pTab i a]! repArrs[iTab i a]!) = true := by
  have h := allLt_spec (allLt_spec sDecompCheck_eq hi) ha
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem decomp_elt (i : Fin 4725) {a : ℕ} (ha : a < 128) :
    ∃ (_ : pTab i a < 128) (hc : iTab i a < 4725),
      factor i (incl (elt a)) = elt (pTab i a) ∧ cosetAct i (incl (elt a)) = ⟨iTab i a, hc⟩ := by
  obtain ⟨h1, h2, h3⟩ := sDecompCheck_parts i.isLt ha
  have h := eq_of_eqA (rep_compA (rep_repArrs i.isLt) (rep_eltArrs ha))
    (rep_compA (rep_eltArrs h1) (rep_repArrs h2)) h3
  have h' : rep i * ((incl (elt a) : P) : Perm315) =
      (elt (pTab i a) : Perm315) * rep ((⟨iTab i a, h2⟩ : Fin 4725) : ℕ) := by
    rw [incl_coe]
    exact h
  exact ⟨h1, h2, decomp_unique (i := i) (g := incl (elt a)) (k := ⟨iTab i a, h2⟩) h'⟩

theorem relIndex_S_P : S.relIndex P = 4725 := by
  have h := Subgroup.relIndex_mul_card S P
  rw [inf_of_le_left S_le_P, card_S, card_P] at h
  omega

theorem card_subgroupOf_S : Nat.card (S.subgroupOf P) = 128 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_P).toEquiv, card_S]

theorem factorization_card_P : (Nat.card P).factorization 2 = 7 := by
  rw [card_P, show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 4725)]
  rfl

@[expose] noncomputable def sylowS : Sylow 2 P :=
  Sylow.ofCard (S.subgroupOf P) (by
    rw [card_subgroupOf_S, factorization_card_P]
    norm_num)

theorem coe_sylowS : (sylowS : Subgroup P) = S.subgroupOf P := Sylow.coe_ofCard _ _

theorem exists_sylow_eq_S : ∃ Q : Sylow 2 P, (Q : Subgroup P) = S.subgroupOf P :=
  ⟨sylowS, coe_sylowS⟩

@[expose] noncomputable def cosetMk (i : Fin 4725) :
    Quotient (QuotientGroup.rightRel (S.subgroupOf P)) :=
  Quotient.mk'' (repP i)

theorem cosetMk_bijective : Function.Bijective cosetMk := by
  refine ⟨fun i i' h => ?_, fun q => ?_⟩
  · have h' := Quotient.exact' h
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h'
    obtain ⟨k, hk, hke⟩ := exists_elt h'
    have : (elt (⟨k, hk⟩ : Fin 128) : Perm315) * rep i =
        (elt (0 : Fin 128) : Perm315) * rep i' := by
      simp only [Fin.val_zero, elt_zero, Subgroup.coe_one, one_mul]
      rw [show ((elt ((⟨k, hk⟩ : Fin 128) : ℕ)) : Perm315) = _ from hke]
      simp [repP]
    exact (tv_injective this).2
  · induction q using Quotient.inductionOn' with
    | h g =>
      refine ⟨(decomp g).2, Quotient.sound' ?_⟩
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
      have hg := congrArg Subtype.val (tv_decomp g)
      rw [tv_coe] at hg
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hg]
      simp [repP]

end CFSG.ComponentClassification.J2Cover.Models
