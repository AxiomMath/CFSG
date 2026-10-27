module

public import CFSG.Certificates.Kernel.FixBoundK.FixMath
public import CFSG.Certificates.Kernel.FixBoundK.TrivSound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu

@[expose] def xorB (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xorB f n ^^ f n

theorem xorB_add (f : Nat → Bool) (k : Nat) : ∀ m,
    xorB f (k + m) = (xorB f k ^^ xorB (fun i => f (k + i)) m)
  | 0 => by simp [xorB]
  | m + 1 => by
    rw [← Nat.add_assoc]
    simp only [xorB]
    rw [xorB_add f k m, Bool.xor_assoc]

theorem xorB_xor (f g : Nat → Bool) : ∀ n,
    xorB (fun i => f i ^^ g i) n = (xorB f n ^^ xorB g n)
  | 0 => rfl
  | n + 1 => by
    simp only [xorB]
    rw [xorB_xor f g n]
    have h4 : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact h4 _ _ _ _

theorem xorB_congr {f g : Nat → Bool} : ∀ {n}, (∀ i < n, f i = g i) → xorB f n = xorB g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [xorB]
    rw [xorB_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem xorB_fold (k x : Nat) : xorB (x ^^^ x >>> k).testBit k = xorB x.testBit (k + k) := by
  have hf : (x ^^^ x >>> k).testBit = fun i => x.testBit i ^^ x.testBit (k + i) := by
    funext i
    simp [Nat.testBit_xor, Nat.testBit_shiftRight]
  rw [hf, xorB_xor, xorB_add]

theorem xorB_cast (f : Nat → Bool) : ∀ n,
    ((xorB f n).toNat : ZMod 2) = ∑ i ∈ Finset.range n, ((f i).toNat : ZMod 2)
  | 0 => by simp [xorB]
  | n + 1 => by
    rw [xorB, Finset.sum_range_succ, ← xorB_cast f n]
    generalize xorB f n = a
    generalize f n = b
    cases a <;> cases b <;> decide

theorem par24_def (x : Nat) : par24 x =
    (fun c => (c ^^^ (c >>> 1 ^^^ c >>> 2)) &&& 1)
      ((fun b => b ^^^ b >>> 3) ((fun a => a ^^^ a >>> 6)
        ((fun y => y ^^^ y >>> 12) (x &&& (2 ^ 24 - 1))))) := rfl

theorem par24_eq (x : Nat) : par24 x = (xorB x.testBit 24).toNat := by
  have h1 : ∀ c : Nat, (c ^^^ (c >>> 1 ^^^ c >>> 2)) &&& 1 = (xorB c.testBit 3).toNat := by
    intro c
    have e : xorB c.testBit 3 = (c ^^^ (c >>> 1 ^^^ c >>> 2)).testBit 0 := by
      simp only [xorB, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.false_xor, Nat.add_zero,
        Bool.xor_assoc]
    rw [e, Nat.toNat_testBit, Nat.and_one_is_mod, Nat.pow_zero, Nat.div_one]
  rw [par24_def]
  dsimp only
  rw [h1]
  simp only [xorB_fold, Nat.reduceAdd]
  congr 1
  exact xorB_congr fun i hi => by
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hi]

theorem par24_lt (x : Nat) : par24 x < 2 := by
  rw [par24_eq]
  cases xorB x.testBit 24 <;> decide

theorem par24_and_omK (x : Nat) : par24 (x &&& omK) = par24 x := by
  rw [par24_eq, par24_eq]
  congr 1
  exact xorB_congr fun i hi => by
    have e : omK = 2 ^ 24 - 1 := rfl
    rw [Nat.testBit_and, e, Nat.testBit_two_pow_sub_one]
    simp [hi]

theorem par24_and_cast (a b : Nat) :
    ((par24 (a &&& b) : Nat) : ZMod 2) = bvec 24 a ⬝ᵥ bvec 24 b := by
  rw [par24_eq, xorB_cast, dotProduct, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [bvec, Nat.testBit_and]
  cases a.testBit k <;> cases b.testBit k <;> simp

theorem dot_Ω_of_par24 {f : Nat} (h : par24 f = 0) : bvec 24 f ⬝ᵥ Ω = 0 := by
  rw [← bvec_omK, ← par24_and_cast, par24_and_omK, h]
  rfl

theorem beqT (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem rowS_iff (f i : Nat) : ∀ (ws : List Nat) (j₀ : Nat), rowS f i ws j₀ = true ↔
    ∀ j < ws.length, par24 (f &&& ws.getD j 0) = if i = j₀ + j then 1 else 0
  | [], _ => iff_of_true rfl fun j hj => absurd hj (Nat.not_lt_zero j)
  | w :: ws, j₀ => by
    change Bool.rec (motive := fun _ => Bool) false (rowS f i ws (Nat.succ j₀))
      (Nat.beq (par24 (f &&& w)) (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq i j₀))) = true ↔ _
    rw [TrivSound.bAnd_eq, Bool.and_eq_true, TrivSound.nIf_beq, beqT, rowS_iff f i ws]
    constructor
    · rintro ⟨h0, h1⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j =>
        have := h1 j (by simpa using hj)
        rw [List.getD_cons_succ, this]
        congr 1
        apply propext
        omega
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      rw [List.getD_cons_succ] at this
      rw [this]
      congr 1
      apply propext
      omega

theorem dualS_iff (ws : List Nat) : ∀ (fs : List Nat) (i₀ : Nat), dualS ws fs i₀ = true ↔
    i₀ + fs.length = ws.length ∧ ∀ i < fs.length, rowS (fs.getD i 0) (i₀ + i) ws 0 = true
  | [], i₀ => by
    change Nat.beq i₀ (lenS ws) = true ↔ _
    rw [beqT, TrivSound.lenS_eq]
    simp
  | f :: fs, i₀ => by
    change Bool.rec (motive := fun _ => Bool) false (dualS ws fs (Nat.succ i₀))
      (rowS f i₀ ws 0) = true ↔ _
    rw [TrivSound.bAnd_eq, Bool.and_eq_true, dualS_iff ws fs]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
      cases i with
      | zero => simpa using h0
      | succ i =>
        rw [List.getD_cons_succ, ← Nat.add_assoc, Nat.add_right_comm]
        exact h2 i (by simpa using hi)
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h2 0 (by simp), by simp only [List.length_cons] at h1; omega,
        fun i hi => ?_⟩
      have := h2 (i + 1) (by simpa using hi)
      rw [List.getD_cons_succ] at this
      rwa [Nat.succ_add, ← Nat.add_succ]

theorem dualS_spec {ws fs : List Nat} (h : dualS ws fs 0 = true) :
    fs.length = ws.length ∧ ∀ i < ws.length, ∀ j < ws.length,
      par24 (fs.getD i 0 &&& ws.getD j 0) = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := (dualS_iff ws fs 0).1 h
  rw [Nat.zero_add] at h1
  refine ⟨h1, fun i hi j hj => ?_⟩
  have := (rowS_iff _ _ ws 0).1 (h2 i (by omega)) j hj
  simpa using this

theorem length_le_finrank_of_dualS {V : Submodule (ZMod 2) C} {ws fs : List Nat}
    (hdual : dualS ws fs 0 = true) (hmem : ∀ w ∈ ws, bvec 24 w ∈ C)
    (hV : ∀ (w : Nat) (hw : w ∈ ws), (⟨bvec 24 w, hmem w hw⟩ : C) ∈ V) :
    ws.length ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨-, hd⟩ := dualS_spec hdual
  have hmemw : ∀ j : Fin ws.length, ws.getD j 0 ∈ ws := by
    intro j
    rw [List.getD_eq_getElem _ _ j.2]
    exact List.getElem_mem j.2
  let w : Fin ws.length → V := fun j =>
    ⟨⟨bvec 24 (ws.getD j 0), hmem _ (hmemw j)⟩, hV _ (hmemw j)⟩
  let L : Fin ws.length → C →ₗ[ZMod 2] ZMod 2 := fun i =>
    ((dotProductEquiv (ZMod 2) (Fin 24)) (bvec 24 (fs.getD i 0))).comp C.subtype
  have hLi : ∀ (i j : Fin ws.length), L i (w j : C) = if i = j then 1 else 0 := by
    intro i j
    simp only [L, LinearMap.comp_apply, Submodule.coe_subtype]
    rw [dotProductEquiv_apply_apply]
    change bvec 24 (fs.getD i 0) ⬝ᵥ bvec 24 (ws.getD j 0) = _
    rw [← par24_and_cast, hd i i.2 j j.2]
    by_cases hij : i = j
    · simp [hij]
    · have hne : (i : Nat) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hne]
  have hli : LinearIndependent (ZMod 2) w := by
    refine (Fintype.linearIndependent_iff (R := ZMod 2) (M := V) (v := w)).2 ?_
    intro g hg i
    have h0 : L i (V.subtype (∑ j, g j • w j)) = 0 := by simp [hg]
    have h2 : L i (V.subtype (∑ j, g j • w j)) = ∑ j, g j • L i ((w j : V) : C) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]; rfl
    rw [h2] at h0
    have h3 : ∑ j : Fin ws.length, g j • L i ((w j : V) : C) = g i := by
      rw [Finset.sum_eq_single i]
      · rw [hLi i i, if_pos rfl, smul_eq_mul, mul_one]
      · intro j _ hji
        rw [hLi i j, if_neg (Ne.symm hji), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h3] at h0
    exact h0
  simpa using LinearIndependent.fintype_card_le_finrank (b := w) hli

theorem dot_actM (g : Nat) : ∀ (B : List Nat) (x : Nat),
    bvec 24 g ⬝ᵥ bvec 24 (actM B x) = ∑ t ∈ Finset.range B.length,
      (if x.testBit t then bvec 24 g ⬝ᵥ bvec 24 (B.getD t 0) else 0)
  | [], x => by simp [actM, bvec_zero]
  | b :: B, x => by
    rw [actM, bvec_xor, dotProduct_add, dot_actM g B (x / 2), List.length_cons,
      Finset.sum_range_succ']
    have e : ∀ t, (x / 2).testBit t = x.testBit (t + 1) := fun t => (Nat.testBit_succ x t).symm
    simp only [e, List.getD_cons_succ, List.getD_cons_zero]
    have hA : bvec 24 g ⬝ᵥ bvec 24 (if x % 2 = 1 then b else 0) =
        if x.testBit 0 = true then bvec 24 g ⬝ᵥ bvec 24 b else 0 := by
      rw [Nat.testBit_zero]
      by_cases hx : x % 2 = 1
      · rw [if_pos hx, if_pos (decide_eq_true hx)]
      · rw [if_neg hx, if_neg (fun h => hx (of_decide_eq_true h)), bvec_zero, dotProduct_zero]
    rw [hA, add_comm]

theorem dot_actS_dual {B gs : List Nat} (hd : dualS B gs 0 = true) {i : Nat} (hi : i < B.length)
    (x : Nat) : bvec 24 (gs.getD i 0) ⬝ᵥ bvec 24 (actS B x) = if x.testBit i then 1 else 0 := by
  obtain ⟨-, hdd⟩ := dualS_spec hd
  rw [actS_eq, dot_actM, Finset.sum_eq_single i]
  · rw [← par24_and_cast, hdd i hi i hi, if_pos rfl]
    simp
  · intro t ht hti
    rw [← par24_and_cast, hdd i hi t (Finset.mem_range.1 ht), if_neg (Ne.symm hti)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 hi) h

theorem actS_bvec_inj {B gs : List Nat} (hd : dualS B gs 0 = true) {x y : Nat}
    (hx : x < 2 ^ B.length) (hy : y < 2 ^ B.length) (h : bvec 24 (actS B x) = bvec 24 (actS B y)) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < B.length
  · have e := dot_actS_dual hd hi x
    rw [h, dot_actS_dual hd hi y] at e
    cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> simp_all
  · have h1 : 2 ^ B.length ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h1),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy h1)]

theorem headS_eq {α : Type} (d : α) (l : List α) : headS d l = l.getD 0 d := by
  cases l <;> rfl

theorem tailS_getD {α : Type} (d : α) (l : List α) (i : Nat) :
    (tailS l).getD i d = l.getD (i + 1) d := by
  cases l <;> simp [tailS]

theorem testBit_par24 (x n : Nat) : (par24 x).testBit n = (decide (n = 0) && (par24 x).testBit 0) := by
  have h := par24_lt x
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_one_ne_zero, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.le_self_pow (Nat.add_one_ne_zero n) 2))

theorem testBit_parV (d : Nat) : ∀ (fl : List Nat) (s₀ n : Nat), (parV fl d s₀).testBit n =
    (decide (s₀ ≤ n) && (par24 (fl.getD (n - s₀) 0 &&& d)).testBit 0)
  | [], s₀, n => by
    change Nat.testBit 0 n = _
    have e : par24 (0 &&& d) = 0 := by rw [Nat.zero_and]; rfl
    rw [Nat.zero_testBit, List.getD_nil, e, Nat.zero_testBit, Bool.and_false]
  | f :: fl, s₀, n => by
    change (Nat.shiftLeft (par24 (f &&& d)) s₀ ||| parV fl d (Nat.succ s₀)).testBit n = _
    rw [Nat.testBit_or, testBit_parV d fl (Nat.succ s₀) n]
    change (((par24 (f &&& d)) <<< s₀).testBit n || _) = _
    rw [Nat.testBit_shiftLeft, testBit_par24]
    by_cases h1 : n < s₀
    · have h2 : ¬ s₀ ≤ n := by omega
      have h3 : ¬ Nat.succ s₀ ≤ n := by omega
      simp [h2, h3]
    · by_cases h4 : n = s₀
      · subst h4
        simp
      · have h5 : Nat.succ s₀ ≤ n := by omega
        have h6 : n - s₀ = (n - Nat.succ s₀) + 1 := by omega
        have h7 : n - s₀ ≠ 0 := by omega
        simp [h5, h6, Nat.le_of_succ_le h5]

theorem toNat_testBit_par24 (x : Nat) : ((par24 x).testBit 0).toNat = par24 x := by
  rw [Nat.toNat_testBit, Nat.pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt (par24_lt x)

theorem ycolS_cast (y s : Nat) : ∀ (gens : List (List Nat)) (yfT : List (List Nat)),
    (((ycolS gens yfT y).testBit s).toNat : ZMod 2) = ∑ i ∈ Finset.range gens.length,
      ((par24 ((yfT.getD i []).getD s 0 &&& (permS (gens.getD i []) y ^^^ y)) : Nat) : ZMod 2)
  | [], _ => by simp [ycolS]
  | g :: gens, yfT => by
    change (((Nat.xor (withN (Nat.xor (permS g y) y) (fun d => parV (headS [] yfT) d 0))
      (ycolS gens (tailS yfT) y)).testBit s).toNat : ZMod 2) = _
    rw [withN_eq]
    change ((((parV (headS [] yfT) (permS g y ^^^ y) 0) ^^^
      (ycolS gens (tailS yfT) y)).testBit s).toNat : ZMod 2) = _
    rw [Nat.testBit_xor, List.length_cons, Finset.sum_range_succ']
    have ih := ycolS_cast y s gens (tailS yfT)
    simp only [tailS_getD] at ih
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← ih, testBit_parV, headS_eq, Nat.sub_zero]
    simp only [Nat.zero_le, decide_true, Bool.true_and]
    rw [add_comm, ← toNat_testBit_par24]
    generalize (par24 _).testBit 0 = a
    generalize (ycolS gens (tailS yfT) y).testBit s = b
    cases a <;> cases b <;> decide

theorem ysChk_iff (gens : List (List Nat)) (yfT : List (List Nat)) : ∀ (ys : List Nat) (t₀ : Nat),
    ysChk gens yfT ys t₀ = true ↔ ∀ t < ys.length, ycolS gens yfT (ys.getD t 0) = 2 ^ (t₀ + t)
  | [], _ => iff_of_true rfl fun t ht => absurd ht (Nat.not_lt_zero t)
  | y :: ys, t₀ => by
    change Bool.rec (motive := fun _ => Bool) false (ysChk gens yfT ys (Nat.succ t₀))
      (Nat.beq (ycolS gens yfT y) (Nat.shiftLeft 1 t₀)) = true ↔ _
    rw [TrivSound.bAnd_eq, Bool.and_eq_true, beqT, ysChk_iff gens yfT ys]
    have e : Nat.shiftLeft 1 t₀ = 2 ^ t₀ := Nat.one_shiftLeft t₀
    rw [e]
    constructor
    · rintro ⟨h0, h1⟩ t ht
      cases t with
      | zero => simpa using h0
      | succ t =>
        rw [List.getD_cons_succ, h1 t (by simpa using ht)]
        congr 1
        omega
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun t ht => ?_⟩
      have := h (t + 1) (by simpa using ht)
      rw [List.getD_cons_succ] at this
      rw [this]
      congr 1
      omega

theorem mem_appS {x : Nat} : ∀ {l₁ l₂ : List Nat}, x ∈ appS l₁ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
  | [], _ => by simp [appS]
  | y :: l, l₂ => by
    change x ∈ y :: appS l l₂ ↔ _
    rw [List.mem_cons, mem_appS, List.mem_cons, or_assoc]

@[expose] def ysFun (σ : Nat → AutPerm) (n : Nat) (yfT : List (List Nat)) (m : Nat) :
    C →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearMap.pi fun s => ∑ i ∈ Finset.range n,
    ((dotProductEquiv (ZMod 2) (Fin 24)) (bvec 24 ((yfT.getD i []).getD s 0))).comp
      (C.subtype ∘ₗ ((permC (σ i)).toLinearMap - LinearMap.id))

theorem ysFun_apply (σ : Nat → AutPerm) (n : Nat) (yfT : List (List Nat)) (m : Nat) (c : C)
    (s : Fin m) : ysFun σ n yfT m c s = ∑ i ∈ Finset.range n,
      bvec 24 ((yfT.getD i []).getD s 0) ⬝ᵥ ((permC (σ i) c - c : C) : Fin 24 → ZMod 2) := by
  simp only [ysFun, LinearMap.pi_apply]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    Submodule.coe_subtype, dotProductEquiv_apply_apply]

theorem fixModΩ_cover {gens : List (List Nat)} {B gs ys : List Nat} {yfT : List (List Nat)}
    (hgen : ∀ g ∈ gens, ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) g)
    (hlen : B.length + ys.length = 12) (hsyn : ∀ y ∈ appS B ys, synS y = 0)
    (hfix : ∀ g ∈ gens, ∀ b ∈ B, fixS g b = true) (hd : dualS B gs 0 = true)
    (hpar : ∀ l ∈ yfT, ∀ f ∈ l, par24 f = 0) (hys : ysChk gens yfT ys 0 = true)
    {c : C} (hc : c ∈ fixModΩ (Subgroup.closure (GenSet gens))) :
    ∃ j < 2 ^ B.length, bvec 24 (actS B j) = (c : Fin 24 → ZMod 2) := by
  classical
  set P := Subgroup.closure (GenSet gens)
  have hgetD : ∀ i < gens.length, gens.getD i [] ∈ gens := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hσ : ∀ i, ∃ σ : AutPerm, i < gens.length → ImgL (σ : Equiv.Perm (Fin 24)) (gens.getD i []) := by
    intro i
    by_cases hi : i < gens.length
    · obtain ⟨σ, hσ⟩ := hgen _ (hgetD i hi)
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose σ hσ using hσ
  have hσP : ∀ i < gens.length, σ i ∈ P := fun i hi =>
    Subgroup.subset_closure ⟨_, hgetD i hi, hσ i hi⟩
  let Φ := ysFun σ gens.length yfT ys.length
  have hker : fixModΩ P ≤ LinearMap.ker Φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext s
    rw [ysFun_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rcases mem_ΩLine_iff.1 (hx (σ i) (hσP i hi')) with h0 | hΩ
    · rw [h0]
      simp
    · rw [hΩ]
      change _ ⬝ᵥ Ω = 0
      apply dot_Ω_of_par24
      by_cases hl : i < yfT.length
      · by_cases hs : (s : Nat) < (yfT.getD i []).length
        · apply hpar (yfT.getD i [])
          · rw [List.getD_eq_getElem _ _ hl]
            exact List.getElem_mem hl
          · rw [List.getD_eq_getElem _ _ hs]
            exact List.getElem_mem hs
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hs)]
          rfl
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hl), List.getD_nil]
        rfl
  have hysC : ∀ t < ys.length, bvec 24 (ys.getD t 0) ∈ C := fun t ht => by
    rw [← synS_eq_zero_iff]
    apply hsyn
    rw [mem_appS, List.getD_eq_getElem _ _ ht]
    exact Or.inr (List.getElem_mem ht)
  have himg : ∀ t : Fin ys.length, Φ ⟨bvec 24 (ys.getD t 0), hysC t t.2⟩ = Pi.single t 1 := by
    intro t
    funext s
    rw [ysFun_apply]
    have hsum : ∀ i ∈ Finset.range gens.length,
        bvec 24 ((yfT.getD i []).getD s 0) ⬝ᵥ
          ((permC (σ i) ⟨bvec 24 (ys.getD t 0), hysC t t.2⟩ -
            ⟨bvec 24 (ys.getD t 0), hysC t t.2⟩ : C) : Fin 24 → ZMod 2) =
        ((par24 ((yfT.getD i []).getD s 0 &&&
          (permS (gens.getD i []) (ys.getD t 0) ^^^ ys.getD t 0)) : Nat) : ZMod 2) := by
      intro i hi
      rw [par24_and_cast, bvec_permS_xor (hσ i (Finset.mem_range.1 hi))]
    rw [Finset.sum_congr rfl hsum, ← ycolS_cast, (ysChk_iff gens yfT ys 0).1 hys t t.2,
      Nat.zero_add, Nat.testBit_two_pow]
    by_cases hst : s = t
    · subst hst
      simp
    · have hne : (t : Nat) ≠ s := fun h => hst (Fin.ext h.symm)
      simp [hne, Pi.single_apply, hst]
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨∑ t, v t • ⟨bvec 24 (ys.getD t 0), hysC t t.2⟩, ?_⟩
    rw [map_sum]
    simp only [map_smul, himg]
    funext s
    simp [Finset.sum_apply, Pi.single_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_C] at hrk
  have hdim : Module.finrank (ZMod 2) (fixModΩ P) ≤ B.length := by
    have := Submodule.finrank_mono hker
    omega
  have hcard : Nat.card (fixModΩ P) ≤ 2 ^ B.length := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  have hB : ∀ b ∈ B, synS b = 0 := fun b hb => hsyn b (mem_appS.2 (Or.inl hb))
  let f : Fin (2 ^ B.length) → fixModΩ P := fun j =>
    ⟨⟨bvec 24 (actS B j), (actS_mem_fixModΩ hB hfix j).fst⟩, (actS_mem_fixModΩ hB hfix j).snd⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun x : fixModΩ P => ((x : C) : Fin 24 → ZMod 2)) hab
    exact Fin.ext (actS_bvec_inj hd a.2 b.2 h)
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    have e : Nat.card (Fin (2 ^ B.length)) = 2 ^ B.length :=
      Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
    rw [e]
    exact hcard
  obtain ⟨j, hj⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨j, j.2, congrArg (fun x : fixModΩ P => ((x : C) : Fin 24 → ZMod 2)) hj⟩

end CFSG.KC.FixBoundK

end
