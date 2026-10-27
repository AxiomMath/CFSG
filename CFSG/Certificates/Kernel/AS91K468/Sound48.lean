module

public import Certificates.Data.Kernel.AS91K468.K48
public import CFSG.Certificates.Kernel.AS91K468.Sound46

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.Quasithin.H13.AS91.Two (app7 mul7 mk7 id7 ok7 aPart enum7 closed7 fix7 fixEb res6 s48
  c3List b7List itList pbar t7List t7el tOrbit ncOrbit ncGens48 stabGens48 s0Mask d7Gens r7Gens
  wit48 crdOK48 stabOK48 c3OK48 iOK48 tOK48 fusOK48 orbOK48 ok48 lam0 idA q0c stabWords48 i7List
  omList)

theorem un7_pk7 {a0 a1 a2 a3 a4 a5 a6 : ℕ} (h0 : a0 < 128) (h1 : a1 < 128) (h2 : a2 < 128)
    (h3 : a3 < 128) (h4 : a4 < 128) (h5 : a5 < 128) (h6 : a6 < 128) :
    un7 (pk7 a0 a1 a2 a3 a4 a5 a6) = [a0, a1, a2, a3, a4, a5, a6] := by
  simp only [un7, pk7, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem pk7_lt {a0 a1 a2 a3 a4 a5 a6 : ℕ} (h0 : a0 < 128) (h1 : a1 < 128) (h2 : a2 < 128)
    (h3 : a3 < 128) (h4 : a4 < 128) (h5 : a5 < 128) (h6 : a6 < 128) :
    pk7 a0 a1 a2 a3 a4 a5 a6 < 2 ^ 49 := by
  simp only [pk7]
  omega

theorem un7_inj {a b : ℕ} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49) (h : un7 a = un7 b) : a = b := by
  simp only [un7, List.cons.injEq, and_true] at h
  omega

theorem beq7 {a b : ℕ} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49) :
    (unpack7 a == unpack7 b) = Nat.beq a b := by
  rw [← nat_beq]
  by_cases h : a = b
  · subst h
    simp
  · rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne]
    intro e
    exact h (un7_inj ha hb (congrArg Array.toList e))

theorem unpack7_inj {a b : ℕ} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49) (h : unpack7 a = unpack7 b) :
    a = b := un7_inj ha hb (congrArg Array.toList h)

theorem ite_xor (n j acc a : ℕ) :
    (if n.testBit j = true then acc ^^^ a else acc) = acc ^^^ a * (n / 2 ^ j % 2) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h
  · simp [h]
  · simp [h]

theorem app7S (X n : ℕ) : app7 (unpack7 X) n = app7Q X n := by
  have hr : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  rw [app7, hr]
  simp only [List.foldl_cons, List.foldl_nil, ite_xor]
  rfl

theorem term_lt (a b : ℕ) : a % 128 * (b % 2) < 2 ^ 7 := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h]
    omega
  · rw [h]
    omega

theorem app7Q_lt (X n : ℕ) : app7Q X n < 128 := by
  rw [app7Q]
  change _ < 2 ^ 7
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.two_pow_pos 7)
    (term_lt X (n / 1))) (term_lt (X / 128) (n / 2))) (term_lt (X / 16384) (n / 4)))
    (term_lt (X / 2097152) (n / 8))) (term_lt (X / 268435456) (n / 16)))
    (term_lt (X / 34359738368) (n / 32))) (term_lt (X / 4398046511104) (n / 64))

theorem mul7S (X Y : ℕ) : mul7 (unpack7 X) (unpack7 Y) = unpack7 (mul7Q X Y) := by
  have e : unpack7 (mul7Q X Y) = [app7Q X (Y % 128), app7Q X (Y / 128 % 128),
      app7Q X (Y / 16384 % 128), app7Q X (Y / 2097152 % 128), app7Q X (Y / 268435456 % 128),
      app7Q X (Y / 34359738368 % 128), app7Q X (Y / 4398046511104 % 128)].toArray := by
    rw [mul7Q, unpack7, un7_pk7 (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _)
      (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _)]
  rw [e, mul7]
  change (un7 Y).toArray.map (app7 (unpack7 X)) = _
  rw [List.map_toArray]
  simp only [un7, List.map_cons, List.map_nil, app7S]

theorem mul7Q_lt (X Y : ℕ) : mul7Q X Y < 2 ^ 49 :=
  pk7_lt (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _) (app7Q_lt _ _)
    (app7Q_lt _ _) (app7Q_lt _ _)

theorem getD_lt64 {A : List ℕ} (hA : ∀ x ∈ A, x < 64) (i : ℕ) : A.getD i 0 < 64 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : A[i]? with _ | a
  · simp
  · exact hA a (List.mem_of_getElem? h)

theorem mk7S (l : ℕ) {A : List ℕ} (hA : ∀ x ∈ A, x < 64) : mk7 l A = unpack7 (mk7Q l A) := by
  have g := getD_lt64 hA
  have g0 := g 0
  have g1 := g 1
  have g2 := g 2
  have g3 := g 3
  have g4 := g 4
  have g5 := g 5
  rw [mk7Q, unpack7, un7_pk7 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)]
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  simp only [mk7, hr, List.map_cons, List.map_nil, Nat.shiftRight_eq_div_pow]
  norm_num

theorem mk7Q_lt (l : ℕ) {A : List ℕ} (hA : ∀ x ∈ A, x < 64) : mk7Q l A < 2 ^ 49 := by
  have g := getD_lt64 hA
  have g0 := g 0
  have g1 := g 1
  have g2 := g 2
  have g3 := g 3
  have g4 := g 4
  have g5 := g 5
  exact pk7_lt (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem ok7_unpack7 (X : ℕ) : ok7 (unpack7 X) = true := by
  simp [ok7, unpack7, un7, Nat.mod_lt]

theorem contains7 {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 49) {y : ℕ} (hy : y < 2 ^ 49) :
    (L.map unpack7).contains (unpack7 y) = L.contains y := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← unpack7_inj (hL x hx) hy e]
  · exact fun h => ⟨y, h, rfl⟩

theorem dedup7 {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 49) (h : nodupP X = true) :
    (X.map unpack7).dedup = X.map unpack7 := by
  have hn : (X.map unpack7).Nodup :=
    List.Nodup.map_on (fun x hx y hy e => unpack7_inj (hX x hx) (hX y hy) e) ((nodupP_iff X).1 h)
  exact List.dedup_eq_self.2 hn

theorem dedup7S {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 49) (n : ℕ) (h1 : nodupP X = true)
    (h2 : Nat.beq X.length n = true) : ((X.map unpack7).dedup.length == n) = true := by
  rw [dedup7 hX h1, List.length_map, nat_beq, h2]

theorem filter_mapG {α β : Type} {L : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ x ∈ L, p (f x) = q x) : (L.map f).filter p = (L.filter q).map f := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => h x hx

theorem id7_eq : id7 = unpack7 one7 := by decide +kernel

theorem one7_lt : one7 < 2 ^ 49 := by decide +kernel

theorem enum7S (gs : List ℕ) :
    enum7 (gs.map unpack7) = (enum7Q gs).map unpack7 ∧ ∀ q ∈ enum7Q gs, q < 2 ^ 49 := by
  have hf : ∀ q, q < 2 ^ 49 →
      (((gs.map unpack7).map fun g x => mul7 x g).map fun f => f (unpack7 q)) =
        ((gs.map fun g x => mul7Q x g).map fun f => f q).map unpack7 := by
    intro q _
    simp only [List.map_map]
    exact List.map_congr_left fun g _ => mul7S q g
  have hd : ∀ q, q < 2 ^ 49 → ∀ f ∈ gs.map (fun g x => mul7Q x g), f q < 2 ^ 49 := by
    intro q _ f hf'
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hf'
    exact mul7Q_lt _ _
  have hk : ∀ a b : ℕ, a < 2 ^ 49 → b < 2 ^ 49 →
      ((fun x : Array ℕ => x) (unpack7 a) == (fun x : Array ℕ => x) (unpack7 b)) = (a == b) :=
    fun a b ha hb => by rw [nat_beq]; exact beq7 ha hb
  have hs : SRel unpack7 (fun x : Array ℕ => x) (· < 2 ^ 49)
      ((∅ : Std.HashSet (Array ℕ)).insert (unpack7 one7)) (insP (.tip []) one7) := by
    intro q hq
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty,
      hk _ _ one7_lt hq]
  have := bfsClosure_N unpack7 (fun x : Array ℕ => x) (· < 2 ^ 49) hk _ _ hf hd 100000
    [one7] [] _ _ (fun q hq => by rw [List.mem_singleton.1 hq]; exact one7_lt) (by simp) hs
  rw [enum7, id7_eq]
  exact this

theorem closed7S (gs X : List ℕ) (hX : ∀ q ∈ X, q < 2 ^ 49) :
    closed7 (gs.map unpack7) (X.map unpack7) = closed7Q gs X := by
  simp only [closed7, closed7Q]
  refine all_mapL fun x _ => all_mapL fun g _ => ?_
  rw [Std.HashSet.contains_ofList, mul7S, contains7 hX (mul7Q_lt _ _), memP_ofListP]

theorem st48_lt : ∀ w ∈ stabWords48, ∀ i ∈ w, i < g13Q.length := by decide +kernel

theorem stabGens48_eq (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA) :
    stabGens48 () = st48Q.map unpackA := by
  rw [stabGens48, hg, st48Q, List.map_map]
  exact List.map_congr_left fun w hw => wordRowsS g13Q w (st48_lt w hw)

theorem res6S (x : ℕ) : res6 (unpackA x) = res6Q x := by
  simp only [res6, res6Q, appNS]

theorem s48Of_eq (gs : List ℕ) : ((enumGrp (gs.map unpackA)).map res6).dedup = s48Of (enumQ gs) := by
  rw [enumS, List.map_map, s48Of]
  congr 1
  exact List.map_congr_left fun x _ => res6S x

theorem c3Of_eq (SA : List (List ℕ)) (hA : ∀ A ∈ SA, ∀ x ∈ A, x < 64) :
    SA.flatMap (fun A => (List.range 64).map fun l => mk7 l A) = (c3Of SA).map unpack7 := by
  rw [c3Of, List.map_flatMap]
  refine List.flatMap_congr fun A hA' => ?_
  rw [List.map_map]
  exact List.map_congr_left fun l _ => mk7S l (hA A hA')

theorem c3Of_lt (SA : List (List ℕ)) (hA : ∀ A ∈ SA, ∀ x ∈ A, x < 64) :
    ∀ q ∈ c3Of SA, q < 2 ^ 49 := by
  intro q hq
  rw [c3Of, List.mem_flatMap] at hq
  obtain ⟨A, hA', hq⟩ := hq
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hq
  exact mk7Q_lt l (hA A hA')

theorem b7Of_eq (C : List ℕ) :
    ((C.map unpack7).filter fun X => i7List.all fun v => app7 X v == v) = (b7Of C).map unpack7 := by
  rw [b7Of]
  refine filter_mapG (q := fun X => i7List.all fun v => Nat.beq (app7Q X v) v) fun x _ => ?_
  refine allc fun v _ => ?_
  rw [app7S, nat_beq]

theorem s48_eq (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA) :
    s48 () = s48Of (enumQ st48Q) := by
  rw [s48, stabGens48_eq hg, s48Of_eq]

theorem idA_lt : ∀ x ∈ idA, x < 64 := by decide +kernel

theorem t7el_eq : t7el = unpack7 t7Q := by
  rw [t7el, t7Q, ← mk7S 10 idA_lt]
  rfl

theorem t7Q_lt : t7Q < 2 ^ 49 := mk7Q_lt 10 idA_lt

theorem s0Mask_eq : s0Mask () = s0M := rfl

theorem testBit_or_one_shiftLeft (a k y : ℕ) :
    (a ||| 1 <<< k).testBit y = (a.testBit y || decide (k = y)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem foldl_img_testBit (m y : ℕ) (f : ℕ → ℕ) : ∀ (L : List ℕ) (a : ℕ),
    (L.foldl (fun acc x => if m.testBit x then acc ||| 1 <<< f x else acc) a).testBit y = true ↔
      a.testBit y = true ∨ ∃ x ∈ L, m.testBit x = true ∧ f x = y
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, foldl_img_testBit m y f L]
    by_cases hx : m.testBit x = true
    · rw [if_pos hx, testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · rintro ((h | h) | ⟨z, hz, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, hx, h⟩
        · exact Or.inr ⟨z, List.mem_cons_of_mem x hz, h⟩
      · rintro (h | ⟨z, hz, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact Or.inl (Or.inr h.2)
          · exact Or.inr ⟨z, hz, h⟩
    · rw [if_neg hx]
      constructor
      · rintro (h | ⟨z, hz, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨z, List.mem_cons_of_mem x hz, h⟩
      · rintro (h | ⟨z, hz, h⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact absurd h.1 hx
          · exact Or.inr ⟨z, hz, h⟩

theorem imgS_zero (A : List ℕ) (m b acc : ℕ) :
    imgS A 0 m b acc = if m = 0 then acc else acc ||| 1 <<< mvNR A b := by
  by_cases h : m = 0
  · subst h
    rfl
  · rw [if_neg h]
    have e : Nat.beq m 0 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    change Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq m 0) = _
    rw [e]
    rfl

theorem imgS_succ (A : List ℕ) (d m b acc : ℕ) :
    imgS A (d + 1) m b acc = if m = 0 then acc else
      imgS A d (m >>> 2 ^ d) (b + 2 ^ d) (imgS A d (m % 2 ^ 2 ^ d) b acc) := by
  by_cases h : m = 0
  · subst h
    rfl
  · rw [if_neg h]
    have e : Nat.beq m 0 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    change Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq m 0) = _
    rw [e]
    rfl

theorem imgS_testBit (A : List ℕ) (y : ℕ) : ∀ (d m b acc : ℕ), m < 2 ^ 2 ^ d →
    ((imgS A d m b acc).testBit y = true ↔
      acc.testBit y = true ∨ ∃ x, x < 2 ^ d ∧ m.testBit x = true ∧ mvNR A (b + x) = y)
  | 0, m, b, acc, hm => by
    rw [imgS_zero]
    by_cases h : m = 0
    · subst h
      simp
    · have h1 : m = 1 := by simp at hm; omega
      subst h1
      rw [if_neg h, testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨0, by norm_num, rfl, h⟩
      · rintro (h | ⟨x, hx, -, h⟩)
        · exact Or.inl h
        · have : x = 0 := by simpa using hx
          subst this
          exact Or.inr h
  | d + 1, m, b, acc, hm => by
    rw [imgS_succ]
    by_cases h : m = 0
    · subst h
      simp
    · rw [if_neg h]
      have hp : (2 : ℕ) ^ 2 ^ (d + 1) = 2 ^ 2 ^ d * 2 ^ 2 ^ d := by
        rw [pow_succ, pow_mul, sq]
      have hhi : m >>> 2 ^ d < 2 ^ 2 ^ d := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
        rw [hp] at hm
        exact hm
      have hlo : m % 2 ^ 2 ^ d < 2 ^ 2 ^ d := Nat.mod_lt _ (by positivity)
      rw [imgS_testBit A y d _ _ _ hhi, imgS_testBit A y d _ _ _ hlo]
      have hd : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
      constructor
      · rintro ((h | ⟨x, hx, hb, he⟩) | ⟨x, hx, hb, he⟩)
        · exact Or.inl h
        · rw [Nat.testBit_mod_two_pow] at hb
          exact Or.inr ⟨x, by omega, (Bool.and_eq_true _ _ ▸ hb).2, he⟩
        · rw [Nat.testBit_shiftRight] at hb
          exact Or.inr ⟨2 ^ d + x, by omega, hb, by rw [← he]; congr 1; omega⟩
      · rintro (h | ⟨x, hx, hb, he⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hxd : x < 2 ^ d
          · refine Or.inl (Or.inr ⟨x, hxd, ?_, he⟩)
            rw [Nat.testBit_mod_two_pow, hb, decide_eq_true hxd, Bool.and_true]
          · refine Or.inr ⟨x - 2 ^ d, by omega, ?_, by rw [← he]; congr 1; omega⟩
            rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' (by omega)]
            exact hb

theorem imgF_eq (g m : ℕ) : CFSG.Quasithin.H13.AS91.Two.imgMask (unpackA g) m = imgF g m := by
  apply Nat.eq_of_testBit_eq
  intro y
  rw [Bool.eq_iff_iff, CFSG.Quasithin.H13.AS91.Two.imgMask, foldl_img_testBit, imgF,
    imgS_testBit _ _ 12 _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range, appNS, zero_add,
    Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, hb, he⟩
    exact ⟨x, hx, ⟨hx, hb⟩, he⟩
  · rintro ⟨x, -, ⟨hx, hb⟩, he⟩
    exact ⟨x, hx, hb, he⟩

theorem orbit_eq (gs : List ℕ) (m : ℕ) :
    bfsClosure (fun x : ℕ => x) ((gs.map unpackA).map CFSG.Quasithin.H13.AS91.Two.imgMask) 100 [m]
      ((∅ : Std.HashSet ℕ).insert m) [] = closN (gs.map imgF) 100 [m] (insP (.tip []) m) [] := by
  have hfs : (gs.map unpackA).map CFSG.Quasithin.H13.AS91.Two.imgMask = gs.map imgF := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => funext fun x => ?_
    rw [Function.comp_apply, imgF_eq]
  have hk : ∀ a b : ℕ, True → True →
      ((fun x : ℕ => x) ((fun q => q) a) == (fun x : ℕ => x) ((fun q => q) b)) = (a == b) :=
    fun _ _ _ _ => rfl
  have hs : SRel (fun q => q) (fun x : ℕ => x) (fun _ => True)
      ((∅ : Std.HashSet ℕ).insert m) (insP (.tip []) m) := by
    intro q _
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty]
  have := bfsClosure_N (fun q => q) (fun x : ℕ => x) (fun _ => True) hk (gs.map imgF) (gs.map imgF)
    (fun q _ => by rw [List.map_id']) (fun _ _ _ _ => trivial) 100 [m] [] _ _
    (fun _ _ => trivial) (fun _ _ => trivial) hs
  rw [hfs]
  simp only [List.map_id', List.map_nil] at this
  exact this.1

theorem tOrbit_eq (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA) :
    tOrbit () = tOrbQ := by
  rw [tOrbit, hg, s0Mask_eq, orbit_eq]
  rfl

theorem core1Rows_eq : CFSG.Quasithin.H13.AS91.Two.core1Rows = core1Q.map unpackA := by
  decide +kernel

theorem ncGens48_eq (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hgens : gensOKQ g13Q = true) : ncGens48 () = ncQ.map unpackA := by
  have hinv : invOKQ (g13Q.headD oneQ) (invQ (g13Q.headD oneQ)) = true := by
    rw [gensOKQ, List.all_eq_true] at hgens
    rcases h : g13Q with _ | ⟨g, gs⟩
    · rw [h] at hgens
      exact absurd h (by decide)
    · exact hgens g (by rw [h]; exact List.mem_cons_self)
  have h1 : (g13Q.map unpackA).headD idR = unpackA (g13Q.headD oneQ) := by
    rw [idRS]
    rfl
  have h2 : (core1Q.map unpackA).headD idR = unpackA (core1Q.headD oneQ) := by
    rw [idRS]
    rfl
  rw [ncGens48, hg, core1Rows_eq, ebRows_eq, h1, h2, invRS hinv, mulRS, mulRS, ncQ, List.map_append,
    List.map_append, List.map_cons, List.map_nil]

theorem ncOrbit_eq (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hgens : gensOKQ g13Q = true) : ncOrbit () = ncOrbQ := by
  rw [ncOrbit, ncGens48_eq hg hgens, s0Mask_eq, orbit_eq]
  rfl

theorem stab_sound (S : List ℕ) (ES : enumGrp (st48Q.map unpackA) = S.map unpackA)
    (BS : ∀ q ∈ S, q < 2 ^ 144) (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : stabAt S tOrbQ = true) : stabOK48 () = true := by
  simp only [stabAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [stabOK48, Bool.and_eq_true]
  rw [stabGens48_eq hg, ES, tOrbit_eq hg]
  generalize tOrbQ = O at h7 ⊢
  refine ⟨⟨⟨⟨⟨gensS _ h1, ?_⟩, ?_⟩, ?_⟩, dedupS BS 768 h5 h6⟩, h7⟩
  · refine (all_mapL fun g _ => ?_).trans h2
    rw [appNS, w1_contains]
  · rw [idRS, containsS BS oneQ_lt]
    exact h3
  · rw [closedS _ _ BS]
    exact h4

theorem s48L_shape : ∀ A ∈ s48L, ∀ x ∈ A, x < 64 := by decide +kernel

theorem pbarL_shape : ∀ A ∈ pbarL, ∀ x ∈ A, x < 64 := by decide +kernel

theorem b7L_lt : ∀ q ∈ b7L, q < 2 ^ 49 := by decide +kernel

theorem r64L_lt : ∀ q ∈ r64L, q < 2 ^ 49 := by decide +kernel

theorem wit1_lt : wit1Q < 2 ^ 49 := by decide +kernel

theorem wit2_lt : wit2Q < 2 ^ 49 := by decide +kernel

theorem d7Gens_eq : d7Gens = d7Q.map unpack7 := by decide +kernel

theorem r7Gens_eq : r7Gens = r7Q.map unpack7 := by decide +kernel

theorem wit48_eq : wit48 = (unpack7 wit1Q, unpack7 wit2Q) := by decide +kernel

theorem s48_eqL (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : s48OK = true) : s48 () = s48L := by
  rw [s48_eq hg]
  exact beq_iff_eq.1 h

theorem c3_eqL (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : s48OK = true) : c3List () = (c3Of s48L).map unpack7 := by
  rw [c3List, s48_eqL hg h, c3Of_eq _ s48L_shape]

theorem b7_eqL (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : s48OK = true) (hb : b7OK = true) : b7List () = b7L.map unpack7 := by
  rw [b7List, c3_eqL hg h, b7Of_eq, beq_iff_eq.1 hb]

theorem pbar_eqL (hpn : pNodup46Q = true) (h : pbarOK = true) : pbar () = pbarL := by
  rw [pbar, pList_eq (enumQ pQ) (enumS pQ) (enumS_lt _) hpn, List.map_map]
  have e : (enumQ pQ).map (res6 ∘ unpackA) = (enumQ pQ).map res6Q :=
    List.map_congr_left fun x _ => res6S x
  rw [e]
  exact beq_iff_eq.1 h

theorem t7List_eqL (hpn : pNodup46Q = true) (h : pbarOK = true) :
    t7List () = (c3Of pbarL).map unpack7 := by
  rw [t7List, pbar_eqL hpn h, c3Of_eq _ pbarL_shape]

theorem r7_enum (hr : r64OK = true) : enum7 r7Gens = r64L.map unpack7 := by
  rw [r7Gens_eq, (enum7S r7Q).1, beq_iff_eq.1 hr]

theorem c3_sound (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hs : s48OK = true) (hb : b7OK = true) (h : c348Q = true) : c3OK48 () = true := by
  have BC := c3Of_lt s48L s48L_shape
  simp only [c348Q, c3At, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [c3OK48, Bool.and_eq_true, and_assoc]
  rw [s48_eqL hg hs, c3_eqL hg hs, b7_eqL hg hs hb, t7el_eq, id7_eq]
  generalize c3Of s48L = C at BC h2 h3 h9 ⊢
  refine ⟨h1, dedup7S BC 3072 h2 h3, dedup7S b7L_lt 16 h4 h5, ?_, ?_, ?_, ?_⟩
  · rw [contains7 b7L_lt t7Q_lt]
    exact h6
  · refine (all_mapL fun x _ => ?_).trans h7
    refine all_mapL fun y _ => ?_
    rw [mul7S, mul7S, beq7 (mul7Q_lt _ _) (mul7Q_lt _ _)]
  · refine (all_mapL fun x _ => ?_).trans h8
    rw [mul7S, beq7 (mul7Q_lt _ _) one7_lt]
  · refine (all_mapL fun X hX => ?_).trans h9
    have e : ((b7L.map unpack7).all fun b => mul7 (unpack7 X) b == mul7 b (unpack7 X)) =
        b7L.all fun b => Nat.beq (mul7Q X b) (mul7Q b X) := by
      refine all_mapL fun b _ => ?_
      rw [mul7S, mul7S, beq7 (mul7Q_lt _ _) (mul7Q_lt _ _)]
    rw [e, Std.HashSet.contains_ofList, contains7 b7L_lt (BC X hX), memP_ofListP]

theorem itList_eq : itList () = itOf (enumQ ebQ) := by
  rw [itList, ebRows_eq, enumS, List.map_map, itOf]
  have e : (fun e => appN e q0c ^^^ q0c) ∘ unpackA = fun e => mvNR (unpackQ e) q0c ^^^ q0c := by
    funext e
    rw [Function.comp_apply, appNS]
  rw [e]

theorem i_sound (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hs : s48OK = true) (h : i48Q = true) : iOK48 () = true := by
  have BC := c3Of_lt s48L s48L_shape
  simp only [i48Q, iAt, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  simp only [iOK48, Bool.and_eq_true, and_assoc]
  rw [itList_eq, c3_eqL hg hs, wit48_eq]
  dsimp only
  generalize c3Of s48L = C at BC h7 h8 h9 h10 ⊢
  generalize itOf (enumQ ebQ) = It at h1 h2 h3 h4 h5 h6 ⊢
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_, h12, h13⟩
  · refine (all_mapL fun X _ => ?_).trans h7
    refine allc fun c _ => ?_
    rw [app7S]
  · refine (allc fun c _ => ?_).trans h8
    refine any_mapL fun X _ => ?_
    rw [app7S, nat_beq]
  · rw [contains7 BC wit1_lt]
    exact h9
  · rw [contains7 BC wit2_lt]
    exact h10
  · simp only [app7S, bne, nat_beq]
    exact h11

theorem contains_mapN (L : List ℕ) (f : ℕ → ℕ) (y : ℕ) :
    (L.map f).contains y = L.any fun x => Nat.beq y (f x) := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.contains_cons, ih, List.any_cons, nat_beq]

theorem pbarL_length : pbarL.length = 16 := rfl

theorem norm_all (R : List ℕ) (SA : List (List ℕ))
    (h : ∀ i < SA.length, tNormAt R (c3Of [SA.getD i []]) = true) : tNormAt R (c3Of SA) = true := by
  rw [tNormAt, c3Of, List.all_flatMap, List.all_eq_true]
  intro A hA
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
  have := h i hi
  rw [tNormAt, c3Of, List.getD_eq_getElem _ _ hi, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at this
  exact this

theorem tNorm_all (h : ∀ i < 16, tNorm48Q i = true) : tNormAt r64L (c3Of pbarL) = true :=
  norm_all r64L pbarL fun i hi => h i (pbarL_length ▸ hi)

theorem cent_of {T G : List ℕ} {p : ℕ → ℕ → Bool} {a b : ℕ → Bool} (hG : ∀ g ∈ G, g ∈ T)
    (h : T.all (fun X => !(G.all (p X)) || a X || b X) = true) :
    T.all (fun X => !(T.all (p X)) || a X || b X) = true := by
  rw [List.all_eq_true] at h ⊢
  intro X hX
  have hx := h X hX
  by_cases hall : G.all (p X) = true
  · rw [hall] at hx
    rcases Bool.eq_false_or_eq_true (T.all (p X)) with hT | hT
    · rw [hT]
      exact hx
    · rw [hT]
      rfl
  · have hT : T.all (p X) = false := by
      rw [Bool.not_eq_true, List.all_eq_false] at *
      obtain ⟨g, hg, hpg⟩ := hall
      exact ⟨g, hG g hg, hpg⟩
    rw [hT]
    rfl

theorem t_sound (hpn : pNodup46Q = true) (hpb : pbarOK = true)
    (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA) (hs : s48OK = true)
    (hb : b7OK = true) (hr : r64OK = true) (h1 : tBase48Q = true)
    (h2 : ∀ i < 16, tNorm48Q i = true) (h3 : tCent48Q = true) : tOK48 () = true := by
  have BT := c3Of_lt pbarL pbarL_shape
  have BD := (enum7S d7Q).2
  have hn := tNorm_all h2
  have h3c : tCentAt (c3Of pbarL) = true := h3
  simp only [tBase48Q, tBaseAt, Bool.and_eq_true, and_assoc] at h1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ :=
    h1
  simp only [tOK48, Bool.and_eq_true, and_assoc]
  rw [t7List_eqL hpn hpb, b7_eqL hg hs hb, pbar_eqL hpn hpb, s48_eqL hg hs, r7_enum hr, d7Gens_eq,
    (enum7S d7Q).1, r7Gens_eq, t7el_eq, id7_eq]
  generalize c3Of pbarL = T at BT hn h3c a2 a3 a4 a9 a15 a19 ⊢
  generalize enum7Q d7Q = D at BD a5 a6 a7 a8 a9 a10 ⊢
  have hok : ∀ L : List ℕ, (L.map unpack7).all ok7 = true := fun L => by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact ok7_unpack7 y
  have hsub : ∀ (L : List ℕ), (∀ q ∈ L, q < 2 ^ 49) →
      (L.all fun x => memP (ofListP T) x) = true →
      ((L.map unpack7).all fun x => (Std.HashSet.ofList (T.map unpack7)).contains x) = true := by
    intro L hL hh
    refine (all_mapL fun x hx => ?_).trans hh
    rw [Std.HashSet.contains_ofList, contains7 BT (hL x hx), memP_ofListP]
  have e17 : tNormAt r64L T = T.all fun X => r7Q.all fun y =>
      r64L.any fun y' => Nat.beq (mul7Q X y) (mul7Q y' X) := by
    simp only [tNormAt]
    refine allc fun X _ => allc fun y _ => ?_
    rw [memP_ofListP, contains_mapN]
  have hG : ∀ g ∈ tGens, g ∈ T := by
    intro g hg'
    have := List.all_eq_true.1 a19 g hg'
    rw [memP_ofListP] at this
    exact List.contains_iff_mem.1 this
  have h3' := cent_of (p := fun X Y => Nat.beq (mul7Q X Y) (mul7Q Y X))
    (a := fun X => Nat.beq X one7) (b := fun X => Nat.beq X t7Q) hG h3c
  refine ⟨a1, dedup7S BT 1024 a2 a3, hsub _ b7L_lt a4, hok _, ?_, ?_, dedup7S BD 64 a7 a8,
    hsub _ BD a9, ?_, hok _, ?_, ?_, dedup7S r64L_lt 64 a13 a14, hsub _ r64L_lt a15, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [contains7 BD one7_lt]
    exact a5
  · rw [closed7S _ _ BD]
    exact a6
  · refine (all_mapL fun x hx => ?_).trans a10
    rw [contains7 b7L_lt (BD x hx), beq7 (BD x hx) one7_lt]
  · rw [contains7 r64L_lt one7_lt]
    exact a11
  · rw [closed7S _ _ r64L_lt]
    exact a12
  · refine (all_mapL fun x _ => ?_).trans a16
    refine all_mapL fun y _ => ?_
    rw [mul7S, mul7S, beq7 (mul7Q_lt _ _) (mul7Q_lt _ _)]
  · refine (all_mapL fun x _ => ?_).trans a17
    rw [mul7S, beq7 (mul7Q_lt _ _) one7_lt]
  · refine (all_mapL fun X _ => ?_).trans (e17.symm.trans hn)
    refine all_mapL fun y _ => ?_
    refine any_mapL fun y' _ => ?_
    rw [mul7S, mul7S, beq7 (mul7Q_lt _ _) (mul7Q_lt _ _)]
  · exact (any_mapL fun x _ => rfl).trans a18
  · refine (all_mapL fun X hX => ?_).trans h3'
    have e : ((T.map unpack7).all fun Y => mul7 (unpack7 X) Y == mul7 Y (unpack7 X)) =
        T.all fun Y => Nat.beq (mul7Q X Y) (mul7Q Y X) := by
      refine all_mapL fun Y _ => ?_
      rw [mul7S, mul7S, beq7 (mul7Q_lt _ _) (mul7Q_lt _ _)]
    rw [e, beq7 (BT X hX) one7_lt, beq7 (BT X hX) t7Q_lt]

theorem aPartS (X : ℕ) : aPart (unpack7 X) = aPartQ X := rfl

theorem fixEbS (r : ℕ) : fixEb (unpackA r) = fixEbQ (enumQ ebQ) r := by
  rw [fixEb, ebRows_eq, enumS, fixEbQ, filter_mapG (q := fun e => Nat.beq (mulQ r e) (mulQ e r)),
    List.length_map]
  intro e _
  rw [mulRS, mulRS, beqS (mulQ_lt' _ _) (mulQ_lt' _ _)]

theorem fix7S (X : ℕ) : fix7 (unpack7 X) = fix7Q X := by
  simp only [fix7, fix7Q, app7S, nat_beq]

theorem fus_sound (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hr : r64OK = true) (h : fus48Q = true) : fusOK48 () = true := by
  simp only [fus48Q, fusAt, Bool.and_eq_true] at h
  obtain ⟨hnd, hle⟩ := h
  simp only [fusOK48]
  rw [r7_enum hr, stabGens48_eq hg, enumS]
  have hfe : ∀ r, fixEb (unpackA r) = fixEbQ (enumQ ebQ) r := fixEbS
  generalize enumQ ebQ = Eb at hfe hle ⊢
  generalize enumQ st48Q = S at hle ⊢
  rw [filter_mapG (q := fusP (S.map fun r => (r, res6Q r)) Eb)]
  · have hnd' := ((nodupP_iff _).1 hnd).filter (fusP (S.map fun r => (r, res6Q r)) Eb)
    rw [List.dedup_eq_self.2 (hnd'.map_on fun x hx y hy e =>
      unpack7_inj (r64L_lt x (List.mem_filter.1 hx).1) (r64L_lt y (List.mem_filter.1 hy).1) e),
      List.length_map, nat_ble]
    exact hle
  · intro X hX
    rw [fusP, bne, id7_eq, beq7 (r64L_lt X hX) one7_lt, List.any_map, List.any_map]
    refine congrArg₂ (fun a b => !a && b) rfl (anyc fun r _ => ?_)
    simp only [Function.comp_apply]
    rw [res6S, aPartS, fix7S, hfe, nat_ble]

theorem wordQS_lt (gs w : List ℕ) : wordQS gs w < 2 ^ 144 := by
  rw [wordQS]
  generalize w.map _ = L
  cases L with
  | nil => exact oneQ_lt
  | cons a L => exact mulQ_lt' _ _

theorem okRowsV (X : ℕ) : Viol.okRows (unpackA X) = true := by
  rw [Viol.okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨rfl, fun i hi => decide_eq_true ?_⟩
  exact unpackQ_lt4096 X _ (List.getElem_mem (by simpa [unpackA] using hi))

theorem spanRows48_eq : CFSG.Quasithin.H13.AS91.Two.spanRows48 = unpackA spQ := by decide +kernel

theorem spanInv48_eq : CFSG.Quasithin.H13.AS91.Two.spanInv48 = unpackA siQ := by decide +kernel

theorem orbW_lt : ∀ p ∈ CFSG.Quasithin.H13.AS91.Two.orbWords48, ∀ i ∈ p.2, i < g13Q.length := by
  decide +kernel

theorem ncW_lt : ∀ w ∈ CFSG.Quasithin.H13.AS91.Two.stabNcWords48, ∀ i ∈ w, i < ncQ.length := by
  decide +kernel

theorem orb_sound (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (hs : s48OK = true) (hb : b7OK = true) (h : orb48Q = true) : orbOK48 () = true := by
  simp only [orb48Q, orbAt, Bool.and_eq_true, and_assoc] at h
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := h
  simp only [orbOK48, Bool.and_eq_true, and_assoc]
  rw [ncGens48_eq hg o4, ncOrbit_eq hg o4, hg, b7_eqL hg hs hb, spanRows48_eq, spanInv48_eq,
    mk7S _ idA_lt, t7el_eq]
  generalize ncOrbQ = O at o7 ⊢
  refine ⟨?_, okRowsV _, okRowsV _, ?_, by decide +kernel, by decide +kernel, ?_, ?_,
    by decide +kernel, gensS _ o5, ?_, ?_, o7⟩
  · refine (allc fun p hp => ?_).trans o1
    rw [wordRowsS g13Q p.2 (orbW_lt p hp), appNS, w1_contains]
  · rw [mulRS, idRS, beqS (mulQ_lt' _ _) oneQ_lt]
    exact o2
  · rw [contains7 b7L_lt (mk7Q_lt _ idA_lt)]
    exact o3
  · rw [bne, beq7 (mk7Q_lt _ idA_lt) t7Q_lt]
    decide +kernel
  · refine (allc fun p hp => ?_).trans o6
    have h1 := (List.of_mem_zip hp).1
    have h2 := (List.of_mem_zip hp).2
    rw [wordRowsS ncQ p.2 (ncW_lt p.2 h2), wordRowsS g13Q p.1 (st48_lt p.1 h1),
      beqS (wordQS_lt _ _) (wordQS_lt _ _)]
  · rw [List.length_map]
    decide +kernel

theorem ok48_of (hw : wordsOK46 = true) (hpn : pNodup46Q = true) (hc : crdOK48 () = true)
    (hs : s48OK = true) (hpb : pbarOK = true) (hb : b7OK = true) (hr : r64OK = true)
    (h1 : stab48Q = true) (h2 : c348Q = true) (h3 : i48Q = true) (h4 : tBase48Q = true)
    (h5 : ∀ i < 16, tNorm48Q i = true) (h6 : tCent48Q = true) (h7 : fus48Q = true)
    (h8 : orb48Q = true) : ok48 () = true := by
  have hg := g13Gens_eq hw
  have e1 := stab_sound _ (enumS st48Q) (enumS_lt _) hg h1
  rw [ok48, hc, e1, c3_sound hg hs hb h2, i_sound hg hs h3, t_sound hpn hpb hg hs hb hr h4 h5 h6,
    fus_sound hg hr h7, orb_sound hg hs hb h8]
  rfl

end Certificates.Kernel.AS91K468
