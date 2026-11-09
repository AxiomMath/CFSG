module

public import Certificates.Data.Kernel.F2Orb24
public import CFSG.Certificates.Kernel.F2Set24Sound

public section

namespace CFSG.KS.F2Orb24

open CFSG.KC.F2Orb24
open CFSG.KS.F2Set24 (Back Back.base Back.sf Back.sg back_mem)
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native (vecMulN)

theorem mem_nil (d v : ℕ) : mem d v .nil = false := by cases d <;> rfl

theorem mod_two_pow_succ (v d : ℕ) : v % 2 ^ (d + 1) = v % 2 + 2 * (v / 2 % 2 ^ d) := by
  rw [Nat.pow_succ', Nat.mod_mul]

theorem mod_succ_iff (v x d : ℕ) :
    v % 2 ^ (d + 1) = x % 2 ^ (d + 1) ↔ v % 2 = x % 2 ∧ v / 2 % 2 ^ d = x / 2 % 2 ^ d := by
  rw [mod_two_pow_succ, mod_two_pow_succ]
  omega

theorem mem_ins : ∀ (d v x : ℕ) (t : BT),
    mem d v (ins d x t) = (decide (v % 2 ^ d = x % 2 ^ d) || mem d v t)
  | 0, v, x, t => by simp [ins, mem, Nat.mod_one]
  | d + 1, v, x, t => by
    have ih := mem_ins d (v / 2) (x / 2)
    simp only [mod_succ_iff, Bool.decide_and]
    cases t <;> rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      simp [ins, mem, hx, hv, ih, mem_nil]

theorem mem24_ins {v x : ℕ} (t : BT) (hv : v < 2 ^ 24) (hx : x < 2 ^ 24) :
    mem 24 v (ins 24 x t) = (decide (v = x) || mem 24 v t) := by
  rw [mem_ins, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hx]

@[expose] def Rep (t : BT) (s : List ℕ) : Prop :=
  (∀ u ∈ s, u < 2 ^ 24) ∧ ∀ v < 2 ^ 24, mem 24 v t = true ↔ v ∈ s

theorem rep_ins {t : BT} {s : List ℕ} (h : Rep t s) {x : ℕ} (hx : x < 2 ^ 24) :
    Rep (ins 24 x t) (x :: s) := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact hx
    · exact h.1 u hu
  · rw [mem24_ins t hv hx, Bool.or_eq_true, decide_eq_true_eq, h.2 v hv, List.mem_cons]

theorem bfsK_sound {f g f' g' : ℕ → ℕ} {root : ℕ} (hf : ∀ v < 2 ^ 24, f v = f' v)
    (hg : ∀ v < 2 ^ 24, g v = g' v) :
    ∀ (es : List (ℕ × Bool)) (t T : BT) (s : List ℕ), Rep t s → s.Nodup →
      (∀ u ∈ s, Back f' g' root u) → bfsK f g t es = some T →
      Rep T ((es.map Prod.fst).reverse ++ s) ∧ ((es.map Prod.fst).reverse ++ s).Nodup ∧
        ∀ u ∈ (es.map Prod.fst).reverse ++ s, Back f' g' root u
  | [], t, T, s, hr, hn, hb, h => by
    have : t = T := Option.some.inj h
    subst this
    simpa using ⟨hr, hn, hb⟩
  | e :: es, t, T, s, hr, hn, hb, h => by
    simp only [bfsK] at h
    by_cases hc : (Nat.blt e.1 16777216 && !mem 24 e.1 t &&
        (Nat.blt (if e.2 then g e.1 else f e.1) 16777216 &&
          mem 24 (if e.2 then g e.1 else f e.1) t)) = true
    · simp only [hc, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨he, hnew⟩, hw, hwm⟩ := hc
      have hnot : e.1 ∉ s := fun hm => by
        rw [← (hr.2 e.1 he)] at hm
        rw [hm] at hnew
        exact Bool.noConfusion hnew
      have hbe : Back f' g' root e.1 := by
        have hwb := hb _ ((hr.2 _ hw).1 hwm)
        cases hb2 : e.2
        · rw [hb2] at hwb
          simp only [Bool.false_eq_true, ite_false] at hwb
          rw [hf e.1 he] at hwb
          exact Back.sf hwb
        · rw [hb2] at hwb
          simp only [ite_true] at hwb
          rw [hg e.1 he] at hwb
          exact Back.sg hwb
      have ih := bfsK_sound hf hg es _ T (e.1 :: s) (rep_ins hr he) (List.nodup_cons.2 ⟨hnot, hn⟩)
        (fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hbe
          · exact hb u hu) h
      simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih
    · simp [hc] at h

theorem mulC_eq (l : List ℕ) (v : ℕ) : mulC l v = vecMulN l.length l.toArray v := by
  have key : ∀ (l : List ℕ) (v acc : ℕ), (List.range l.length).foldl
      (fun acc j => if v.testBit j then acc ^^^ (l[j]?.getD 0) else acc) acc = acc ^^^ mulC l v := by
    intro l
    induction l with
    | nil => intro v acc; simp [mulC]
    | cons c0 cs ih =>
      intro v acc
      rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have e : ∀ a j, (if v.testBit (j + 1) then a ^^^ ((c0 :: cs)[j + 1]?.getD 0) else a) =
          (if (v / 2).testBit j then a ^^^ (cs[j]?.getD 0) else a) := by
        intro a j
        rw [Nat.testBit_succ, List.getElem?_cons_succ]
      rw [show (fun (x : ℕ) (y : ℕ) => if v.testBit y.succ = true then
          x ^^^ (c0 :: cs)[y.succ]?.getD 0 else x) =
          (fun a j => if (v / 2).testBit j = true then a ^^^ cs[j]?.getD 0 else a) from
        funext fun a => funext fun j => e a j]
      rw [ih (v / 2)]
      simp only [mulC, Nat.testBit_zero, List.getElem?_cons_zero, Option.getD_some]
      by_cases h : v % 2 = 1 <;> simp [h, Nat.xor_assoc]
  unfold vecMulN
  simp only [List.getElem?_toArray]
  rw [key l v 0, Nat.zero_xor]

theorem land1 (v : ℕ) : Nat.land v 1 = v % 2 := Nat.and_one_is_mod v

theorem shr1 (v : ℕ) : Nat.shiftRight v 1 = v / 2 := Nat.shiftRight_one v

theorem brec_beq {α : Sort _} (a b : α) (x y : ℕ) :
    Bool.rec (motive := fun _ => α) a b (Nat.beq x y) = if x = y then b else a := by
  cases hb : Nat.beq x y
  · exact (ite_eq_right (Nat.ne_of_beq_eq_false hb)).symm
  · exact (ite_eq_left (Nat.eq_of_beq_eq_true hb)).symm

theorem brec_bool {α : Sort _} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem memK_eq : ∀ (d : ℕ) (t : BT) (v : ℕ), memK d t v = mem d v t
  | 0, .nil, _ => rfl
  | 0, .tip, _ => rfl
  | 0, .node _ _, _ => rfl
  | _ + 1, .nil, _ => rfl
  | _ + 1, .tip, _ => rfl
  | d + 1, .node l r, v => by
    show Bool.rec (motive := fun _ => Bool) (memK d r (Nat.shiftRight v 1))
      (memK d l (Nat.shiftRight v 1)) (Nat.beq (Nat.land v 1) 0) = mem (d + 1) v (.node l r)
    rw [land1, shr1, memK_eq d l, memK_eq d r, brec_beq]
    simp only [mem]

theorem insK_eq : ∀ (d v : ℕ) (t : BT), insK d v t = ins d v t
  | 0, _, _ => rfl
  | d + 1, v, t => by
    show Bool.rec (motive := fun _ => BT) (BT.node (lftK t) (insK d (Nat.shiftRight v 1) (rgtK t)))
      (BT.node (insK d (Nat.shiftRight v 1) (lftK t)) (rgtK t)) (Nat.beq (Nat.land v 1) 0) =
      ins (d + 1) v t
    rw [land1, shr1, insK_eq d, insK_eq d, brec_beq]
    all_goals cases t <;> by_cases h : v % 2 = 0 <;> simp [h, ins, lftK, rgtK]

theorem mulCK_eq : ∀ (l : List ℕ) (v : ℕ), mulCK l v = mulC l v
  | [], _ => rfl
  | c :: l, v => by
    show Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 c (Nat.beq (Nat.land v 1) 1))
      (mulCK l (Nat.shiftRight v 1)) = mulC (c :: l) v
    rw [land1, shr1, mulCK_eq l, brec_beq]
    rfl

theorem bfsKK_eq (f g : ℕ → ℕ) : ∀ (es : List (ℕ × Bool)) (t : BT),
    bfsKK f g es t = bfsK f g t es
  | [], _ => rfl
  | (v, b) :: es, t => by
    show Bool.rec (motive := fun _ => Option BT) none (bfsKK f g es (insK 24 v t))
      (stepOK v (Bool.rec (motive := fun _ => ℕ) (f v) (g v) b) t) = bfsK f g t ((v, b) :: es)
    rw [bfsKK_eq f g es, insK_eq, brec_bool]
    unfold stepOK
    rw [memK_eq, memK_eq]
    cases b <;> rfl

theorem closedKK_eq (f g : ℕ → ℕ) (T : BT) : ∀ L : List ℕ, closedKK f g T L = closedK f g T L
  | [] => rfl
  | v :: L => by
    show (Nat.blt (f v) 16777216 && memK 24 T (f v) && Nat.blt (g v) 16777216 &&
      memK 24 T (g v) && closedKK f g T L) = closedK f g T (v :: L)
    rw [closedKK_eq f g T L, memK_eq, memK_eq]
    simp [closedK, Bool.and_assoc]

theorem sparseK_eq (cP cQ : List ℕ) (root n : ℕ) (es : List (ℕ × Bool)) :
    sparseK cP cQ root n es = sparseOK cP cQ root n es := by
  have hf : mulCK cP = mulC cP := funext (mulCK_eq cP)
  have hg : mulCK cQ = mulC cQ := funext (mulCK_eq cQ)
  unfold sparseK sparseOK
  rw [hf, hg, bfsKK_eq, insK_eq]
  cases bfsK (mulC cP) (mulC cQ) (ins 24 root .nil) es with
  | none => rfl
  | some T => simp only [closedKK_eq]

theorem sparseOK_sound {cP cQ : List ℕ} {root n : ℕ} {es : List (ℕ × Bool)}
    (h : sparseOK cP cQ root n es = true) :
    ∃ T : Finset ℕ, (∀ v ∈ T, v < 2 ^ 24) ∧ root ∈ T ∧
      (∀ v ∈ T, vecMulN 24 cP.toArray v ∈ T ∧ vecMulN 24 cQ.toArray v ∈ T) ∧
      (∀ v ∈ T, Back (vecMulN 24 cP.toArray) (vecMulN 24 cQ.toArray) root v) ∧
      T.card = n := by
  unfold sparseOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hlP, hlQ⟩, hroot⟩, hn⟩, h⟩ := h
  have hfP : ∀ v < 2 ^ 24, mulC cP v = vecMulN 24 cP.toArray v := fun v _ => by
    rw [mulC_eq, hlP]
  have hfQ : ∀ v < 2 ^ 24, mulC cQ v = vecMulN 24 cQ.toArray v := fun v _ => by
    rw [mulC_eq, hlQ]
  have hroot' : root < 2 ^ 24 := by norm_num; exact hroot
  have hr0 : Rep (ins 24 root .nil) [root] := by
    refine ⟨fun u hu => by rw [List.mem_singleton.1 hu]; exact hroot', fun v hv => ?_⟩
    rw [mem24_ins _ hv hroot', mem_nil, Bool.or_false, decide_eq_true_eq, List.mem_singleton]
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i T hT
    obtain ⟨hR, hN, hB⟩ := bfsK_sound hfP hfQ es _ T [root] hr0 (List.nodup_singleton _)
      (fun u hu => by rw [List.mem_singleton.1 hu]; exact Back.base) hT
    set s := (es.map Prod.fst).reverse ++ [root] with hs
    have hmem : ∀ v, v ∈ root :: es.map Prod.fst ↔ v ∈ s := fun v => by
      simp [hs, or_comm]
    unfold closedK at h
    rw [List.all_eq_true] at h
    have hcl : ∀ v ∈ s, vecMulN 24 cP.toArray v ∈ s ∧ vecMulN 24 cQ.toArray v ∈ s := by
      intro v hv
      have hv' := h v ((hmem v).2 hv)
      simp only [Bool.and_eq_true, Nat.blt_eq] at hv'
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv'
      have hvl := hR.1 v hv
      rw [← hfP v hvl, ← hfQ v hvl]
      exact ⟨(hR.2 _ (by norm_num; exact h1)).1 h2, (hR.2 _ (by norm_num; exact h3)).1 h4⟩
    refine ⟨s.toFinset, fun v hv => hR.1 v (List.mem_toFinset.1 hv),
      List.mem_toFinset.2 ((hmem root).1 List.mem_cons_self), fun v hv => ?_,
      fun v hv => hB v (List.mem_toFinset.1 hv), ?_⟩
    · obtain ⟨a, b⟩ := hcl v (List.mem_toFinset.1 hv)
      exact ⟨List.mem_toFinset.2 a, List.mem_toFinset.2 b⟩
    · rw [List.toFinset_card_of_nodup hN, hs]
      simp [hn]

open CFSG.Sporadic.Co1Schreier Matrix in
theorem orbit_of_sparseOK {P Q : GL24} {cP cQ : List ℕ} {root n : ℕ} {es : List (ℕ × Bool)}
    (hP : ActsBy P cP.toArray) (hQ : ActsBy Q cQ.toArray) (h : sparseOK cP cQ root n es = true) :
    (kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root)).ncard = n := by
  obtain ⟨T, hlt, hr, hcl, hback, hcard⟩ := sparseOK_sound h
  have hset : kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) =
      toVecD 24 '' (T : Set ℕ) := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      refine closure_mapsTo ((T.finite_toSet).image _) ?_ ?_ hk _ ⟨root, hr, rfl⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨_, (hcl v hv).1, (hP v).symm⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨_, (hcl v hv).2, (hQ v).symm⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact back_mem hP hQ (hback v hv)
  rw [hset, Set.InjOn.ncard_image fun a ha b hb hab => toVecD_injective (hlt a ha) (hlt b hb) hab,
    Set.ncard_coe_finset, hcard]

open CFSG.Sporadic.Co1Schreier Matrix in
theorem orbit_of_sparseK {P Q : GL24} {cP cQ : List ℕ} {root n : ℕ} {es : List (ℕ × Bool)}
    (hP : ActsBy P cP.toArray) (hQ : ActsBy Q cQ.toArray) (h : sparseK cP cQ root n es = true) :
    (kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root)).ncard = n :=
  orbit_of_sparseOK hP hQ (by rw [← sparseK_eq]; exact h)

end CFSG.KS.F2Orb24

end
