module

public import CFSG.Certificates.Kernel.VecKOrbit
public import CFSG.Certificates.Kernel.VecKTrees
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.VOrbFull

open CFSG.KC.VecK CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem push_lt {α : Type} [Inhabited α] (a : Array α) (x : α) {j : Nat} (h : j < a.size) :
    (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

theorem push_last {α : Type} [Inhabited α] (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem ofNat_ne_none {x : Nat} (hx : x < 2 ^ 30) : UInt32.ofNat x ≠ none32 := by
  intro e
  have h := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  omega

theorem toNat_ofNat {x : Nat} (hx : x < 2 ^ 30) : (UInt32.ofNat x).toNat = x := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

structure PInv (d v0 : Nat) (R : Finset Nat) (pos : Array UInt32) (pts : Array Nat) : Prop where
  pos0 : 0 < pts.size
  p0 : pts[0]! = v0
  mem : ∀ i < pts.size, pts[i]! ∈ R
  inj : ∀ i < pts.size, ∀ j < pts.size, pts[i]! = pts[j]! → i = j
  psz : pos.size = 2 ^ d
  hit : ∀ i < pts.size, pos[pts[i]!]! = UInt32.ofNat i
  miss : ∀ x < 2 ^ d, (∀ i < pts.size, pts[i]! ≠ x) → pos[x]! = none32

variable {d n v0 : Nat} {R : Finset Nat}

theorem size_le {pts : Array Nat} (hmem : ∀ i < pts.size, pts[i]! ∈ R)
    (hinj : ∀ i < pts.size, ∀ j < pts.size, pts[i]! = pts[j]! → i = j) : pts.size ≤ R.card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.range pts.size) (t := R) (fun i => pts[i]!)
    (fun i hi => hmem i (by simpa using hi))
    (fun i hi j hj e => hinj i (by simpa using hi) j (by simpa using hj) e)
  simpa using h

theorem ins_inv {pos : Array UInt32} {pts : Array Nat} {x : Nat} (hR : R.card = n)
    (hn : n < 2 ^ 30) (hRlt : ∀ y ∈ R, y < 2 ^ d) (H : PInv d v0 R pos pts) (hx : x ∈ R) :
    PInv d v0 R (if (pos[x]! == none32) = true then pos.set! x (UInt32.ofNat pts.size) else pos)
      (if (pos[x]! == none32) = true then pts.push x else pts) ∧
    pts.size ≤ (if (pos[x]! == none32) = true then pts.push x else pts).size ∧
    (∀ i < pts.size, (if (pos[x]! == none32) = true then pts.push x else pts)[i]! = pts[i]!) ∧
    ∃ i < (if (pos[x]! == none32) = true then pts.push x else pts).size,
      (if (pos[x]! == none32) = true then pts.push x else pts)[i]! = x ∧
      (if (pos[x]! == none32) = true then pos.set! x (UInt32.ofNat pts.size) else pos)[x]! =
        UInt32.ofNat i := by
  have hsz : pts.size ≤ n := hR ▸ size_le H.mem H.inj
  have hxd := hRlt x hx
  by_cases hc : ∃ i < pts.size, pts[i]! = x
  · obtain ⟨i, hi, rfl⟩ := hc
    have hget := H.hit i hi
    have hne : (pos[pts[i]!]! == none32) = false := by
      rw [hget]
      exact beq_false_of_ne (ofNat_ne_none (by omega))
    have hc' : ¬ ((pos[pts[i]!]! == none32) = true) := by rw [hne]; exact Bool.false_ne_true
    rw [ite_eq_right hc', ite_eq_right hc']
    exact ⟨H, le_refl _, fun _ _ => rfl, i, hi, rfl, hget⟩
  · have hall : ∀ i < pts.size, pts[i]! ≠ x := fun i hi e => hc ⟨i, hi, e⟩
    have hmiss : pos[x]! = none32 := H.miss x hxd hall
    have hcond : (pos[x]! == none32) = true := by rw [hmiss]; exact beq_self_eq_true _
    rw [ite_eq_left hcond, ite_eq_left hcond]
    have hself : (pos.set! x (UInt32.ofNat pts.size))[x]! = UInt32.ofNat pts.size := by
      rw [Array.getElem!_set!_self _ _ _ (by rw [H.psz]; exact hxd)]
    have hs1 : (pts.push x).size = pts.size + 1 := by simp
    have hget : ∀ i < pts.size + 1, (pts.push x)[i]! = if i < pts.size then pts[i]! else x := by
      intro i hi
      by_cases h : i < pts.size
      · rw [push_lt _ _ h, ite_eq_left h]
      · have : i = pts.size := by omega
        subst this
        rw [push_last, ite_eq_right h]
    refine ⟨⟨by omega, ?_, fun i hi => ?_, fun i hi j hj e => ?_, by rw [Array.size_set!, H.psz],
      fun i hi => ?_, fun y hy hy' => ?_⟩, by omega, fun i hi => push_lt _ _ hi,
      pts.size, by omega, push_last _ _, hself⟩
    · rw [push_lt _ _ H.pos0]
      exact H.p0
    · rw [hs1] at hi
      rw [hget i hi]
      split
      · exact H.mem i (by assumption)
      · exact hx
    · rw [hs1] at hi hj
      rw [hget i hi, hget j hj] at e
      by_cases h1 : i < pts.size <;> by_cases h2 : j < pts.size
      · rw [ite_eq_left h1, ite_eq_left h2] at e
        exact H.inj i h1 j h2 e
      · rw [ite_eq_left h1, ite_eq_right h2] at e
        exact absurd e (hall i h1)
      · rw [ite_eq_right h1, ite_eq_left h2] at e
        exact absurd e.symm (hall j h2)
      · omega
    · rw [hs1] at hi
      rw [hget i hi]
      by_cases h1 : i < pts.size
      · rw [ite_eq_left h1, Array.getElem!_set!_ne _ _ _ _ (fun e => hall i h1 e.symm)]
        exact H.hit i h1
      · rw [ite_eq_right h1, hself]
        congr 1
        omega
    · have hyx : x ≠ y := fun e => by
        subst e
        exact hy' pts.size (by omega) (push_last _ _)
      rw [Array.getElem!_set!_ne _ _ _ _ hyx]
      refine H.miss y hy fun i hi e => hy' i (by omega) ?_
      rw [push_lt _ _ hi, e]

structure FInv (d v0 : Nat) (R : Finset Nat) (cA cB : Array Nat) (h : Nat) (s : VSt) : Prop where
  pt : PInv d v0 R s.1 s.2.1
  h_le : h ≤ s.2.1.size
  asz : s.2.2.1.size = h
  bsz : s.2.2.2.size = h
  aok : ∀ j < h, ap s.2.2.1 j < s.2.1.size ∧ s.2.1[ap s.2.2.1 j]! = vecMulN d cA s.2.1[j]!
  bok : ∀ j < h, ap s.2.2.2 j < s.2.1.size ∧ s.2.1[ap s.2.2.2 j]! = vecMulN d cB s.2.1[j]!

variable {cA cB : Array Nat}

theorem table_step {pts pts2 : Array Nat} {al : Table} {h i : Nat} {f : Nat → Nat}
    (hal : al.size = h) (hlt : h < pts.size) (hsz : pts.size ≤ pts2.size)
    (hpre : ∀ j < pts.size, pts2[j]! = pts[j]!) (hi : i < pts2.size) (hi30 : i < 2 ^ 30)
    (hpi : pts2[i]! = f pts[h]!)
    (hold : ∀ j < h, ap al j < pts.size ∧ pts[ap al j]! = f pts[j]!) :
    ∀ j < h + 1, ap (al.push (UInt32.ofNat i)) j < pts2.size ∧
      pts2[ap (al.push (UInt32.ofNat i)) j]! = f pts2[j]! := by
  intro j hj
  have e : ap (al.push (UInt32.ofNat i)) j = if j < h then ap al j else i := by
    unfold ap
    by_cases h1 : j < h
    · rw [push_lt _ _ (by omega), ite_eq_left h1]
    · have : j = h := by omega
      subst this
      rw [ite_eq_right h1, ← hal, push_last, toNat_ofNat hi30]
  rw [e, hpre j (by omega)]
  by_cases h1 : j < h
  · rw [ite_eq_left h1]
    obtain ⟨a1, a2⟩ := hold j h1
    exact ⟨by omega, by rw [hpre _ a1, a2]⟩
  · rw [ite_eq_right h1]
    have : j = h := by omega
    subst this
    exact ⟨hi, hpi⟩

theorem step_inv (hR : R.card = n) (hn : n < 2 ^ 30) (hRlt : ∀ y ∈ R, y < 2 ^ d)
    (hA : ∀ x ∈ R, vecMulN d cA x ∈ R) (hB : ∀ x ∈ R, vecMulN d cB x ∈ R) (h : Nat) (s : VSt)
    (H : FInv d v0 R cA cB h s) :
    (∃ s', vBody d cA cB h s = pure (.yield s') ∧ FInv d v0 R cA cB (h + 1) s') ∨
      (∃ s', vBody d cA cB h s = pure (.done s') ∧ FInv d v0 R cA cB s'.2.1.size s') := by
  rcases s with ⟨pos, pts, al, be⟩
  obtain ⟨Hp, hle, has, hbs, hao, hbo⟩ := H
  dsimp only at Hp hle has hbs hao hbo
  by_cases hlt : h < pts.size
  · left
    have hv := Hp.mem h hlt
    obtain ⟨H1, hs1, hpre1, i1, hi1, hpi1, hpos1⟩ := ins_inv hR hn hRlt Hp (hA _ hv)
    obtain ⟨H2, hs2, hpre2, i2, hi2, hpi2, hpos2⟩ := ins_inv hR hn hRlt H1 (hB _ hv)
    have hsz2 := hR ▸ size_le H2.mem H2.inj
    unfold vBody
    rw [ite_eq_left hlt]
    simp only [vIns_eq]
    refine ⟨_, rfl, ⟨H2, by dsimp only; omega, by simp [has], by simp [hbs],
      ?_, ?_⟩⟩
    · dsimp only
      rw [hpos1]
      refine table_step has hlt (by omega) ?_ (by omega) (by omega) ?_ hao
      · intro j hj
        rw [hpre2 j (by omega), hpre1 j hj]
      · rw [hpre2 i1 hi1, hpi1]
    · dsimp only
      rw [hpos2]
      refine table_step hbs hlt (by omega) ?_ hi2 (by omega) hpi2 hbo
      intro j hj
      rw [hpre2 j (by omega), hpre1 j hj]
  · right
    unfold vBody
    simp only [hlt, ite_false]
    have : h = pts.size := by omega
    subst this
    exact ⟨_, rfl, ⟨Hp, hle, has, hbs, hao, hbo⟩⟩

private theorem forIn_range_inv {β : Type} (P : Nat → β → Prop) (Q : β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → P j b →
      (∃ b', f j b = pure (.yield b') ∧ P (j + 1) b') ∨ (∃ b', f j b = pure (.done b') ∧ Q b'))
    (hE : ∀ b, P E b → Q b) :
    ∀ k a (init : β), a + k = E → P a init → Q (forIn (List.range' a k) init f)
  | 0, a, init, hk, h => by
    rw [List.range'_zero, List.forIn_nil]
    rw [Nat.add_zero] at hk
    subst hk
    exact hE init h
  | k + 1, a, init, hk, h => by
    rcases hf a init (by omega) h with ⟨b', hb, hR⟩ | ⟨b', hb, hQ⟩
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact forIn_range_inv P Q E f hf hE k (a + 1) b' (by omega) hR
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact hQ

theorem vOrbitBFS_full (hR : R.card = n) (hn : n < 2 ^ 30) (hRlt : ∀ y ∈ R, y < 2 ^ d)
    (hv0 : v0 ∈ R) (hA : ∀ x ∈ R, vecMulN d cA x ∈ R) (hB : ∀ x ∈ R, vecMulN d cB x ∈ R)
    (hmin : ∀ S : Set Nat, v0 ∈ S → (∀ x ∈ S, vecMulN d cA x ∈ S ∧ vecMulN d cB x ∈ S) →
      ∀ x ∈ R, x ∈ S) :
    (vOrbitBFS d cA cB v0 n).pts.size = n ∧ (vOrbitBFS d cA cB v0 n).alpha.size = n ∧
      (vOrbitBFS d cA cB v0 n).beta.size = n ∧ (vOrbitBFS d cA cB v0 n).pts[0]! = v0 ∧
      (∀ i < n, (vOrbitBFS d cA cB v0 n).pts[i]! ∈ R) ∧
      (∀ i < n, ∀ j < n, (vOrbitBFS d cA cB v0 n).pts[i]! = (vOrbitBFS d cA cB v0 n).pts[j]! →
        i = j) ∧
      (∀ i < n, ap (vOrbitBFS d cA cB v0 n).alpha i < n ∧
        (vOrbitBFS d cA cB v0 n).pts[ap (vOrbitBFS d cA cB v0 n).alpha i]! =
          vecMulN d cA (vOrbitBFS d cA cB v0 n).pts[i]!) ∧
      (∀ i < n, ap (vOrbitBFS d cA cB v0 n).beta i < n ∧
        (vOrbitBFS d cA cB v0 n).pts[ap (vOrbitBFS d cA cB v0 n).beta i]! =
          vecMulN d cB (vOrbitBFS d cA cB v0 n).pts[i]!) := by
  have hv0d := hRlt v0 hv0
  have hrs : (Array.replicate (1 <<< d) (none32 ())).size = 2 ^ d := by
    rw [Array.size_replicate, Nat.one_shiftLeft]
  have hinit : FInv d v0 R cA cB 0 ((Array.replicate (1 <<< d) none32).set! v0 0, #[v0], #[], #[]) :=
    ⟨⟨by simp, rfl, fun i hi => by
        have : i = 0 := by simpa using hi
        subst this
        exact hv0,
      fun i hi j hj _ => by simp at hi hj; omega, by rw [Array.size_set!, hrs],
      fun i hi => by
        have : i = 0 := by simpa using hi
        subst this
        change ((Array.replicate (1 <<< d) none32).set! v0 0)[v0]! = UInt32.ofNat 0
        rw [Array.getElem!_set!_self _ _ _ (by rw [hrs]; exact hv0d)]
        rfl,
      fun x hx hall => by
        have hne : v0 ≠ x := fun e => hall 0 (by simp) (by rw [← e]; rfl)
        change ((Array.replicate (1 <<< d) none32).set! v0 0)[x]! = none32
        rw [Array.getElem!_set!_ne _ _ _ _ hne, getElem!_pos _ x (by rw [hrs]; exact hx)]
        simp⟩,
      Nat.zero_le _, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hfin := forIn_range_inv (FInv d v0 R cA cB) (fun s => FInv d v0 R cA cB s.2.1.size s) n
    (vBody d cA cB) (fun j b _ H => step_inv hR hn hRlt hA hB j b H)
    (fun b H => by
      have h1 := H.h_le
      have h2 := hR ▸ size_le H.pt.mem H.pt.inj
      have : b.2.1.size = n := by omega
      rw [this]
      exact H) n 0 _ (Nat.zero_add n) hinit
  rw [vOrbitBFS_eq, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  simp only [hr]
  generalize (forIn (List.range' 0 n) _ (vBody d cA cB) : Id VSt) = s at hfin
  obtain ⟨Hp, -, has, hbs, hao, hbo⟩ := hfin
  set m := s.2.1.size with hm
  have hcl : ∀ x ∈ R, ∃ i < m, s.2.1[i]! = x := by
    refine hmin {x | ∃ i < m, s.2.1[i]! = x} ⟨0, Hp.pos0, Hp.p0⟩ ?_
    rintro x ⟨i, hi, rfl⟩
    exact ⟨⟨_, (hao i hi).1, (hao i hi).2⟩, ⟨_, (hbo i hi).1, (hbo i hi).2⟩⟩
  have hmn : m = n := by
    have h1 : m ≤ n := hR ▸ size_le Hp.mem Hp.inj
    have h2 : R ⊆ (Finset.range m).image fun i => s.2.1[i]! := by
      intro x hx
      obtain ⟨i, hi, e⟩ := hcl x hx
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e⟩
    have h3 := (Finset.card_le_card h2).trans Finset.card_image_le
    rw [Finset.card_range, hR] at h3
    omega
  rw [hmn] at has hbs hao hbo
  refine ⟨hmn, has, hbs, Hp.p0, fun i hi => Hp.mem i (by omega),
    fun i hi j hj e => Hp.inj i (by omega) j (by omega) e, fun i hi => ?_, fun i hi => ?_⟩
  · exact hao i hi
  · exact hbo i hi

theorem orbit_ok_of {O : VOrbit} (hn : n < 2 ^ 30) (hsz : O.pts.size = n) (hasz : O.alpha.size = n)
    (hbsz : O.beta.size = n) (hlt : ∀ i < n, O.pts[i]! < 2 ^ d)
    (hinj : ∀ i < n, ∀ j < n, O.pts[i]! = O.pts[j]! → i = j)
    (hao : ∀ i < n, ap O.alpha i < n ∧ O.pts[ap O.alpha i]! = vecMulN d cA O.pts[i]!)
    (hbo : ∀ i < n, ap O.beta i < n ∧ O.pts[ap O.beta i]! = vecMulN d cB O.pts[i]!) :
    vOrbitOK d n cA cB O = true := by
  unfold vOrbitOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hsz, hasz⟩, hbsz⟩, CFSG.KS.TW.allIn_iff.2 fun i hi => ?_⟩
  have hpos := CFSG.KC.PosTable.posTable_get (d := d) (pts := O.pts)
    (fun j hj => hlt j (by omega)) (fun j hj k hk e => hinj j (by omega) k (by omega) e)
    (by omega) (i := i) (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hlt i hi, hpos⟩, (hao i hi).1⟩, (hao i hi).2⟩, (hbo i hi).1⟩, (hbo i hi).2⟩

abbrev lets (O : VOrbit) : Array Table := #[O.alpha, O.beta]

abbrev tf (O : VOrbit) : Nat → Nat → Nat := fun l x => ap (lets O)[l]! x

theorem tree_of {O : VOrbit} (hn0 : 0 < n) (hn : n < 2 ^ 30)
    (ha : ∀ i < n, ap O.alpha i < n) (hb : ∀ i < n, ap O.beta i < n)
    (hreach : ∀ i < n, Reach (· ∈ #[0, 1]) (tf O) 0 i) :
    (treeBFS n 0 (lets O) #[0, 1]).pts.size = n ∧
      CFSG.Perm.Native.treeOK n 0 (treeBFS n 0 (lets O) #[0, 1]) (lets O) #[0, 1] = true := by
  have hL : ∀ l ∈ (#[0, 1] : Array Nat), ∀ x < n, ap (lets O)[l]! x < n := by
    intro l hl x hx
    have : l = 0 ∨ l = 1 := by simpa using hl
    rcases this with rfl | rfl
    · exact ha x hx
    · exact hb x hx
  have hB := treeBFS_spec (n := n) (root := 0) (letters := lets O) (lv := #[0, 1]) (by omega) hn0
    (fun l hl => by
      have : l = 0 ∨ l = 1 := by simpa using hl
      rcases this with rfl | rfl <;> norm_num) hL
  refine ⟨?_, hB.ok⟩
  have hcov : ∀ i < n, ∃ t < (treeBFS n 0 (lets O) #[0, 1]).pts.size,
      ap (treeBFS n 0 (lets O) #[0, 1]).pts t = i :=
    fun i hi => (hB.facts.reach_iff i).1 (hreach i hi)
  have h1 := hB.size_le
  have h2 : Finset.range n ⊆ (Finset.range (treeBFS n 0 (lets O) #[0, 1]).pts.size).image
      (ap (treeBFS n 0 (lets O) #[0, 1]).pts) := by
    intro i hi
    obtain ⟨t, ht, e⟩ := hcov i (Finset.mem_range.1 hi)
    exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht, e⟩
  have h3 := (Finset.card_le_card h2).trans Finset.card_image_le
  rw [Finset.card_range, Finset.card_range] at h3
  omega

theorem reach_of_min {O : VOrbit} {fA fB : Nat → Nat}
    (hinj : ∀ i < n, ∀ j < n, O.pts[i]! = O.pts[j]! → i = j)
    (hao : ∀ i < n, ap O.alpha i < n ∧ O.pts[ap O.alpha i]! = fA O.pts[i]!)
    (hbo : ∀ i < n, ap O.beta i < n ∧ O.pts[ap O.beta i]! = fB O.pts[i]!)
    (h0 : 0 < n) (hmem : ∀ i < n, O.pts[i]! ∈ R)
    (hmin : ∀ S : Set Nat, O.pts[0]! ∈ S → (∀ x ∈ S, fA x ∈ S ∧ fB x ∈ S) → ∀ x ∈ R, x ∈ S) :
    ∀ i < n, Reach (· ∈ #[0, 1]) (tf O) 0 i := by
  have key := hmin {x | ∃ i < n, Reach (· ∈ #[0, 1]) (tf O) 0 i ∧ O.pts[i]! = x}
    ⟨0, h0, Reach.root, rfl⟩ (by
      rintro x ⟨i, hi, hr, rfl⟩
      refine ⟨⟨ap O.alpha i, (hao i hi).1, ?_, (hao i hi).2⟩,
        ⟨ap O.beta i, (hbo i hi).1, ?_, (hbo i hi).2⟩⟩
      · exact Reach.step (l := 0) hr (by simp)
      · exact Reach.step (l := 1) hr (by simp))
  intro i hi
  obtain ⟨j, hj, hr, e⟩ := key _ (hmem i hi)
  rwa [hinj j hj i hi e] at hr

theorem reach_of_parents {O : VOrbit}
    (hpar : ∀ y, 0 < y → y < n → ∃ p < y, ap O.alpha p = y ∨ ap O.beta p = y) :
    ∀ i < n, Reach (· ∈ #[0, 1]) (tf O) 0 i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      exact Reach.root
    · obtain ⟨p, hp, e | e⟩ := hpar i h0 hi
      · rw [← e]
        exact Reach.step (l := 0) (ih p hp (by omega)) (by simp)
      · rw [← e]
        exact Reach.step (l := 1) (ih p hp (by omega)) (by simp)

theorem others_of {O : VOrbit} {others : List Nat} (hsz : O.pts.size = n)
    (hmem : ∀ i < n, O.pts[i]! ∈ R) (hoth : ∀ w ∈ others, w ∉ R) :
    (others.all fun w => !O.pts.contains w) = true := by
  rw [List.all_eq_true]
  intro w hw
  rw [Bool.not_eq_true']
  by_contra hc
  rw [Bool.not_eq_false, Array.contains_iff_mem] at hc
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hc
  have h1 := hmem i (by omega)
  rw [getElem!_pos O.pts i hi, e] at h1
  exact hoth w hw h1

end CFSG.KC.VOrbFull

end
