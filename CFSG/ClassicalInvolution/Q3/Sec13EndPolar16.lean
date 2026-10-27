module

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.IntervalCases
public import CFSG.ClassicalInvolution.Q3.Sec13EndSympForm
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Polar

variable {V : Type*} [CommGroup V]

private theorem p16_zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem p16_zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

private theorem p16_self_eq_add : ∀ c : ZMod 2, c = c + c → c = 0 := by decide

private theorem p16_ncard_eq {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    {x | P x}.ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card']
  simp

private theorem p16_four_pow : ∀ (n : ℕ) (G : Type _) [CommGroup G] [Finite G]
    (B : G → G → ZMod 2), Nat.card G = n → SympForm B → ∃ m : ℕ, n = 4 ^ m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ B hcard hB
  by_cases hx : ∃ x : G, x ≠ 1
  swap
  · push_neg at hx
    have h1 : Nat.card G = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => by rw [hx a, hx b]⟩, ⟨1⟩⟩
    exact ⟨0, by rw [← hcard, h1]; rfl⟩
  obtain ⟨x, hx1⟩ := hx
  have hB1 : ∀ c : G, B c 1 = 0 := fun c => p16_self_eq_add _ (by
    have h := hB.mul_right c 1 1
    rw [mul_one] at h
    exact h)
  obtain ⟨y, hy⟩ : ∃ y : G, B x y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx1 (hB.nondeg x hcon)
  have hxy : B x y = 1 := (p16_zmod2_cases _).resolve_left hy
  have hyx : B y x = 1 := (hB.symm x y).symm.trans hxy
  have hw : ∀ c d : ZMod 2, ∃ w : G, B x w = c ∧ B y w = d ∧
      ∀ k : G, B k x = 0 → B k y = 0 → B k w = 0 := by
    intro c d
    rcases p16_zmod2_cases c with rfl | rfl <;> rcases p16_zmod2_cases d with rfl | rfl
    · exact ⟨1, hB1 x, hB1 y, fun k _ _ => hB1 k⟩
    · exact ⟨x, hB.alt x, hyx, fun k hk _ => hk⟩
    · exact ⟨y, hxy, hB.alt y, fun k _ hk => hk⟩
    · refine ⟨x * y, ?_, ?_, fun k hk1 hk2 => ?_⟩
      · rw [hB.mul_right, hB.alt, hxy, zero_add]
      · rw [hB.mul_right, hyx, hB.alt, add_zero]
      · rw [hB.mul_right, hk1, hk2, add_zero]
  let ψ : G →* Multiplicative (ZMod 2 × ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (B x g, B y g)
      map_one' := by
        show Multiplicative.ofAdd (B x 1, B y 1) = 1
        rw [hB1 x, hB1 y]
        rfl
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (B x (g * h), B y (g * h)) =
          Multiplicative.ofAdd (B x g, B y g) * Multiplicative.ofAdd (B x h, B y h)
        rw [hB.mul_right x g h, hB.mul_right y g h, ← ofAdd_add]
        rfl }
  have hψ : Function.Surjective ψ := by
    intro c
    obtain ⟨w, hwx, hwy, -⟩ := hw (Multiplicative.toAdd c).1 (Multiplicative.toAdd c).2
    refine ⟨w, ?_⟩
    show Multiplicative.ofAdd (B x w, B y w) = c
    rw [hwx, hwy]
    simp
  have hKidx : ψ.ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top]
    show Nat.card (ZMod 2 × ZMod 2) = 4
    rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
  have hKmem : ∀ g : G, g ∈ ψ.ker ↔ B x g = 0 ∧ B y g = 0 := by
    intro g
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (B x g, B y g) = 1 ↔ _
    rw [ofAdd_eq_one, Prod.mk_eq_zero]
  have hBK : SympForm (fun u v : ψ.ker => B u.1 v.1) := by
    refine
      { sq_eq_one := fun a => Subtype.ext (hB.sq_eq_one a.1)
        mul_left := fun a a' b => hB.mul_left a.1 a'.1 b.1
        mul_right := fun a b b' => hB.mul_right a.1 b.1 b'.1
        alt := fun a => hB.alt a.1
        nondeg := ?_ }
    intro a ha
    apply Subtype.ext
    show a.1 = 1
    apply hB.nondeg a.1
    intro g
    have haK := (hKmem a.1).1 a.2
    obtain ⟨w, hwx, hwy, hwk⟩ := hw (B x g) (B y g)
    have hg' : g * w ∈ ψ.ker := by
      rw [hKmem]
      constructor
      · rw [hB.mul_right, hwx, p16_zmod2_add_self]
      · rw [hB.mul_right, hwy, p16_zmod2_add_self]
    have h1 := ha ⟨g * w, hg'⟩
    have h2 : B a.1 w = 0 :=
      hwk a.1 (by rw [hB.symm]; exact haK.1) (by rw [hB.symm]; exact haK.2)
    have hgeq : g = g * w * w := by rw [mul_assoc, hB.sq_eq_one w, mul_one]
    rw [hgeq, hB.mul_right]
    exact (by rw [h1, h2, add_zero] : B a.1 (g * w) + B a.1 w = 0)
  have hcardK : Nat.card G = Nat.card ψ.ker * 4 := by
    rw [← hKidx]
    exact (Subgroup.card_mul_index ψ.ker).symm
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  obtain ⟨m, hm⟩ := ih (Nat.card ψ.ker) (by omega) ψ.ker (fun u v => B u.1 v.1) rfl hBK
  exact ⟨m + 1, by rw [← hcard, hcardK, hm, pow_succ]⟩

private def p16Ext (hsq : ∀ g : V, g * g = 1) (H : Subgroup V) (y : V) : Subgroup V where
  carrier := {g | g ∈ H ∨ y * g ∈ H}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (H.mul_mem ha hb)
    · refine Or.inr ?_
      have e : y * (a * b) = (y * b) * a := by ac_rfl
      rw [e]
      exact H.mul_mem hb ha
    · refine Or.inr ?_
      have e : y * (a * b) = (y * a) * b := by ac_rfl
      rw [e]
      exact H.mul_mem ha hb
    · refine Or.inl ?_
      have e : (y * a) * (y * b) = a * b := by
        rw [show (y * a) * (y * b) = (y * y) * (a * b) by ac_rfl, hsq y, one_mul]
      rw [← e]
      exact H.mul_mem ha hb
  one_mem' := Or.inl H.one_mem
  inv_mem' := by
    intro g hg
    rw [inv_eq_of_mul_eq_one_right (hsq g)]
    exact hg

private theorem p16_mem_ext_iff (hsq : ∀ g : V, g * g = 1) (H : Subgroup V) (y g : V) :
    g ∈ p16Ext hsq H y ↔ g ∈ H ∨ y * g ∈ H := Iff.rfl

private theorem p16_natCard_ext_le [Finite V] (hsq : ∀ g : V, g * g = 1) (H : Subgroup V)
    (y : V) : Nat.card (p16Ext hsq H y) ≤ 2 * Nat.card H := by
  have hsub : ((p16Ext hsq H y : Subgroup V) : Set V) ⊆
      (H : Set V) ∪ (fun h => y * h) '' (H : Set V) := by
    intro g hg
    rcases hg with hg | hg
    · exact Or.inl hg
    · refine Or.inr ⟨y * g, hg, ?_⟩
      show y * (y * g) = g
      rw [← mul_assoc, hsq y, one_mul]
  have h1 : Nat.card (p16Ext hsq H y) = ((p16Ext hsq H y : Subgroup V) : Set V).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card H = (H : Set V).ncard := Nat.card_coe_set_eq _
  have h3 := Set.ncard_le_ncard hsub
  have h4 := Set.ncard_union_le (H : Set V) ((fun h => y * h) '' (H : Set V))
  rw [Set.ncard_image_of_injective _ (mul_right_injective y)] at h4
  rw [h1, h2]
  omega

private theorem p16_natCard_closure_le [Finite V] (hsq : ∀ g : V, g * g = 1) (T : Finset V) :
    Nat.card (Subgroup.closure (T : Set V)) ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp
  | insert y T hyT ih =>
    rw [Finset.card_insert_of_notMem hyT, pow_succ]
    have hle : Subgroup.closure ((insert y T : Finset V) : Set V) ≤
        p16Ext hsq (Subgroup.closure (T : Set V)) y := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · refine Or.inr ?_
        rw [hsq x]
        exact (Subgroup.closure _).one_mem
      · exact Or.inl (Subgroup.subset_closure hx)
    calc Nat.card (Subgroup.closure ((insert y T : Finset V) : Set V))
        ≤ Nat.card (p16Ext hsq (Subgroup.closure (T : Set V)) y) :=
          Subgroup.card_le_of_le hle
      _ ≤ 2 * Nat.card (Subgroup.closure (T : Set V)) := p16_natCard_ext_le hsq _ y
      _ ≤ 2 * 2 ^ T.card := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ T.card * 2 := by ring

private theorem p16_natCard_closure_pairs [Finite V] (hsq : ∀ g : V, g * g = 1) {z : V}
    (hz1 : z ≠ 1) : ∀ (n : ℕ) (X : Finset V), X.card = 2 * n → (∀ x ∈ X, z * x ∈ X) →
      Nat.card (Subgroup.closure (insert z (X : Set V))) ≤ 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro X hX _
    classical
    have hX0 : X = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hX0
    have h := p16_natCard_closure_le hsq {z}
    simpa using h
  | succ n ih =>
    intro X hX hzX
    classical
    obtain ⟨x, hx⟩ : X.Nonempty := Finset.card_pos.1 (by omega)
    have hzx : z * x ∈ X := hzX x hx
    have hne : z * x ≠ x := fun h => hz1 (mul_eq_right.1 h)
    set X' : Finset V := (X.erase x).erase (z * x) with hX'
    have hmemX' : ∀ y, y ∈ X' ↔ y ∈ X ∧ y ≠ x ∧ y ≠ z * x := by
      intro y
      simp only [hX', Finset.mem_erase]
      tauto
    have hcard : X'.card = 2 * n := by
      have h1 : (X.erase x).card = X.card - 1 := Finset.card_erase_of_mem hx
      have hzx' : z * x ∈ X.erase x := Finset.mem_erase.2 ⟨hne, hzx⟩
      have h2 : X'.card = (X.erase x).card - 1 := Finset.card_erase_of_mem hzx'
      omega
    have hX'z : ∀ y ∈ X', z * y ∈ X' := by
      intro y hy
      obtain ⟨hyX, hyx, hyzx⟩ := (hmemX' y).1 hy
      rw [hmemX']
      refine ⟨hzX y hyX, ?_, ?_⟩
      · intro h
        apply hyzx
        rw [← h, ← mul_assoc, hsq z, one_mul]
      · intro h
        apply hyx
        have h' : z * (z * y) = z * (z * x) := by rw [h]
        rw [← mul_assoc, hsq z, one_mul, ← mul_assoc, hsq z, one_mul] at h'
        exact h'
    have hle : Subgroup.closure (insert z (X : Set V)) ≤
        p16Ext hsq (Subgroup.closure (insert z (X' : Set V))) x := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with hw | hw
      · rw [hw]
        exact Or.inl (Subgroup.subset_closure (Set.mem_insert z (X' : Set V)))
      · by_cases hwx : w = x
        · subst hwx
          refine Or.inr ?_
          rw [hsq w]
          exact (Subgroup.closure _).one_mem
        · by_cases hwzx : w = z * x
          · subst hwzx
            refine Or.inr ?_
            have e : x * (z * x) = z := by
              rw [show x * (z * x) = z * (x * x) by ac_rfl, hsq x, mul_one]
            rw [e]
            exact Subgroup.subset_closure (Set.mem_insert z (X' : Set V))
          · refine Or.inl (Subgroup.subset_closure ?_)
            right
            exact (hmemX' w).2 ⟨hw, hwx, hwzx⟩
    have hX'card := ih X' hcard hX'z
    calc Nat.card (Subgroup.closure (insert z (X : Set V)))
        ≤ Nat.card (p16Ext hsq (Subgroup.closure (insert z (X' : Set V))) x) :=
          Subgroup.card_le_of_le hle
      _ ≤ 2 * Nat.card (Subgroup.closure (insert z (X' : Set V))) :=
          p16_natCard_ext_le hsq _ x
      _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 hX'card
      _ = 2 ^ (n + 1 + 1) := by ring

theorem SympForm.exists_natCard_eq_four_pow [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) :
    ∃ m : ℕ, Nat.card V = 4 ^ m :=
  p16_four_pow (Nat.card V) V B rfl hB

theorem natCard_closure_le [Finite V] (hsq : ∀ a : V, a * a = 1) (T : Finset V) :
    Nat.card (Subgroup.closure (T : Set V)) ≤ 2 ^ T.card :=
  p16_natCard_closure_le hsq T

@[expose] def nbr (B : V → V → ZMod 2) (S : Set V) (p : V) : Set V :=
  {x | x ∈ S ∧ x ≠ p ∧ B p x = 0}

@[expose] def far (B : V → V → ZMod 2) (S : Set V) (z : V) : Set V :=
  {x | x ∈ S ∧ B z x = 1}

@[expose] def qPairs (B : V → V → ZMod 2) (S : Set V) (z : V) : Set (V × V) :=
  {q | q.1 ∈ nbr B S z ∧ q.2 ∈ nbr B S z ∧ B q.1 q.2 = 0 ∧ q.2 ≠ q.1 ∧ q.2 ≠ z * q.1}

structure PointSet (B : V → V → ZMod 2) (S : Set V) (a : ℕ) : Prop where
  one_notMem : (1 : V) ∉ S
  mul_mem_of_orth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → B x y = 0 → x * y ∈ S
  card_nbr : ∀ p ∈ S, (nbr B S p).ncard = 2 * a

namespace PointSet

variable {B : V → V → ZMod 2} {S : Set V} {a : ℕ}

theorem mul_mem_nbr [Finite V] (hB : SympForm B) (hS : PointSet B S a) {p x : V} (hp : p ∈ S)
    (hx : x ∈ nbr B S p) : p * x ∈ nbr B S p ∧ p * x ≠ x := by
  obtain ⟨hxS, hxp, hBpx⟩ := hx
  have hx1 : x ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hxS)
  have hp1 : p ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hp)
  refine ⟨⟨hS.mul_mem_of_orth p hp x hxS (Ne.symm hxp) hBpx, ?_, ?_⟩, ?_⟩
  · intro h
    exact hx1 (mul_eq_left.1 h)
  · rw [hB.mul_right, hB.alt, hBpx, add_zero]
  · intro h
    exact hp1 (mul_eq_right.1 h)

private theorem mem_nbr_iff {p x : V} : x ∈ nbr B S p ↔ x ∈ S ∧ x ≠ p ∧ B p x = 0 := Iff.rfl

private theorem mem_far_iff {z s : V} : s ∈ far B S z ↔ s ∈ S ∧ B z s = 1 := Iff.rfl

private theorem mem_qPairs_iff {z j y : V} : (j, y) ∈ qPairs B S z ↔
    j ∈ nbr B S z ∧ y ∈ nbr B S z ∧ B j y = 0 ∧ y ≠ j ∧ y ≠ z * j := Iff.rfl

private theorem p16_card_nbr_pair [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z f : V}
    (hz : z ∈ S) (hf : B z f = 1) : {j | j ∈ nbr B S z ∧ B j f = 0}.ncard = a := by
  have hN : (nbr B S z).ncard = 2 * a := hS.card_nbr z hz
  have hTN : {j | j ∈ nbr B S z ∧ B j f = 0} ⊆ nbr B S z := fun j hj => hj.1
  have hTimg : nbr B S z \ {j | j ∈ nbr B S z ∧ B j f = 0} =
      (fun j => z * j) '' {j | j ∈ nbr B S z ∧ B j f = 0} := by
    ext y
    constructor
    · rintro ⟨hyN, hyT⟩
      have hy1 : B y f = 1 := by
        rcases p16_zmod2_cases (B y f) with h | h
        · exact absurd (show y ∈ {j | j ∈ nbr B S z ∧ B j f = 0} from ⟨hyN, h⟩) hyT
        · exact h
      refine ⟨z * y, ⟨(mul_mem_nbr hB hS hz hyN).1, ?_⟩, ?_⟩
      · show B (z * y) f = 0
        rw [hB.mul_left, hf, hy1]
        decide
      · show z * (z * y) = y
        rw [← mul_assoc, hB.sq_eq_one z, one_mul]
    · rintro ⟨j, hjT, rfl⟩
      refine ⟨(mul_mem_nbr hB hS hz hjT.1).1, fun h => ?_⟩
      have h2 : B (z * j) f = 0 := h.2
      rw [hB.mul_left, hf, hjT.2, add_zero] at h2
      exact absurd h2 (by decide)
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hTN
  rw [hTimg, Set.ncard_image_of_injective _ (mul_right_injective z)] at h1
  rw [hN] at h1
  omega

theorem card_far_nbr [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z j : V} (hz : z ∈ S)
    (hj : j ∈ nbr B S z) :
    {s | s ∈ far B S z ∧ B j s = 0}.ncard + {y | (j, y) ∈ qPairs B S z}.ncard + 2 = 2 * a := by
  have hj' := hj
  obtain ⟨hjS, hjz, hzj⟩ := hj
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hz)
  have hjz' : B j z = 0 := (hB.symm j z).trans hzj
  have hzjS : z * j ∈ S := hS.mul_mem_of_orth z hz j hjS (Ne.symm hjz) hzj
  have hkey : nbr B S j = insert z (insert (z * j) ({y | (j, y) ∈ qPairs B S z} ∪
      {s | s ∈ far B S z ∧ B j s = 0})) := by
    ext x
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_union, mem_nbr_iff]
    constructor
    · rintro ⟨hxS, hxj, hjx⟩
      by_cases hzx : B z x = 0
      · by_cases hxz : x = z
        · exact Or.inl hxz
        · by_cases hxzj : x = z * j
          · exact Or.inr (Or.inl hxzj)
          · exact Or.inr (Or.inr (Or.inl
              ((mem_qPairs_iff).2 ⟨hj', (mem_nbr_iff).2 ⟨hxS, hxz, hzx⟩, hjx, hxj, hxzj⟩)))
      · have hzx1 : B z x = 1 := (p16_zmod2_cases _).resolve_left hzx
        exact Or.inr (Or.inr (Or.inr ⟨(mem_far_iff).2 ⟨hxS, hzx1⟩, hjx⟩))
    · rintro (rfl | rfl | hQ | hF)
      · exact ⟨hz, fun h => hjz h.symm, hjz'⟩
      · refine ⟨hzjS, fun h => hz1 (mul_eq_right.1 h), ?_⟩
        rw [hB.mul_right, hjz', hB.alt, add_zero]
      · have hQ' : (j, x) ∈ qPairs B S z := hQ
        obtain ⟨-, hxN, hjx, hxj, -⟩ := (mem_qPairs_iff).1 hQ'
        exact ⟨((PointSet.mem_nbr_iff).1 hxN).1, hxj, hjx⟩
      · have hF' : x ∈ far B S z ∧ B j x = 0 := hF
        refine ⟨hF'.1.1, fun h => ?_, hF'.2⟩
        have h1 : B z x = 1 := hF'.1.2
        rw [h, hzj] at h1
        exact absurd h1 (by decide)
  have hdisjQF : Disjoint {y | (j, y) ∈ qPairs B S z} {s | s ∈ far B S z ∧ B j s = 0} := by
    rw [Set.disjoint_left]
    intro y hQ hF
    have hQ' : (j, y) ∈ qPairs B S z := hQ
    have hF' : y ∈ far B S z ∧ B j y = 0 := hF
    have h1 : B z y = 0 := ((PointSet.mem_nbr_iff).1 ((mem_qPairs_iff).1 hQ').2.1).2.2
    have h2 : B z y = 1 := hF'.1.2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hz_notin : z ∉ insert (z * j) ({y | (j, y) ∈ qPairs B S z} ∪
      {s | s ∈ far B S z ∧ B j s = 0}) := by
    rintro (h | h | h)
    · have hj1 : j = 1 := mul_left_cancel (show z * j = z * 1 by rw [mul_one]; exact h.symm)
      exact hS.one_notMem (hj1 ▸ hjS)
    · have hQ' : (j, z) ∈ qPairs B S z := h
      exact ((PointSet.mem_nbr_iff).1 ((mem_qPairs_iff).1 hQ').2.1).2.1 rfl
    · have hF' : z ∈ far B S z ∧ B j z = 0 := h
      have h1 : B z z = 1 := hF'.1.2
      rw [hB.alt] at h1
      exact absurd h1 (by decide)
  have hzj_notin : z * j ∉ {y | (j, y) ∈ qPairs B S z} ∪
      {s | s ∈ far B S z ∧ B j s = 0} := by
    rintro (h | h)
    · have hQ' : (j, z * j) ∈ qPairs B S z := h
      exact ((mem_qPairs_iff).1 hQ').2.2.2.2 rfl
    · have hF' : z * j ∈ far B S z ∧ B j (z * j) = 0 := h
      have h1 : B z (z * j) = 1 := hF'.1.2
      rw [hB.mul_right, hB.alt, hzj, zero_add] at h1
      exact absurd h1 (by decide)
  have hcard := hS.card_nbr j hjS
  rw [hkey, Set.ncard_insert_of_notMem hz_notin, Set.ncard_insert_of_notMem hzj_notin,
    Set.ncard_union_eq hdisjQF] at hcard
  omega

theorem card_far_mul [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z : V} (hz : z ∈ S) :
    a * (far B S z).ncard + (qPairs B S z).ncard + 4 * a = 4 * a * a := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  set N : Finset V := Finset.univ.filter (fun j => j ∈ nbr B S z) with hNdef
  set F : Finset V := Finset.univ.filter (fun s => s ∈ far B S z) with hFdef
  set Q : Finset (V × V) := Finset.univ.filter (fun q => q ∈ qPairs B S z) with hQdef
  have hNc : N.card = 2 * a := by
    rw [hNdef, ← p16_ncard_eq (fun j => j ∈ nbr B S z)]
    exact hS.card_nbr z hz
  have hFc : (far B S z).ncard = F.card := p16_ncard_eq (fun s => s ∈ far B S z)
  have hQc : (qPairs B S z).ncard = Q.card := p16_ncard_eq (fun q => q ∈ qPairs B S z)
  have hA : ∀ j ∈ N, (F.filter (fun s => B j s = 0)).card +
      (Finset.univ.filter (fun y => (j, y) ∈ qPairs B S z)).card + 2 = 2 * a := by
    intro j hj
    have hjn : j ∈ nbr B S z := (Finset.mem_filter.1 hj).2
    have h := card_far_nbr hB hS hz hjn
    rw [p16_ncard_eq (fun s => s ∈ far B S z ∧ B j s = 0),
      p16_ncard_eq (fun y => (j, y) ∈ qPairs B S z)] at h
    rw [hFdef, Finset.filter_filter]
    exact h
  have hQsum : Q.card = ∑ j ∈ N, (Finset.univ.filter (fun y => (j, y) ∈ qPairs B S z)).card := by
    rw [hQdef, Finset.card_filter, Fintype.sum_prod_type, hNdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rw [Finset.card_filter]
    · apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      intro hq
      exact hj ((mem_qPairs_iff).1 hq).1
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := N) (t := F) (r := fun j s => B j s = 0)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  have hD : ∀ s ∈ F, (N.filter (fun j => B j s = 0)).card = a := by
    intro s hs
    have hsf : s ∈ far B S z := (Finset.mem_filter.1 hs).2
    have h := p16_card_nbr_pair hB hS hz hsf.2
    rw [p16_ncard_eq (fun j => j ∈ nbr B S z ∧ B j s = 0)] at h
    rw [hNdef, Finset.filter_filter]
    exact h
  have hsB : ∑ s ∈ F, (N.filter (fun j => B j s = 0)).card = F.card * a := by
    rw [Finset.sum_congr rfl hD, Finset.sum_const, smul_eq_mul]
  have hsA := Finset.sum_congr rfl hA
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, hNc,
    smul_eq_mul, smul_eq_mul] at hsA
  rw [hFc, hQc, hQsum]
  rw [hdc, hsB] at hsA
  nlinarith [hsA]

theorem card_mul [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z : V} (hz : z ∈ S) :
    a * S.ncard + (qPairs B S z).ncard + 3 * a = 6 * a * a := by
  have hSeq : S = {z} ∪ (nbr B S z ∪ far B S z) := by
    ext x
    constructor
    · intro hx
      by_cases hxz : x = z
      · exact Or.inl (Set.mem_singleton_iff.2 hxz)
      · by_cases hzx : B z x = 0
        · exact Or.inr (Or.inl ((mem_nbr_iff).2 ⟨hx, hxz, hzx⟩))
        · exact Or.inr (Or.inr ((mem_far_iff).2 ⟨hx, (p16_zmod2_cases _).resolve_left hzx⟩))
    · rintro (h | h | h)
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hz
      · exact ((PointSet.mem_nbr_iff).1 h).1
      · exact ((mem_far_iff).1 h).1
  have hdisj1 : Disjoint ({z} : Set V) (nbr B S z ∪ far B S z) := by
    rw [Set.disjoint_singleton_left]
    rintro (h | h)
    · exact ((PointSet.mem_nbr_iff).1 h).2.1 rfl
    · have h1 : B z z = 1 := ((mem_far_iff).1 h).2
      rw [hB.alt] at h1
      exact absurd h1 (by decide)
  have hdisj2 : Disjoint (nbr B S z) (far B S z) := by
    rw [Set.disjoint_left]
    intro x hn hf
    have h1 : B z x = 0 := ((PointSet.mem_nbr_iff).1 hn).2.2
    have h2 : B z x = 1 := ((mem_far_iff).1 hf).2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hcardS : S.ncard = 1 + (nbr B S z).ncard + (far B S z).ncard := by
    calc S.ncard = ({z} ∪ (nbr B S z ∪ far B S z) : Set V).ncard := congrArg Set.ncard hSeq
      _ = 1 + (nbr B S z).ncard + (far B S z).ncard := by
        rw [Set.ncard_union_eq hdisj1, Set.ncard_singleton, Set.ncard_union_eq hdisj2]
        ring
  have key := card_far_mul hB hS hz
  rw [hcardS, hS.card_nbr z hz]
  nlinarith [key]

private theorem p16_even_card_of_invol {α : Type*} [DecidableEq α] (f : α → α)
    (hff : ∀ x, f (f x) = x) : ∀ (n : ℕ) (X : Finset α), X.card = n →
      (∀ x ∈ X, f x ≠ x) → (∀ x ∈ X, f x ∈ X) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hX hne hinv
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [Finset.card_empty] at hX
    rw [← hX]
    exact ⟨0, rfl⟩
  · have hfx : f x ∈ X := hinv x hx
    have hxfx : f x ≠ x := hne x hx
    have hfx' : f x ∈ X.erase x := Finset.mem_erase.2 ⟨hxfx, hfx⟩
    have hcard : ((X.erase x).erase (f x)).card + 2 = X.card := by
      have h1 : (X.erase x).card = X.card - 1 := Finset.card_erase_of_mem hx
      have h2 : ((X.erase x).erase (f x)).card = (X.erase x).card - 1 :=
        Finset.card_erase_of_mem hfx'
      have h4 : 0 < (X.erase x).card := Finset.card_pos.2 ⟨f x, hfx'⟩
      omega
    have hYX : ∀ y ∈ (X.erase x).erase (f x), y ∈ X := fun y hy =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hYinv : ∀ y ∈ (X.erase x).erase (f x), f y ∈ (X.erase x).erase (f x) := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      obtain ⟨h1, h2, h3⟩ := hy
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun h => h2 (by have := congrArg f h; rwa [hff, hff] at this),
        fun h => h1 (by have := congrArg f h; rwa [hff] at this), hinv y h3⟩
    obtain ⟨k, hk⟩ := ih ((X.erase x).erase (f x)).card (by omega) _ rfl
      (fun y hy => hne y (hYX y hy)) hYinv
    rw [← hX]
    exact ⟨k + 1, by omega⟩

open Classical in
private theorem p16_L_comm {z : V} (hB : SympForm B) (j : V) :
    ({z * j, z * (z * j)} : Finset V) = {j, z * j} := by
  rw [← mul_assoc, hB.sq_eq_one z, one_mul, Finset.pair_comm]

open Classical in
private theorem p16_L_of_mem {z : V} (hB : SympForm B) {j u : V}
    (hu : u ∈ ({j, z * j} : Finset V)) : ({u, z * u} : Finset V) = {j, z * j} := by
  rcases Finset.mem_insert.1 hu with h | h
  · rw [h]
  · rw [Finset.mem_singleton.1 h, p16_L_comm hB]

open Classical in
private theorem p16_line_nbr [Finite V] {z : V} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S)
    {y v : V} (hy : y ∈ nbr B S z) (hv : v ∈ ({y, z * y} : Finset V)) : v ∈ nbr B S z := by
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]
    exact hy
  · rw [Finset.mem_singleton.1 h]
    exact (mul_mem_nbr hB hS hz hy).1

open Classical in
private theorem p16_mem_qPairs_iff_L {z u v : V} (hB : SympForm B) :
    (u, v) ∈ qPairs B S z ↔ u ∈ nbr B S z ∧ v ∈ nbr B S z ∧ B u v = 0 ∧
      ({v, z * v} : Finset V) ≠ {u, z * u} := by
  rw [mem_qPairs_iff]
  constructor
  · rintro ⟨hu, hv, hB0, hvu, hvzu⟩
    refine ⟨hu, hv, hB0, fun h => ?_⟩
    have hmem : v ∈ ({v, z * v} : Finset V) := Finset.mem_insert_self _ _
    rw [h] at hmem
    rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hvu h1
    · exact hvzu (Finset.mem_singleton.1 h1)
  · rintro ⟨hu, hv, hB0, hne⟩
    refine ⟨hu, hv, hB0, fun h => hne ?_, fun h => hne ?_⟩
    · rw [h]
    · rw [h]
      exact p16_L_comm hB u

open Classical in
private theorem p16_B_L_inv [Finite V] {z u v j y : V} (hB : SympForm B) (hS : PointSet B S a)
    (hz : z ∈ S) (hj : j ∈ nbr B S z) (hy : y ∈ nbr B S z) (hu : u ∈ ({j, z * j} : Finset V))
    (hv : v ∈ ({y, z * y} : Finset V)) : B u v = B j y := by
  have hBzv : B z v = 0 := ((PointSet.mem_nbr_iff).1 (p16_line_nbr hB hS hz hy hv)).2.2
  have hBjz : B j z = 0 := (hB.symm j z).trans ((PointSet.mem_nbr_iff).1 hj).2.2
  have h1 : B u v = B j v := by
    rcases Finset.mem_insert.1 hu with h | h
    · rw [h]
    · rw [Finset.mem_singleton.1 h, hB.mul_left, hBzv, zero_add]
  have h2 : B j v = B j y := by
    rcases Finset.mem_insert.1 hv with h | h
    · rw [h]
    · rw [Finset.mem_singleton.1 h, hB.mul_right, hBjz, zero_add]
  rw [h1, h2]

theorem eight_dvd_card_qPairs [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z : V}
    (hz : z ∈ S) : 8 ∣ (qPairs B S z).ncard := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hz)
  set Q : Finset (V × V) := Finset.univ.filter (fun q => q ∈ qPairs B S z) with hQdef
  have hQc : (qPairs B S z).ncard = Q.card := p16_ncard_eq (fun q => q ∈ qPairs B S z)
  set φ : V × V → Finset V × Finset V := fun q => ({q.1, z * q.1}, {q.2, z * q.2}) with hφ
  set Qt : Finset (Finset V × Finset V) := Q.image φ with hQt
  have hfib : ∀ q0 ∈ Q, (Q.filter (fun q => φ q = φ q0)).card = 4 := by
    intro q0 hq0
    obtain ⟨hj0, hy0, hjy0, hne0⟩ := (p16_mem_qPairs_iff_L hB).1 (Finset.mem_filter.1 hq0).2
    have hne1 : q0.1 ≠ z * q0.1 := fun h => hz1 (mul_eq_right.1 h.symm)
    have hne2 : q0.2 ≠ z * q0.2 := fun h => hz1 (mul_eq_right.1 h.symm)
    have hprod : Q.filter (fun q => φ q = φ q0) =
        ({q0.1, z * q0.1} : Finset V) ×ˢ ({q0.2, z * q0.2} : Finset V) := by
      ext ⟨u, v⟩
      simp only [hQdef, hφ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Prod.mk.injEq]
      constructor
      · rintro ⟨-, h1, h2⟩
        constructor
        · rw [← h1]
          exact Finset.mem_insert_self _ _
        · rw [← h2]
          exact Finset.mem_insert_self _ _
      · rintro ⟨h1, h2⟩
        have e1 := p16_L_of_mem hB h1
        have e2 := p16_L_of_mem hB h2
        refine ⟨(p16_mem_qPairs_iff_L hB).2 ⟨p16_line_nbr hB hS hz hj0 h1,
          p16_line_nbr hB hS hz hy0 h2, (p16_B_L_inv hB hS hz hj0 hy0 h1 h2).trans hjy0, ?_⟩,
          e1, e2⟩
        rw [e1, e2]
        exact hne0
    rw [hprod, Finset.card_product, Finset.card_pair hne1, Finset.card_pair hne2]
  have hfibP : ∀ P ∈ Qt, (Q.filter (fun q => φ q = P)).card = 4 := by
    intro P hP
    obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.1 hP
    exact hfib q0 hq0
  have hQcard : Q.card = 4 * Qt.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := Qt)
      (fun q hq => Finset.mem_image_of_mem φ hq), Finset.sum_congr rfl hfibP, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hevn : Even Qt.card := by
    refine p16_even_card_of_invol Prod.swap (fun x => Prod.swap_swap x) _ Qt rfl ?_ ?_
    · intro P hP
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hP
      have hq' := (p16_mem_qPairs_iff_L hB).1 (Finset.mem_filter.1 hq).2
      intro h
      have h2 : ({q.2, z * q.2} : Finset V) = {q.1, z * q.1} := congrArg Prod.fst h
      exact hq'.2.2.2 h2
    · intro P hP
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hP
      have hq' := (p16_mem_qPairs_iff_L hB).1 (Finset.mem_filter.1 hq).2
      have hq2 : (q.2, q.1) ∈ qPairs B S z := (p16_mem_qPairs_iff_L hB).2
        ⟨hq'.2.1, hq'.1, (hB.symm _ _).trans hq'.2.2.1, fun h => hq'.2.2.2 h.symm⟩
      exact Finset.mem_image.2 ⟨(q.2, q.1), Finset.mem_filter.2 ⟨Finset.mem_univ _, hq2⟩, rfl⟩
  obtain ⟨k, hk⟩ := hevn
  rw [hQc, hQcard, hk]
  exact ⟨k, by ring⟩

private theorem p16_mul_mem_nbr_far [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z x y : V}
    (hx : x ∈ far B S z) (hy : y ∈ far B S z) (hxy : B x y = 0) (hne : x ≠ y) :
    x * y ∈ nbr B S z := by
  have hxS : x ∈ S := (mem_far_iff.1 hx).1
  have hyS : y ∈ S := (mem_far_iff.1 hy).1
  have hBzx : B z x = 1 := (mem_far_iff.1 hx).2
  have hBzy : B z y = 1 := (mem_far_iff.1 hy).2
  refine (mem_nbr_iff).2 ⟨hS.mul_mem_of_orth x hxS y hyS hne hxy, ?_, ?_⟩
  · intro h
    have hyx : y = x * z := by
      calc y = x * (x * y) := by rw [← mul_assoc, hB.sq_eq_one x, one_mul]
        _ = x * z := by rw [h]
    have h1 : B x y = B z x := by
      rw [hyx, hB.mul_right, hB.alt, zero_add, hB.symm x z]
    rw [hxy, hBzx] at h1
    exact absurd h1 (by decide)
  · rw [hB.mul_right, hBzx, hBzy]
    decide

private theorem p16_card_far_nbr_far [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z s : V}
    (hz : z ∈ S) (hs : s ∈ far B S z) :
    {t | t ∈ far B S z ∧ B s t = 0 ∧ t ≠ s}.ncard = a := by
  have hsS : s ∈ S := (mem_far_iff.1 hs).1
  have hBsz : B s z = 1 := by rw [hB.symm]; exact (mem_far_iff.1 hs).2
  have hA := p16_card_nbr_pair hB hS hsS hBsz
  have hsub : {j | j ∈ nbr B S s ∧ B j z = 0} ⊆ nbr B S s := fun j hj => hj.1
  have hcompl : nbr B S s \ {j | j ∈ nbr B S s ∧ B j z = 0} =
      {t | t ∈ far B S z ∧ B s t = 0 ∧ t ≠ s} := by
    ext t
    constructor
    · rintro ⟨htn, htA⟩
      obtain ⟨htS, hts, hst⟩ := (mem_nbr_iff).1 htn
      have hzt : B z t = 1 := by
        rcases p16_zmod2_cases (B z t) with h | h
        · exact absurd (show t ∈ {j | j ∈ nbr B S s ∧ B j z = 0} from
            ⟨htn, by rw [hB.symm]; exact h⟩) htA
        · exact h
      exact ⟨(mem_far_iff).2 ⟨htS, hzt⟩, hst, hts⟩
    · rintro ⟨htF, hst, hts⟩
      refine ⟨(mem_nbr_iff).2 ⟨(mem_far_iff.1 htF).1, hts, hst⟩, fun hA' => ?_⟩
      have h0 : B z t = 0 := by rw [hB.symm]; exact hA'.2
      rw [(mem_far_iff.1 htF).2] at h0
      exact absurd h0 (by decide)
  have hcard : (nbr B S s).ncard = 2 * a := hS.card_nbr s hsS
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hsub
  rw [hcompl, hA, hcard] at h1
  omega

private theorem p16_no_triangle [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z x y w : V}
    (hq : qPairs B S z = ∅) (hx : x ∈ far B S z) (hy : y ∈ far B S z) (hw : w ∈ far B S z)
    (hxy : B x y = 0) (hxw : B x w = 0) (hyw : B y w = 0)
    (hxy' : x ≠ y) (hxw' : x ≠ w) (hyw' : y ≠ w) : False := by
  have hxyN := p16_mul_mem_nbr_far hB hS hx hy hxy hxy'
  have hxwN := p16_mul_mem_nbr_far hB hS hx hw hxw hxw'
  have hyx : B y x = 0 := (hB.symm y x).trans hxy
  have hpair : (x * y, x * w) ∈ qPairs B S z := by
    rw [mem_qPairs_iff]
    refine ⟨hxyN, hxwN, ?_, ?_, ?_⟩
    · show B (x * y) (x * w) = 0
      rw [hB.mul_left, hB.mul_right, hB.mul_right, hB.alt, hxw, hyx, hyw]
      decide
    · intro h
      exact hyw' (mul_left_cancel h).symm
    · intro h
      have hw' : w = z * y := by
        calc w = x * (x * w) := by rw [← mul_assoc, hB.sq_eq_one x, one_mul]
          _ = x * (z * (x * y)) := by rw [h]
          _ = z * y := by
            rw [show x * (z * (x * y)) = z * y * (x * x) by ac_rfl, hB.sq_eq_one x, mul_one]
      have h1 : B y w = B z y := by
        rw [hw', hB.mul_right, hB.alt, add_zero, hB.symm y z]
      rw [hyw] at h1
      rw [(mem_far_iff.1 hy).2] at h1
      exact absurd h1 (by decide)
  rw [hq] at hpair
  exact hpair

private theorem p16_component_card [Finite V] (hB : SympForm B) (hS : PointSet B S a) {z : V}
    (hz : z ∈ S) (hq : qPairs B S z = ∅) (ha : 1 ≤ a) (C : Set V) (hCF : C ⊆ far B S z)
    (hCcl : ∀ x ∈ C, ∀ y ∈ far B S z, B x y = 0 → y ≠ x → y ∈ C) {x0 : V} (hx0 : x0 ∈ C) :
    2 * a ≤ C.ncard := by
  set G0 : Set V := {t | t ∈ far B S z ∧ B x0 t = 0 ∧ t ≠ x0} with hG0
  have hG0c : G0.ncard = a := p16_card_far_nbr_far hB hS hz (hCF hx0)
  have hne : G0.Nonempty := (Set.ncard_pos (Set.toFinite G0)).1 (by omega)
  obtain ⟨u, hu⟩ := hne
  have hu' : u ∈ far B S z ∧ B x0 u = 0 ∧ u ≠ x0 := hu
  have huC : u ∈ C := hCcl x0 hx0 u hu'.1 hu'.2.1 hu'.2.2
  set Gu : Set V := {t | t ∈ far B S z ∧ B u t = 0 ∧ t ≠ u} with hGu
  have hGuc : Gu.ncard = a := p16_card_far_nbr_far hB hS hz hu'.1
  have hx0Gu : x0 ∈ Gu := ⟨hCF hx0, (hB.symm u x0).trans hu'.2.1, Ne.symm hu'.2.2⟩
  have hGudiff : (Gu \ {x0}).ncard = a - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx0Gu, hGuc]
  have hd1 : Disjoint ({x0} : Set V) G0 :=
    Set.disjoint_singleton_left.2
      (fun h => (show x0 ∈ far B S z ∧ B x0 x0 = 0 ∧ x0 ≠ x0 from h).2.2 rfl)
  have hd2 : Disjoint ({x0} : Set V) (Gu \ {x0}) :=
    Set.disjoint_singleton_left.2 (fun h => h.2 rfl)
  have hd3 : Disjoint G0 (Gu \ {x0}) := by
    rw [Set.disjoint_left]
    intro w hwG0 hwGu
    have hwG0' : w ∈ far B S z ∧ B x0 w = 0 ∧ w ≠ x0 := hwG0
    have hwGu' : w ∈ far B S z ∧ B u w = 0 ∧ w ≠ u := hwGu.1
    exact p16_no_triangle hB hS hq (hCF hx0) hu'.1 hwG0'.1 hu'.2.1 hwG0'.2.1 hwGu'.2.1
      (Ne.symm hu'.2.2) (Ne.symm hwG0'.2.2) (Ne.symm hwGu'.2.2)
  have hT1 : ({x0} ∪ G0 : Set V).ncard = 1 + a := by
    rw [Set.ncard_union_eq hd1, Set.ncard_singleton, hG0c]
  have hT : ({x0} ∪ G0 ∪ (Gu \ {x0}) : Set V).ncard = 1 + a + (a - 1) := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hd2, hd3⟩), hT1, hGudiff]
  have hsub : ({x0} ∪ G0 ∪ (Gu \ {x0}) : Set V) ⊆ C := by
    intro w hw
    rcases hw with (hw | hw) | hw
    · rw [Set.mem_singleton_iff.1 hw]
      exact hx0
    · have hw' : w ∈ far B S z ∧ B x0 w = 0 ∧ w ≠ x0 := hw
      exact hCcl x0 hx0 w hw'.1 hw'.2.1 hw'.2.2
    · have hw' : w ∈ far B S z ∧ B u w = 0 ∧ w ≠ u := hw.1
      exact hCcl u huC w hw'.1 hw'.2.1 hw'.2.2
  have hle := Set.ncard_le_ncard hsub (Set.toFinite C)
  omega

theorem natCard_le_of_qPairs_eq_empty [Finite V] (hB : SympForm B) (hS : PointSet B S a)
    (hspan : Subgroup.closure S = ⊤) {z : V} (hz : z ∈ S) (hq : qPairs B S z = ∅) (ha : 2 ≤ a) :
    Nat.card V ≤ 2 ^ (a + 2) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hsq : ∀ g : V, g * g = 1 := hB.sq_eq_one
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hz)
  set E : Subgroup V := Subgroup.closure (insert z (nbr B S z : Set V)) with hEdef
  have hNfin : (nbr B S z).Finite := Set.toFinite _
  set X : Finset V := hNfin.toFinset with hXdef
  have hXc : X.card = 2 * a := by
    rw [hXdef, ← Set.ncard_eq_toFinset_card _ hNfin]
    exact hS.card_nbr z hz
  have hXcoe : (X : Set V) = nbr B S z := hNfin.coe_toFinset
  have hXz : ∀ x ∈ X, z * x ∈ X := by
    intro x hx
    rw [hXdef, Set.Finite.mem_toFinset] at hx ⊢
    exact (mul_mem_nbr hB hS hz hx).1
  have hEcard : Nat.card E ≤ 2 ^ (a + 1) := by
    have h := p16_natCard_closure_pairs hsq hz1 a X hXc hXz
    rw [hXcoe] at h
    exact h
  have hFcard : (far B S z).ncard + 4 = 4 * a := by
    have h := card_far_mul hB hS hz
    rw [hq, Set.ncard_empty] at h
    have ha0 : 0 < a := by omega
    apply Nat.eq_of_mul_eq_mul_left ha0
    nlinarith [h]
  have hFlt : (far B S z).ncard < 4 * a := by omega
  have hconn : ∀ s ∈ far B S z, ∀ x ∈ far B S z, s * x ∈ E := by
    intro s hs
    set A : Set V := {x | x ∈ far B S z ∧ s * x ∈ E} with hA
    set Bs : Set V := {x | x ∈ far B S z ∧ s * x ∉ E} with hBs
    have hsA : s ∈ A := ⟨hs, by rw [hsq s]; exact E.one_mem⟩
    have hAcl : ∀ x ∈ A, ∀ y ∈ far B S z, B x y = 0 → y ≠ x → y ∈ A := by
      intro x hx y hy hxy hyx
      refine ⟨hy, ?_⟩
      have hxyN : x * y ∈ nbr B S z :=
        p16_mul_mem_nbr_far hB hS hx.1 hy hxy (Ne.symm hyx)
      have hxyE : x * y ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ hxyN)
      have e : s * y = (s * x) * (x * y) := by
        rw [show (s * x) * (x * y) = s * (x * x) * y by ac_rfl, hsq x, mul_one]
      rw [e]
      exact E.mul_mem hx.2 hxyE
    have hBcl : ∀ x ∈ Bs, ∀ y ∈ far B S z, B x y = 0 → y ≠ x → y ∈ Bs := by
      intro x hx y hy hxy hyx
      refine ⟨hy, fun hsy => hx.2 ?_⟩
      have hyxN : y * x ∈ nbr B S z :=
        p16_mul_mem_nbr_far hB hS hy hx.1 ((hB.symm y x).trans hxy) hyx
      have hyxE : y * x ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ hyxN)
      have e : s * x = (s * y) * (y * x) := by
        rw [show (s * y) * (y * x) = s * (y * y) * x by ac_rfl, hsq y, mul_one]
      rw [e]
      exact E.mul_mem hsy hyxE
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨x1, hx1, hx1E⟩ := hcontra
    have hx1B : x1 ∈ Bs := ⟨hx1, hx1E⟩
    have hAc := p16_component_card hB hS hz hq (by omega) A (fun x hx => hx.1) hAcl hsA
    have hBc := p16_component_card hB hS hz hq (by omega) Bs (fun x hx => hx.1) hBcl hx1B
    have hdisj : Disjoint A Bs := Set.disjoint_left.2 (fun x hxA hxB => hxB.2 hxA.2)
    have hunion : A ∪ Bs = far B S z := by
      ext x
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro hx
        by_cases h : s * x ∈ E
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    have hcardU := Set.ncard_union_eq hdisj
    rw [hunion] at hcardU
    omega
  obtain ⟨s, hs⟩ : (far B S z).Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by omega)
  have hSH : S ⊆ (p16Ext hsq E s : Set V) := by
    intro x hx
    rw [SetLike.mem_coe, p16_mem_ext_iff]
    by_cases hxz : x = z
    · left
      rw [hxz]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · by_cases hxB : B z x = 0
      · left
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ((mem_nbr_iff).2 ⟨hx, hxz, hxB⟩))
      · right
        exact hconn s hs x ((mem_far_iff).2 ⟨hx, (p16_zmod2_cases _).resolve_left hxB⟩)
  have htop : (⊤ : Subgroup V) ≤ p16Ext hsq E s := by
    rw [← hspan, Subgroup.closure_le]
    exact hSH
  have h1 : Nat.card V ≤ Nat.card (p16Ext hsq E s) := by
    rw [← Subgroup.card_top]
    exact Subgroup.card_le_of_le htop
  have h2 := p16_natCard_ext_le hsq E s
  calc Nat.card V ≤ Nat.card (p16Ext hsq E s) := h1
    _ ≤ 2 * Nat.card E := h2
    _ ≤ 2 * 2 ^ (a + 1) := Nat.mul_le_mul_left 2 hEcard
    _ = 2 ^ (a + 2) := by ring

end PointSet

@[expose] def lineW (z t : V) : Set V := {z, t, z * t}

@[expose] def lineThrough (q y : V) : Set V := {q, y, q * y}

@[expose] def sigma (B : V → V → ZMod 2) (S : Set V) (e : V) : Set V := {y | y ∈ S ∧ B e y = 0}

structure GridData (B : V → V → ZMod 2) (S : Set V) (z t e : V) (x : V → V) : Prop where
  z_mem : z ∈ S
  t_mem : t ∈ S
  z_ne_t : z ≠ t
  orth_zt : B z t = 0
  e_ne_one : e ≠ 1
  x_mem : ∀ q ∈ lineW z t, x q ∈ S
  x_orth : ∀ q ∈ lineW z t, B q (x q) = 0
  x_notMem : ∀ q ∈ lineW z t, x q ∉ lineW z t
  sigma_eq : ∀ y ∈ S, B e y = 0 ↔ y ∈ lineW z t ∨ ∃ q ∈ lineW z t, y ∈ lineThrough q (x q)
  leg_far : ∀ q ∈ lineW z t, ∀ y ∈ lineThrough q (x q), y ≠ q → ∀ q' ∈ lineW z t, q' ≠ q →
    B y q' = 1

namespace GridData

variable {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z t e : V} {x : V → V}

@[expose] def legPts (x : V → V) (q : V) : Set V := {x q, q * x q}

private theorem mem_W_iff {q : V} : q ∈ lineW z t ↔ q = z ∨ q = t ∨ q = z * t := by
  simp [lineW]

private theorem mem_lineThrough_iff {q y : V} :
    y ∈ lineThrough q (x q) ↔ y = q ∨ y = x q ∨ y = q * x q := by
  simp [lineThrough]

private theorem mem_legPts_iff {q y : V} : y ∈ legPts x q ↔ y = x q ∨ y = q * x q := by
  simp [legPts]

private theorem p16_finite_legPts (x : V → V) (q : V) : (legPts x q).Finite :=
  (Set.finite_singleton _).insert _

private theorem p16_finite_W : (lineW z t).Finite := by
  unfold lineW
  exact ((Set.finite_singleton _).insert _).insert _

private theorem p16_zt_mem (hS : PointSet B S a) (hG : GridData B S z t e x) : z * t ∈ S :=
  hS.mul_mem_of_orth z hG.z_mem t hG.t_mem hG.z_ne_t hG.orth_zt

private theorem p16_W_mem (hS : PointSet B S a) (hG : GridData B S z t e x) {q : V}
    (hq : q ∈ lineW z t) : q ∈ S := by
  rcases mem_W_iff.1 hq with rfl | rfl | rfl
  · exact hG.z_mem
  · exact hG.t_mem
  · exact p16_zt_mem hS hG

private theorem p16_W_ne_one (hS : PointSet B S a) (hG : GridData B S z t e x) {q : V}
    (hq : q ∈ lineW z t) : q ≠ 1 :=
  fun h => hS.one_notMem (by rw [← h]; exact p16_W_mem hS hG hq)

private theorem p16_W_orth (hB : SympForm B) (hG : GridData B S z t e x) {q q' : V}
    (hq : q ∈ lineW z t) (hq' : q' ∈ lineW z t) : B q q' = 0 := by
  have hzt : B z (z * t) = 0 := by rw [hB.mul_right, hB.alt, hG.orth_zt, zero_add]
  have htz : B t (z * t) = 0 := by rw [hB.mul_right, hB.alt, add_zero, hB.symm, hG.orth_zt]
  have hztz : B (z * t) z = 0 := by rw [hB.mul_left, hB.alt, zero_add, hB.symm, hG.orth_zt]
  have hztt : B (z * t) t = 0 := by rw [hB.mul_left, hG.orth_zt, hB.alt, zero_add]
  rcases mem_W_iff.1 hq with rfl | rfl | rfl <;> rcases mem_W_iff.1 hq' with rfl | rfl | rfl
  · exact hB.alt _
  · exact hG.orth_zt
  · exact hzt
  · exact (hB.symm _ _).trans hG.orth_zt
  · exact hB.alt _
  · exact htz
  · exact hztz
  · exact hztt
  · exact hB.alt _

private theorem p16_leg_orth (hB : SympForm B) (hG : GridData B S z t e x) {q y : V}
    (hq : q ∈ lineW z t) (hy : y ∈ lineThrough q (x q)) (hyq : y ≠ q) : B y q = 0 := by
  rcases mem_lineThrough_iff.1 hy with h | h | h
  · exact absurd h hyq
  · rw [h, hB.symm]
    exact hG.x_orth q hq
  · rw [h, hB.mul_left, hB.alt, zero_add, hB.symm]
    exact hG.x_orth q hq

private theorem p16_leg_mem (hS : PointSet B S a) (hG : GridData B S z t e x) {q : V}
    (hq : q ∈ lineW z t) : x q ∈ S ∧ q * x q ∈ S := by
  have hxq : x q ≠ q := fun h => hG.x_notMem q hq (by rw [h]; exact hq)
  exact ⟨hG.x_mem q hq, hS.mul_mem_of_orth q (p16_W_mem hS hG hq) (x q) (hG.x_mem q hq)
    (Ne.symm hxq) (hG.x_orth q hq)⟩

private theorem p16_legPts_S (hS : PointSet B S a) (hG : GridData B S z t e x) {q u : V}
    (hq : q ∈ lineW z t) (hu : u ∈ legPts x q) : u ∈ S := by
  rcases mem_legPts_iff.1 hu with rfl | rfl
  · exact hG.x_mem q hq
  · exact (p16_leg_mem hS hG hq).2

private theorem p16_legPts_ne (hS : PointSet B S a) (hG : GridData B S z t e x) {q w : V}
    (hq : q ∈ lineW z t) (hw : w ∈ legPts x q) : w ≠ q := by
  rcases mem_legPts_iff.1 hw with rfl | rfl
  · exact fun h => hG.x_notMem _ hq (by rw [h]; exact hq)
  · intro h
    have h1 : x q = 1 := mul_eq_left.1 h
    exact hS.one_notMem (by rw [← h1]; exact hG.x_mem q hq)

private theorem p16_partner_ne (hS : PointSet B S a) (hG : GridData B S z t e x) {q w : V}
    (hq : q ∈ lineW z t) (hw : w ∈ legPts x q) : q * w ≠ w := by
  rcases mem_legPts_iff.1 hw with rfl | rfl
  · exact fun h => p16_W_ne_one hS hG hq (mul_eq_right.1 h)
  · intro h
    have h1 : q = 1 := mul_eq_right.1 h
    exact p16_W_ne_one hS hG hq h1

private theorem p16_partner_mem {q w : V} (hB : SympForm B) (hw : w ∈ legPts x q) :
    q * w ∈ legPts x q := by
  rcases mem_legPts_iff.1 hw with rfl | rfl
  · exact mem_legPts_iff.2 (Or.inr rfl)
  · rw [← mul_assoc, hB.sq_eq_one q, one_mul]
    exact mem_legPts_iff.2 (Or.inl rfl)

private theorem p16_partner_unique {q u w : V} (hB : SympForm B) (hu : u ∈ legPts x q)
    (hw : w ∈ legPts x q) (huw : u ≠ w) : u = q * w := by
  rcases mem_legPts_iff.1 hu with h1 | h1 <;> rcases mem_legPts_iff.1 hw with h2 | h2
  · exact absurd (h1.trans h2.symm) huw
  · rw [h1, h2, ← mul_assoc, hB.sq_eq_one q, one_mul]
  · rw [h1, h2]
  · exact absurd (h1.trans h2.symm) huw

private theorem p16_leg_not_W (hB : SympForm B) (hG : GridData B S z t e x) {q y : V}
    (hq : q ∈ lineW z t) (hy : y ∈ lineThrough q (x q)) (hyq : y ≠ q) : y ∉ lineW z t := by
  intro hyW
  have h := hG.leg_far q hq y hy hyq y hyW hyq
  rw [hB.alt] at h
  exact absurd h (by decide)

private theorem p16_leg_disj (hB : SympForm B) (hG : GridData B S z t e x) {q q' y v : V}
    (hq : q ∈ lineW z t) (hq' : q' ∈ lineW z t) (hqq : q' ≠ q)
    (hy : y ∈ lineThrough q (x q)) (hyq : y ≠ q) (hv : v ∈ lineThrough q' (x q'))
    (hvq : v ≠ q') : y ≠ v := by
  intro h
  have h1 := hG.leg_far q hq y hy hyq q' hq' hqq
  have h2 := p16_leg_orth hB hG hq' hv hvq
  rw [← h, h1] at h2
  exact absurd h2 (by decide)

private theorem p16_mem_sigma_iff (hS : PointSet B S a) (hG : GridData B S z t e x) {y : V} :
    y ∈ sigma B S e ↔ y ∈ lineW z t ∨ ∃ q ∈ lineW z t, y ∈ lineThrough q (x q) := by
  constructor
  · rintro ⟨hyS, hye⟩
    exact (hG.sigma_eq y hyS).1 hye
  · intro h
    have hyS : y ∈ S := by
      rcases h with h | ⟨q, hq, h⟩
      · exact p16_W_mem hS hG h
      · rcases mem_lineThrough_iff.1 h with h' | h' | h'
        · rw [h']
          exact p16_W_mem hS hG hq
        · rw [h']
          exact (p16_leg_mem hS hG hq).1
        · rw [h']
          exact (p16_leg_mem hS hG hq).2
    exact ⟨hyS, (hG.sigma_eq y hyS).2 h⟩

private theorem p16_L_split {q y : V} (hq : q ∈ lineW z t) (hy : y ∈ lineThrough q (x q)) :
    y ∈ lineW z t ∨ y ∈ legPts x q := by
  rcases mem_lineThrough_iff.1 hy with h | h | h
  · exact Or.inl (by rw [h]; exact hq)
  · exact Or.inr (mem_legPts_iff.2 (Or.inl h))
  · exact Or.inr (mem_legPts_iff.2 (Or.inr h))

private theorem p16_legPts_sub {q y : V} (hy : y ∈ legPts x q) : y ∈ lineThrough q (x q) := by
  rcases mem_legPts_iff.1 hy with h | h
  · rw [mem_lineThrough_iff]
    exact Or.inr (Or.inl h)
  · rw [mem_lineThrough_iff]
    exact Or.inr (Or.inr h)

private theorem p16_sigma_legPts_iff (hS : PointSet B S a) (hG : GridData B S z t e x) {y : V} :
    y ∈ sigma B S e ↔ y ∈ lineW z t ∨ y ∈ legPts x z ∨ y ∈ legPts x t ∨ y ∈ legPts x (z * t) := by
  rw [p16_mem_sigma_iff hS hG]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · exact Or.inl h
    · rcases p16_L_split hq h with h' | h'
      · exact Or.inl h'
      · rcases mem_W_iff.1 hq with rfl | rfl | rfl
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨z, mem_W_iff.2 (Or.inl rfl), p16_legPts_sub h⟩
    · exact Or.inr ⟨t, mem_W_iff.2 (Or.inr (Or.inl rfl)), p16_legPts_sub h⟩
    · exact Or.inr ⟨z * t, mem_W_iff.2 (Or.inr (Or.inr rfl)), p16_legPts_sub h⟩

private theorem p16_W_ncard (hS : PointSet B S a) (hG : GridData B S z t e x) :
    (lineW z t).ncard = 3 := by
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.z_mem)
  have ht1 : t ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.t_mem)
  have hzne : z ∉ ({t, z * t} : Set V) := by
    rintro (h | h)
    · exact hG.z_ne_t h
    · exact ht1 (mul_eq_left.1 h.symm)
  have htne : t ≠ z * t := fun h => hz1 (mul_eq_right.1 h.symm)
  unfold lineW
  rw [Set.ncard_insert_of_notMem hzne ((Set.finite_singleton _).insert _), Set.ncard_pair htne]

private theorem p16_legPts_ncard (hS : PointSet B S a) (hG : GridData B S z t e x) {q : V}
    (hq : q ∈ lineW z t) : (legPts x q).ncard = 2 := by
  unfold legPts
  exact Set.ncard_pair (Ne.symm (p16_partner_ne hS hG hq (mem_legPts_iff.2 (Or.inl rfl))))

private theorem p16_disj_W_legPts (hS : PointSet B S a) (hB : SympForm B)
    (hG : GridData B S z t e x) {q : V} (hq : q ∈ lineW z t) :
    Disjoint (lineW z t) (legPts x q) := by
  rw [Set.disjoint_left]
  intro w hwW hwL
  exact p16_leg_not_W hB hG hq (p16_legPts_sub hwL) (p16_legPts_ne hS hG hq hwL) hwW

private theorem p16_disj_legPts (hS : PointSet B S a) (hB : SympForm B)
    (hG : GridData B S z t e x) {q q' : V} (hq : q ∈ lineW z t) (hq' : q' ∈ lineW z t)
    (hqq : q' ≠ q) : Disjoint (legPts x q) (legPts x q') := by
  rw [Set.disjoint_left]
  intro w hw hw'
  exact p16_leg_disj hB hG hq hq' hqq (p16_legPts_sub hw) (p16_legPts_ne hS hG hq hw)
    (p16_legPts_sub hw') (p16_legPts_ne hS hG hq' hw') rfl

private theorem p16_nbr_W (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x)
    {q : V} (hq : q ∈ lineW z t) :
    nbr B S q ∩ sigma B S e = (lineW z t \ {q}) ∪ legPts x q := by
  ext u
  constructor
  · rintro ⟨⟨huS, huq, hqu⟩, huSig⟩
    rcases (p16_mem_sigma_iff hS hG).1 huSig with huW | ⟨r, hr, hur⟩
    · exact Or.inl ⟨huW, fun h => huq (Set.mem_singleton_iff.1 h)⟩
    · by_cases hur' : u = r
      · exact Or.inl ⟨by rw [hur']; exact hr, fun h => huq (Set.mem_singleton_iff.1 h)⟩
      · have huP : u ∈ legPts x r := by
          rcases mem_lineThrough_iff.1 hur with h | h | h
          · exact absurd h hur'
          · exact mem_legPts_iff.2 (Or.inl h)
          · exact mem_legPts_iff.2 (Or.inr h)
        by_cases hqr : r = q
        · rw [hqr] at huP
          exact Or.inr huP
        · exfalso
          have h1 := hG.leg_far r hr u hur hur' q hq (fun h => hqr h.symm)
          have h2 : B q u = 1 := (hB.symm q u).trans h1
          rw [hqu] at h2
          exact absurd h2 (by decide)
  · rintro (⟨huW, huq⟩ | huP)
    · have huq' : u ≠ q := fun h => huq (Set.mem_singleton_iff.2 h)
      refine ⟨⟨p16_W_mem hS hG huW, huq', p16_W_orth hB hG hq huW⟩, ?_⟩
      exact (p16_sigma_legPts_iff hS hG).2 (Or.inl huW)
    · have huq' : u ≠ q := p16_legPts_ne hS hG hq huP
      refine ⟨⟨p16_legPts_S hS hG hq huP, huq', ?_⟩, ?_⟩
      · rw [hB.symm]
        exact p16_leg_orth hB hG hq (p16_legPts_sub huP) huq'
      · rw [p16_mem_sigma_iff hS hG]
        exact Or.inr ⟨q, hq, p16_legPts_sub huP⟩

private theorem p16_one_leg (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x)
    {q q' y : V} (hq : q ∈ lineW z t) (hq' : q' ∈ lineW z t) (hqq : q' ≠ q)
    (hy : y ∈ legPts x q) : (nbr B S y ∩ legPts x q').ncard = 1 := by
  have hyl := p16_legPts_sub hy
  have hyq := p16_legPts_ne hS hG hq hy
  have h1 : B y q' = 1 := hG.leg_far q hq y hyl hyq q' hq' hqq
  have hyne : ∀ w ∈ legPts x q', y ≠ w := fun w hw =>
    p16_leg_disj hB hG hq hq' hqq hyl hyq (p16_legPts_sub hw) (p16_legPts_ne hS hG hq' hw)
  have hxS := p16_leg_mem hS hG hq'
  have hBq : B y (q' * x q') = 1 + B y (x q') := by rw [hB.mul_right, h1]
  rcases p16_zmod2_cases (B y (x q')) with hc | hc
  · apply Set.ncard_eq_one.2
    refine ⟨x q', ?_⟩
    ext w
    constructor
    · rintro ⟨hwn, hwP⟩
      rcases mem_legPts_iff.1 hwP with h | h
      · exact Set.mem_singleton_iff.2 h
      · exfalso
        have h0 : B y w = 0 := hwn.2.2
        have h3 : B y w = 1 := by
          rw [h, hBq, hc, add_zero]
        rw [h3] at h0
        exact absurd h0 (by decide)
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      refine ⟨⟨hxS.1, fun h => hyne (x q') (mem_legPts_iff.2 (Or.inl rfl)) h.symm, hc⟩, ?_⟩
      exact mem_legPts_iff.2 (Or.inl rfl)
  · apply Set.ncard_eq_one.2
    refine ⟨q' * x q', ?_⟩
    ext w
    constructor
    · rintro ⟨hwn, hwP⟩
      rcases mem_legPts_iff.1 hwP with h | h
      · exfalso
        have h0 : B y w = 0 := hwn.2.2
        have h3 : B y w = 1 := by
          rw [h, hc]
        rw [h3] at h0
        exact absurd h0 (by decide)
      · exact Set.mem_singleton_iff.2 h
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      refine ⟨⟨(p16_leg_mem hS hG hq').2,
        fun h => hyne (q' * x q') (mem_legPts_iff.2 (Or.inr rfl)) h.symm, ?_⟩, ?_⟩
      · rw [hB.mul_right, h1, hc]
        decide
      · exact mem_legPts_iff.2 (Or.inr rfl)

private theorem p16_nbr_leg (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x)
    {q q' q'' y : V} (hq : q ∈ lineW z t) (hq' : q' ∈ lineW z t) (hq'' : q'' ∈ lineW z t)
    (h1 : q' ≠ q) (h2 : q'' ≠ q) (h3 : q'' ≠ q')
    (hW : ∀ r ∈ lineW z t, r = q ∨ r = q' ∨ r = q'') (hy : y ∈ legPts x q) :
    (nbr B S y ∩ sigma B S e).ncard = 4 := by
  have hyl := p16_legPts_sub hy
  have hyq := p16_legPts_ne hS hG hq hy
  have hyS := p16_legPts_S hS hG hq hy
  have hy1 : y ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hyS)
  have hqy : q * y ∈ legPts x q := p16_partner_mem hB hy
  have hqyne : q * y ≠ y := p16_partner_ne hS hG hq hy
  have hqne : q ≠ q * y := fun h => hy1 (mul_eq_left.1 h.symm)
  have hset : nbr B S y ∩ sigma B S e =
      (({q, q * y} : Set V) ∪ (nbr B S y ∩ legPts x q')) ∪ (nbr B S y ∩ legPts x q'') := by
    ext u
    constructor
    · rintro ⟨⟨huS, huy, hyu⟩, huSig⟩
      have hcase : u ∈ lineW z t ∨ ∃ r ∈ lineW z t, u ∈ legPts x r := by
        rcases (p16_mem_sigma_iff hS hG).1 huSig with huW | ⟨r, hr, hur⟩
        · exact Or.inl huW
        · by_cases hur' : u = r
          · exact Or.inl (by rw [hur']; exact hr)
          · refine Or.inr ⟨r, hr, ?_⟩
            rcases mem_lineThrough_iff.1 hur with h | h | h
            · exact absurd h hur'
            · exact mem_legPts_iff.2 (Or.inl h)
            · exact mem_legPts_iff.2 (Or.inr h)
      rcases hcase with huW | ⟨r, hr, hur⟩
      · rcases hW u huW with h | h | h
        · exact Or.inl (Or.inl (by rw [h]; exact Set.mem_insert _ _))
        · exfalso
          have h4 : B y q' = 1 := hG.leg_far q hq y hyl hyq q' hq' h1
          have h5 : B y u = 1 := by rw [h]; exact h4
          rw [h5] at hyu
          exact absurd hyu (by decide)
        · exfalso
          have h4 : B y q'' = 1 := hG.leg_far q hq y hyl hyq q'' hq'' h2
          have h5 : B y u = 1 := by rw [h]; exact h4
          rw [h5] at hyu
          exact absurd hyu (by decide)
      · rcases hW r hr with h | h | h
        · have hu' : u = q * y := by
            rw [h] at hur
            exact p16_partner_unique hB hur hy huy
          exact Or.inl (Or.inl (by rw [hu']; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        · rw [h] at hur
          exact Or.inl (Or.inr ⟨⟨huS, huy, hyu⟩, hur⟩)
        · rw [h] at hur
          exact Or.inr ⟨⟨huS, huy, hyu⟩, hur⟩
    · rintro (((h | h) | ⟨hu1, hu2⟩) | ⟨hu1, hu2⟩)
      · rw [h]
        exact ⟨⟨p16_W_mem hS hG hq, fun h' => hyq h'.symm, p16_leg_orth hB hG hq hyl hyq⟩,
          (p16_mem_sigma_iff hS hG).2 (Or.inl hq)⟩
      · rw [h]
        refine ⟨⟨p16_legPts_S hS hG hq hqy, hqyne, ?_⟩,
          (p16_mem_sigma_iff hS hG).2 (Or.inr ⟨q, hq, p16_legPts_sub hqy⟩)⟩
        rw [hB.mul_right, hB.alt, add_zero]
        exact p16_leg_orth hB hG hq hyl hyq
      · exact ⟨hu1, (p16_mem_sigma_iff hS hG).2 (Or.inr ⟨q', hq', p16_legPts_sub hu2⟩)⟩
      · exact ⟨hu1, (p16_mem_sigma_iff hS hG).2 (Or.inr ⟨q'', hq'', p16_legPts_sub hu2⟩)⟩
  have hT0 : ({q, q * y} : Set V).ncard = 2 := Set.ncard_pair hqne
  have hD1 : Disjoint ({q, q * y} : Set V) (nbr B S y ∩ legPts x q') := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    rcases hu1 with h | h
    · have huW : u ∈ lineW z t := by rw [h]; exact hq
      exact Set.disjoint_left.1 (p16_disj_W_legPts hS hB hG hq') huW hu2.2
    · have huL : u ∈ legPts x q := by rw [h]; exact hqy
      exact Set.disjoint_left.1 (p16_disj_legPts hS hB hG hq hq' h1) huL hu2.2
  have hD2 : Disjoint ({q, q * y} : Set V) (nbr B S y ∩ legPts x q'') := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    rcases hu1 with h | h
    · have huW : u ∈ lineW z t := by rw [h]; exact hq
      exact Set.disjoint_left.1 (p16_disj_W_legPts hS hB hG hq'') huW hu2.2
    · have huL : u ∈ legPts x q := by rw [h]; exact hqy
      exact Set.disjoint_left.1 (p16_disj_legPts hS hB hG hq hq'' h2) huL hu2.2
  have hD3 : Disjoint (nbr B S y ∩ legPts x q') (nbr B S y ∩ legPts x q'') := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    exact Set.disjoint_left.1 (p16_disj_legPts hS hB hG hq' hq'' h3) hu1.2 hu2.2
  have fin_pair : ({q, q * y} : Set V).Finite := (Set.finite_singleton _).insert _
  have fin_q' : (nbr B S y ∩ legPts x q').Finite :=
    (p16_finite_legPts x q').subset Set.inter_subset_right
  have fin_q'' : (nbr B S y ∩ legPts x q'').Finite :=
    (p16_finite_legPts x q'').subset Set.inter_subset_right
  rw [hset, Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hD2, hD3⟩)
    (fin_pair.union fin_q') fin_q'', Set.ncard_union_eq hD1 fin_pair fin_q', hT0,
    p16_one_leg hB hS hG hq hq' h1 hy, p16_one_leg hB hS hG hq hq'' h2 hy]

theorem card_sigma (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x) :
    (sigma B S e).ncard = 9 := by
  have hz : z ∈ lineW z t := mem_W_iff.2 (Or.inl rfl)
  have ht : t ∈ lineW z t := mem_W_iff.2 (Or.inr (Or.inl rfl))
  have hzt : z * t ∈ lineW z t := mem_W_iff.2 (Or.inr (Or.inr rfl))
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.z_mem)
  have ht1 : t ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.t_mem)
  have hzt_z : z * t ≠ z := fun h => ht1 (mul_eq_left.1 h)
  have hzt_t : z * t ≠ t := fun h => hz1 (mul_eq_right.1 h)
  have e1 : sigma B S e = lineW z t ∪ legPts x z ∪ legPts x t ∪ legPts x (z * t) := by
    ext y
    rw [p16_sigma_legPts_iff hS hG]
    simp only [Set.mem_union]
    tauto
  have dWz := p16_disj_W_legPts hS hB hG hz
  have dWt := p16_disj_W_legPts hS hB hG ht
  have dWzt := p16_disj_W_legPts hS hB hG hzt
  have dzt := p16_disj_legPts hS hB hG hz hzt hzt_z
  have dtzt := p16_disj_legPts hS hB hG ht hzt hzt_t
  have dzt' := p16_disj_legPts hS hB hG hz ht hG.z_ne_t.symm
  have d1 : Disjoint (lineW z t ∪ legPts x z ∪ legPts x t) (legPts x (z * t)) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨dWzt, dzt⟩, dtzt⟩
  have d2 : Disjoint (lineW z t ∪ legPts x z) (legPts x t) :=
    Set.disjoint_union_left.2 ⟨dWt, dzt'⟩
  have finW := p16_finite_W (z := z) (t := t)
  have finPz := p16_finite_legPts x z
  have finPt := p16_finite_legPts x t
  have finPzt := p16_finite_legPts x (z * t)
  rw [e1, Set.ncard_union_eq d1 ((finW.union finPz).union finPt) finPzt,
    Set.ncard_union_eq d2 (finW.union finPz) finPt, Set.ncard_union_eq dWz finW finPz,
    p16_W_ncard hS hG, p16_legPts_ncard hS hG hz, p16_legPts_ncard hS hG ht,
    p16_legPts_ncard hS hG hzt]

theorem card_nbr_inter_sigma (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x)
    {y : V} (hy : y ∈ sigma B S e) : (nbr B S y ∩ sigma B S e).ncard = 4 := by
  have hz : z ∈ lineW z t := mem_W_iff.2 (Or.inl rfl)
  have ht : t ∈ lineW z t := mem_W_iff.2 (Or.inr (Or.inl rfl))
  have hzt : z * t ∈ lineW z t := mem_W_iff.2 (Or.inr (Or.inr rfl))
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.z_mem)
  have ht1 : t ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.t_mem)
  have hzt_z : z * t ≠ z := fun h => ht1 (mul_eq_left.1 h)
  have hzt_t : z * t ≠ t := fun h => hz1 (mul_eq_right.1 h)
  have hWall : ∀ r ∈ lineW z t, r = z ∨ r = t ∨ r = z * t := fun r hr => mem_W_iff.1 hr
  rcases (p16_sigma_legPts_iff hS hG).1 hy with hW | hPz | hPt | hPzt
  · have hdisj : Disjoint (lineW z t \ {y}) (legPts x y) :=
      Set.disjoint_of_subset_left Set.diff_subset (p16_disj_W_legPts hS hB hG hW)
    rw [p16_nbr_W hB hS hG hW, Set.ncard_union_eq hdisj (p16_finite_W.subset Set.diff_subset)
      (p16_finite_legPts x y), Set.ncard_diff_singleton_of_mem hW,
      p16_W_ncard hS hG, p16_legPts_ncard hS hG hW]
  · exact p16_nbr_leg hB hS hG hz ht hzt hG.z_ne_t.symm hzt_z hzt_t hWall hPz
  · exact p16_nbr_leg hB hS hG ht hz hzt hG.z_ne_t hzt_t hzt_z
      (fun r hr => by rcases hWall r hr with h | h | h <;> simp [h]) hPt
  · exact p16_nbr_leg hB hS hG hzt hz ht (Ne.symm hzt_z) (Ne.symm (hzt_t)) hG.z_ne_t.symm
      (fun r hr => by rcases hWall r hr with h | h | h <;> simp [h]) hPzt

theorem edge_count [Finite V] (hB : SympForm B) (hS : PointSet B S a)
    (hG : GridData B S z t e x) : (S.ncard - 9) * a + 36 = 18 * a ∧ 9 ≤ S.ncard ∧ 2 ≤ a := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hz : z ∈ S := hG.z_mem
  have hSgc : (sigma B S e).ncard = 9 := card_sigma hB hS hG
  have hSgS : sigma B S e ⊆ S := fun y hy => hy.1
  have h9 : 9 ≤ S.ncard := by
    rw [← hSgc]
    exact Set.ncard_le_ncard hSgS
  have h4 := card_nbr_inter_sigma hB hS hG (y := z)
    ((p16_mem_sigma_iff hS hG).2 (Or.inl (mem_W_iff.2 (Or.inl rfl))))
  have hle4 := Set.ncard_le_ncard (Set.inter_subset_left (s := nbr B S z) (t := sigma B S e))
  have hn := hS.card_nbr z hz
  have ha2 : 2 ≤ a := by omega
  set Out : Set V := S \ sigma B S e with hOut
  have hOutc : Out.ncard = S.ncard - 9 := by
    rw [hOut, Set.ncard_sdiff hSgS, hSgc]
  set Sf : Finset V := Finset.univ.filter (fun y => y ∈ sigma B S e) with hSf
  set Of : Finset V := Finset.univ.filter (fun w => w ∈ Out) with hOf
  have hSfc : Sf.card = 9 := by
    have h := p16_ncard_eq (fun y => y ∈ sigma B S e)
    rw [hSf, ← h]
    exact hSgc
  have hOfc : Of.card = S.ncard - 9 := by
    have h := p16_ncard_eq (fun w => w ∈ Out)
    rw [hOf, ← h, ← hOutc]
    rfl
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Sf) (t := Of) (r := fun y w => B y w = 0)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  have hRHS : ∀ w ∈ Of, (Sf.filter (fun y => B y w = 0)).card = a := by
    intro w hw
    have hwO : w ∈ Out := (Finset.mem_filter.1 hw).2
    have hwS : w ∈ S := hwO.1
    have hwSg : w ∉ sigma B S e := hwO.2
    have hBew : B w e = 1 := by
      rcases p16_zmod2_cases (B e w) with h | h
      · exact absurd ⟨hwS, h⟩ hwSg
      · rw [hB.symm]
        exact h
    have hcnt := PointSet.p16_card_nbr_pair hB hS hwS hBew
    rw [← hcnt, p16_ncard_eq (fun j => j ∈ nbr B S w ∧ B j e = 0)]
    congr 1
    ext y
    simp only [hSf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hySg, hyw⟩
      have hyw' : y ≠ w := fun h => hwSg (h ▸ hySg)
      exact ⟨(PointSet.mem_nbr_iff).2 ⟨hySg.1, hyw', (hB.symm w y).trans hyw⟩,
        (hB.symm y e).trans hySg.2⟩
    · rintro ⟨hyn, hye⟩
      exact ⟨⟨(PointSet.mem_nbr_iff).1 hyn |>.1, (hB.symm e y).trans hye⟩,
        ((hB.symm y w).trans ((PointSet.mem_nbr_iff).1 hyn).2.2)⟩
  have hLHS : ∀ y ∈ Sf, (Of.filter (fun w => B y w = 0)).card = 2 * a - 4 := by
    intro y hy
    have hySg : y ∈ sigma B S e := (Finset.mem_filter.1 hy).2
    have hyS : y ∈ S := hySg.1
    have hyn := hS.card_nbr y hyS
    have hI := card_nbr_inter_sigma hB hS hG hySg
    have hD := Set.ncard_inter_add_ncard_diff_eq_ncard (nbr B S y) (sigma B S e)
    have hset : (Of.filter (fun w => B y w = 0)).card =
        (nbr B S y \ sigma B S e).ncard := by
      have h := p16_ncard_eq (fun w => w ∈ nbr B S y ∧ w ∉ sigma B S e)
      have hdiff : (nbr B S y \ sigma B S e) = {w | w ∈ nbr B S y ∧ w ∉ sigma B S e} := rfl
      rw [hdiff, h]
      congr 1
      ext w
      simp only [hOf, hOut, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_diff,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hwS, hwSg⟩, hyw⟩
        have hwy : w ≠ y := fun h => hwSg (h ▸ hySg)
        exact ⟨(PointSet.mem_nbr_iff).2 ⟨hwS, hwy, hyw⟩, hwSg⟩
      · rintro ⟨hwn, hwSg⟩
        exact ⟨⟨((PointSet.mem_nbr_iff).1 hwn).1, hwSg⟩, ((PointSet.mem_nbr_iff).1 hwn).2.2⟩
    rw [hset]
    omega
  have hsum := hdc
  rw [Finset.sum_congr rfl hLHS, Finset.sum_const, Finset.sum_congr rfl hRHS,
    Finset.sum_const, hSfc, smul_eq_mul, smul_eq_mul, hOfc] at hsum
  refine ⟨?_, h9, ha2⟩
  generalize hP : (S.ncard - 9) * a = P at hsum ⊢
  omega

theorem zero_nbr_card (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x) :
    {j | j ∈ nbr B S z ∧ B e j = 0}.ncard = 4 ∧
      ∀ j ∈ nbr B S z, ∀ y ∈ nbr B S z, B e j = 0 → B e y = 0 → y ≠ j → y ≠ z * j →
        B j y = 1 := by
  have hz : z ∈ lineW z t := mem_W_iff.2 (Or.inl rfl)
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.z_mem)
  have ht1 : t ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hG.t_mem)
  have hzz : ∀ w : V, z * (z * w) = w := fun w => by
    rw [← mul_assoc, hB.sq_eq_one z, one_mul]
  have hset : {j | j ∈ nbr B S z ∧ B e j = 0} = nbr B S z ∩ sigma B S e := by
    ext j
    constructor
    · rintro ⟨hjn, hje⟩
      exact ⟨hjn, ((PointSet.mem_nbr_iff).1 hjn).1, hje⟩
    · rintro ⟨hjn, -, hje⟩
      exact ⟨hjn, hje⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact card_nbr_inter_sigma hB hS hG ((p16_mem_sigma_iff hS hG).2 (Or.inl hz))
  · intro j hj y hy hej hey hyj hyzj
    have hjSig : j ∈ nbr B S z ∩ sigma B S e := ⟨hj, ((PointSet.mem_nbr_iff).1 hj).1, hej⟩
    have hySig : y ∈ nbr B S z ∩ sigma B S e := ⟨hy, ((PointSet.mem_nbr_iff).1 hy).1, hey⟩
    rw [p16_nbr_W hB hS hG hz] at hjSig hySig
    rcases hjSig with ⟨hjW, hjz⟩ | hjP <;> rcases hySig with ⟨hyW, hyz⟩ | hyP
    · have hjz' : j ≠ z := fun h => hjz (Set.mem_singleton_iff.2 h)
      have hyz' : y ≠ z := fun h => hyz (Set.mem_singleton_iff.2 h)
      have hj' : j = t ∨ j = z * t := by
        rcases mem_W_iff.1 hjW with h | h | h
        · exact absurd h hjz'
        · exact Or.inl h
        · exact Or.inr h
      have hy' : y = t ∨ y = z * t := by
        rcases mem_W_iff.1 hyW with h | h | h
        · exact absurd h hyz'
        · exact Or.inl h
        · exact Or.inr h
      exfalso
      rcases hj' with h | h <;> rcases hy' with h' | h'
      · exact hyj (h'.trans h.symm)
      · exact hyzj (h'.trans (by rw [h]))
      · exact hyzj (h'.trans (by rw [h, hzz]))
      · exact hyj (h'.trans h.symm)
    · have hyL := p16_legPts_sub hyP
      have hyz' : y ≠ z := p16_legPts_ne hS hG hz hyP
      have hjz' : j ≠ z := fun h => hjz (Set.mem_singleton_iff.2 h)
      have h1 : B y j = 1 := hG.leg_far z hz y hyL hyz' j hjW hjz'
      exact (hB.symm j y).trans h1
    · have hjL := p16_legPts_sub hjP
      have hjz' : j ≠ z := p16_legPts_ne hS hG hz hjP
      have hyz' : y ≠ z := fun h => hyz (Set.mem_singleton_iff.2 h)
      exact hG.leg_far z hz j hjL hjz' y hyW hyz'
    · exfalso
      rcases mem_legPts_iff.1 hjP with h | h <;> rcases mem_legPts_iff.1 hyP with h' | h'
      · exact hyj (h'.trans h.symm)
      · exact hyzj (h'.trans (by rw [h]))
      · exact hyzj (h'.trans (by rw [h, hzz]))
      · exact hyj (h'.trans h.symm)

theorem exactly_one_zero (hB : SympForm B) (hS : PointSet B S a) (hG : GridData B S z t e x)
    {j y : V} (hj : j ∈ nbr B S z) (hy : y ∈ nbr B S z) (hjy : B j y = 0) (hne : y ≠ j)
    (hne' : y ≠ z * j) :
    (B e j = 0 ∧ B e y ≠ 0 ∧ B e (j * y) ≠ 0) ∨ (B e j ≠ 0 ∧ B e y = 0 ∧ B e (j * y) ≠ 0) ∨
      (B e j ≠ 0 ∧ B e y ≠ 0 ∧ B e (j * y) = 0) := by
  obtain ⟨-, h2⟩ := zero_nbr_card hB hS hG
  have hBej : B e (j * y) = B e j + B e y := hB.mul_right e j y
  rcases p16_zmod2_cases (B e j) with hj0 | hj1 <;> rcases p16_zmod2_cases (B e y) with hy0 | hy1
  · exfalso
    have h3 := h2 j hj y hy hj0 hy0 hne hne'
    rw [hjy] at h3
    exact absurd h3 (by decide)
  · left
    refine ⟨hj0, ?_, ?_⟩
    · rw [hy1]
      decide
    · rw [hBej, hj0, hy1]
      decide
  · right
    left
    refine ⟨?_, hy0, ?_⟩
    · rw [hj1]
      decide
    · rw [hBej, hj1, hy0]
      decide
  · right
    right
    refine ⟨?_, ?_, ?_⟩
    · rw [hj1]
      decide
    · rw [hy1]
      decide
    · rw [hBej, hj1, hy1]
      decide

end GridData

private theorem p16_le_two_through (L' : Finset (Finset (Fin 6))) (A B : Fin 6) (hAB : A ≠ B)
    (hL' : ∀ l ∈ L', l.card = 3 ∧ B ∈ l ∧ A ∉ l)
    (H1 : ∀ l ∈ L', ∀ l' ∈ L', l ≠ l' → (l ∩ l').card ≤ 1) : 2 * L'.card ≤ 4 := by
  classical
  have hBU : B ∈ Finset.univ.erase A := Finset.mem_erase.2 ⟨hAB.symm, Finset.mem_univ _⟩
  have hUc : ((Finset.univ.erase A).erase B).card = 4 := by
    rw [Finset.card_erase_of_mem hBU, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ l ∈ L', l.erase B ⊆ (Finset.univ.erase A).erase B := by
    intro l hl x hx
    obtain ⟨hxB, hxl⟩ := Finset.mem_erase.1 hx
    refine Finset.mem_erase.2 ⟨hxB, Finset.mem_erase.2 ⟨fun h => (hL' l hl).2.2 (h ▸ hxl),
      Finset.mem_univ _⟩⟩
  have hcard2 : ∀ l ∈ L', (l.erase B).card = 2 := by
    intro l hl
    rw [Finset.card_erase_of_mem (hL' l hl).2.1, (hL' l hl).1]
  have hdisj : ∀ l ∈ L', ∀ l' ∈ L', l ≠ l' → Disjoint (l.erase B) (l'.erase B) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hxB, hxl⟩ := Finset.mem_erase.1 hx
    obtain ⟨-, hxl'⟩ := Finset.mem_erase.1 hx'
    have h2 : 1 < (l ∩ l').card :=
      Finset.one_lt_card.2 ⟨x, Finset.mem_inter.2 ⟨hxl, hxl'⟩, B,
        Finset.mem_inter.2 ⟨(hL' l hl).2.1, (hL' l' hl').2.1⟩, hxB⟩
    have h3 := H1 l hl l' hl' hne
    omega
  have hbi : (L'.biUnion fun l => l.erase B).card = 2 * L'.card := by
    rw [Finset.card_biUnion (fun l hl l' hl' hne => hdisj l hl l' hl' hne)]
    rw [Finset.sum_congr rfl hcard2, Finset.sum_const, smul_eq_mul]
    ring
  have hle : (L'.biUnion fun l => l.erase B).card ≤ ((Finset.univ.erase A).erase B).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨l, hl, hx⟩ := Finset.mem_biUnion.1 hx
    exact hsub l hl hx
  omega

private theorem p16_core (L : Finset (Finset (Fin 6))) (hL3 : L.card = 3)
    (hc : ∀ l ∈ L, l.card = 3)
    (H1 : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → (l ∩ l').card ≤ 1)
    (H2 : ∀ l ∈ L, ∀ p : Fin 6, p ∉ l →
      (l.filter fun q => ∃ m ∈ L, p ∈ m ∧ q ∈ m).card = 1 ∨
      (l.filter fun q => ∃ m ∈ L, p ∈ m ∧ q ∈ m).card = 3)
    (A B : Fin 6) (hAB : A ≠ B) (hnc : ¬ ∃ l ∈ L, A ∈ l ∧ B ∈ l)
    (hor : ∀ l ∈ L, A ∈ l ∨ B ∈ l)
    (hLA : (L.filter fun l => A ∈ l).card = 1) : False := by
  classical
  obtain ⟨l1, hl1⟩ := Finset.card_eq_one.1 hLA
  have hl1mem : l1 ∈ L.filter (fun l => A ∈ l) := by
    rw [hl1]
    exact Finset.mem_singleton_self _
  obtain ⟨hl1L, hA1⟩ := Finset.mem_filter.1 hl1mem
  have hB1 : B ∉ l1 := fun h => hnc ⟨l1, hl1L, hA1, h⟩
  have hother : ∀ l ∈ L, l ≠ l1 → A ∉ l ∧ B ∈ l := by
    intro l hl hne
    have hAl : A ∉ l := by
      intro hAl
      have hm : l ∈ L.filter (fun l => A ∈ l) := Finset.mem_filter.2 ⟨hl, hAl⟩
      rw [hl1, Finset.mem_singleton] at hm
      exact hne hm
    refine ⟨hAl, ?_⟩
    rcases hor l hl with h | h
    · exact absurd h hAl
    · exact h
  have hrest : (L.erase l1).card = 2 := by
    rw [Finset.card_erase_of_mem hl1L, hL3]
  obtain ⟨l2, l3, hl23, hLr⟩ := Finset.card_eq_two.1 hrest
  have hl2 : l2 ∈ L ∧ l2 ≠ l1 := by
    have : l2 ∈ L.erase l1 := by
      rw [hLr]
      exact Finset.mem_insert_self _ _
    exact ⟨(Finset.mem_erase.1 this).2, (Finset.mem_erase.1 this).1⟩
  have hl3 : l3 ∈ L ∧ l3 ≠ l1 := by
    have : l3 ∈ L.erase l1 := by
      rw [hLr]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨(Finset.mem_erase.1 this).2, (Finset.mem_erase.1 this).1⟩
  have hB2 := (hother l2 hl2.1 hl2.2).2
  have hB3 := (hother l3 hl3.1 hl3.2).2
  have hA2 := (hother l2 hl2.1 hl2.2).1
  have hA3 := (hother l3 hl3.1 hl3.2).1
  have hBU : B ∈ Finset.univ.erase A := Finset.mem_erase.2 ⟨hAB.symm, Finset.mem_univ _⟩
  have hUc : ((Finset.univ.erase A).erase B).card = 4 := by
    rw [Finset.card_erase_of_mem hBU, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsub23 : ∀ l ∈ ({l2, l3} : Finset (Finset (Fin 6))), ∀ x ∈ l.erase B,
      x ∈ (Finset.univ.erase A).erase B := by
    intro l hl x hx
    obtain ⟨hxB, hxl⟩ := Finset.mem_erase.1 hx
    have hAl : A ∉ l := by
      rw [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hA2
      · exact hA3
    refine Finset.mem_erase.2 ⟨hxB, Finset.mem_erase.2 ⟨fun h => hAl (h ▸ hxl),
      Finset.mem_univ _⟩⟩
  have hcov : ((l2.erase B) ∪ (l3.erase B)) = (Finset.univ.erase A).erase B := by
    have hdisj23 : Disjoint (l2.erase B) (l3.erase B) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨hxB, hxl⟩ := Finset.mem_erase.1 hx
      obtain ⟨-, hxl'⟩ := Finset.mem_erase.1 hx'
      have h2 : 1 < (l2 ∩ l3).card :=
        Finset.one_lt_card.2 ⟨x, Finset.mem_inter.2 ⟨hxl, hxl'⟩, B,
          Finset.mem_inter.2 ⟨hB2, hB3⟩, hxB⟩
      have h3 := H1 l2 hl2.1 l3 hl3.1 hl23
      omega
    have hcard : ((l2.erase B) ∪ (l3.erase B)).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj23, Finset.card_erase_of_mem hB2,
        Finset.card_erase_of_mem hB3, hc l2 hl2.1, hc l3 hl3.1]
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hsub23 l2 (Finset.mem_insert_self _ _) x hx
      · exact hsub23 l3 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) x hx
    · rw [hcard, hUc]
  have hF : (l1.filter fun q => ∃ m ∈ L, B ∈ m ∧ q ∈ m) = l1.erase A := by
    ext q
    constructor
    · intro hq
      obtain ⟨hql1, -⟩ := Finset.mem_filter.1 hq
      refine Finset.mem_erase.2 ⟨?_, hql1⟩
      intro hqA
      rw [hqA] at hq
      obtain ⟨-, m, hm, hBm, hAm⟩ := Finset.mem_filter.1 hq
      exact hnc ⟨m, hm, hAm, hBm⟩
    · intro hq
      obtain ⟨hqA, hql1⟩ := Finset.mem_erase.1 hq
      refine Finset.mem_filter.2 ⟨hql1, ?_⟩
      have hqU : q ∈ (Finset.univ.erase A).erase B := by
        refine Finset.mem_erase.2 ⟨fun h => hB1 (h ▸ hql1), Finset.mem_erase.2 ⟨hqA,
          Finset.mem_univ _⟩⟩
      rw [← hcov] at hqU
      rcases Finset.mem_union.1 hqU with h | h
      · exact ⟨l2, hl2.1, hB2, (Finset.mem_erase.1 h).2⟩
      · exact ⟨l3, hl3.1, hB3, (Finset.mem_erase.1 h).2⟩
  have hFc : ((l1.filter fun q => ∃ m ∈ L, B ∈ m ∧ q ∈ m)).card = 2 := by
    rw [hF, Finset.card_erase_of_mem hA1, hc l1 hl1L]
  rcases H2 l1 hl1L B hB1 with h | h <;> omega

theorem residue_six_false :
    ∀ L ∈ Finset.powersetCard 3 (Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))),
      (∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → (l ∩ l').card ≤ 1) →
      (∀ l ∈ L, ∀ p : Fin 6, p ∉ l →
        (l.filter fun q => ∃ m ∈ L, p ∈ m ∧ q ∈ m).card = 1 ∨
        (l.filter fun q => ∃ m ∈ L, p ∈ m ∧ q ∈ m).card = 3) →
      ∀ A B : Fin 6, A ≠ B → (¬ ∃ l ∈ L, A ∈ l ∧ B ∈ l) →
        (∀ l ∈ L, (l ∩ {A, B}).card = 1) → False := by
  intro L hL H1 H2 A B hAB hnc H3
  have hL3 : L.card = 3 := (Finset.mem_powersetCard.1 hL).2
  have hc : ∀ l ∈ L, l.card = 3 := fun l hl =>
    (Finset.mem_powersetCard.1 ((Finset.mem_powersetCard.1 hL).1 hl)).2
  have hor : ∀ l ∈ L, A ∈ l ∨ B ∈ l := by
    intro l hl
    by_contra hcon
    push_neg at hcon
    have h1 := H3 l hl
    rw [Finset.card_eq_one] at h1
    obtain ⟨x, hx⟩ := h1
    have hxm : x ∈ l ∩ {A, B} := by
      rw [hx]
      exact Finset.mem_singleton_self x
    rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hxm
    rcases hxm with ⟨hxl, rfl | rfl⟩
    · exact hcon.1 hxl
    · exact hcon.2 hxl
  have hsplit : (L.filter fun l => A ∈ l).card + (L.filter fun l => B ∈ l).card = 3 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := L) (fun l => A ∈ l)
    have h2 : L.filter (fun l => ¬ A ∈ l) = L.filter (fun l => B ∈ l) := by
      apply Finset.filter_congr
      intro l hl
      constructor
      · intro hnA
        exact (hor l hl).resolve_left hnA
      · intro hB' hA'
        exact hnc ⟨l, hl, hA', hB'⟩
    rw [h2, hL3] at h1
    exact h1
  have hLA2 : (L.filter fun l => A ∈ l).card ≤ 2 := by
    have := p16_le_two_through (L.filter fun l => A ∈ l) B A hAB.symm
      (fun l hl => ⟨hc l (Finset.mem_filter.1 hl).1, (Finset.mem_filter.1 hl).2,
        fun hBl => hnc ⟨l, (Finset.mem_filter.1 hl).1, (Finset.mem_filter.1 hl).2, hBl⟩⟩)
      (fun l hl l' hl' hne => H1 l (Finset.mem_filter.1 hl).1 l' (Finset.mem_filter.1 hl').1 hne)
    omega
  have hLB2 : (L.filter fun l => B ∈ l).card ≤ 2 := by
    have := p16_le_two_through (L.filter fun l => B ∈ l) A B hAB
      (fun l hl => ⟨hc l (Finset.mem_filter.1 hl).1, (Finset.mem_filter.1 hl).2,
        fun hAl => hnc ⟨l, (Finset.mem_filter.1 hl).1, hAl, (Finset.mem_filter.1 hl).2⟩⟩)
      (fun l hl l' hl' hne => H1 l (Finset.mem_filter.1 hl).1 l' (Finset.mem_filter.1 hl').1 hne)
    omega
  rcases (show (L.filter fun l => A ∈ l).card = 1 ∨ (L.filter fun l => A ∈ l).card = 2 by
    omega) with h | h
  · exact p16_core L hL3 hc H1 H2 A B hAB hnc hor h
  · apply p16_core L hL3 hc H1 H2 B A hAB.symm
      (fun ⟨l, hl, h1, h2⟩ => hnc ⟨l, hl, h2, h1⟩) (fun l hl => (hor l hl).symm)
    omega

open Classical in
private structure p16Res (B : V → V → ZMod 2) (S : Set V) (z : V) (g : V → Fin 6) : Prop where
  eq_iff : ∀ u ∈ nbr B S z, ∀ w ∈ nbr B S z,
    g u = g w ↔ ({u, z * u} : Finset V) = {w, z * w}
  surj : ∀ i : Fin 6, ∃ u ∈ nbr B S z, g u = i

open Classical in
private def p16Pl (g : V → Fin 6) (q : V × V) : Finset (Fin 6) :=
  {g q.1, g q.2, g (q.1 * q.2)}

open Classical in
private theorem p16r_mem_pl {g : V → Fin 6} {q : V × V} {x : Fin 6} (hx : x ∈ p16Pl g q) :
    ∃ v ∈ ({q.1, q.2, q.1 * q.2} : Finset V), g v = x := by
  unfold p16Pl at hx
  rcases Finset.mem_insert.1 hx with h | h
  · exact ⟨q.1, Finset.mem_insert_self _ _, h.symm⟩
  rcases Finset.mem_insert.1 h with h | h
  · exact ⟨q.2, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h.symm⟩
  · exact ⟨q.1 * q.2, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)), (Finset.mem_singleton.1 h).symm⟩

open Classical in
private theorem p16r_tri_orth {B : V → V → ZMod 2} (hB : SympForm B) {j y v v' : V}
    (hjy : B j y = 0) (hv : v ∈ ({j, y, j * y} : Finset V))
    (hv' : v' ∈ ({j, y, j * y} : Finset V)) :
    B v v' = 0 := by
  have hyj : B y j = 0 := (hB.symm y j).trans hjy
  have hjj : B j (j * y) = 0 := by rw [hB.mul_right, hB.alt, hjy, add_zero]
  have hyjy : B y (j * y) = 0 := by rw [hB.mul_right, hB.alt, add_zero, hyj]
  have hjyj : B (j * y) j = 0 := by rw [hB.mul_left, hB.alt, zero_add, hyj]
  have hjyy : B (j * y) y = 0 := by rw [hB.mul_left, hB.alt, add_zero, hjy]
  have hjjj : B (j * y) (j * y) = 0 := hB.alt _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
  rcases hv with h | h | h <;> rcases hv' with h' | h' | h' <;> rw [h, h']
  · exact hB.alt _
  · exact hjy
  · exact hjj
  · exact hyj
  · exact hB.alt _
  · exact hyjy
  · exact hjyj
  · exact hjyy
  · exact hjjj

private theorem p16r_qPair_mul_nbr [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z j y : V}
    (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (hq : (j, y) ∈ qPairs B S z) :
    j * y ∈ nbr B S z := by
  obtain ⟨hj, hy, hjy, hne, hne'⟩ := (PointSet.mem_qPairs_iff).1 hq
  have hjS : j ∈ S := ((PointSet.mem_nbr_iff).1 hj).1
  have hyS : y ∈ S := ((PointSet.mem_nbr_iff).1 hy).1
  refine (PointSet.mem_nbr_iff).2 ⟨hS.mul_mem_of_orth j hjS y hyS (Ne.symm hne) hjy, ?_, ?_⟩
  · intro h
    apply hne'
    calc y = j * (j * y) := by rw [← mul_assoc, hB.sq_eq_one j, one_mul]
      _ = j * z := by rw [h]
      _ = z * j := mul_comm j z
  · rw [hB.mul_right, ((PointSet.mem_nbr_iff).1 hj).2.2, ((PointSet.mem_nbr_iff).1 hy).2.2,
      add_zero]

open Classical in
private theorem p16r_line_mul_eq {B : V → V → ZMod 2} {z u v w v' : V} (hB : SympForm B)
    (hu : u ∈ ({v, z * v} : Finset V)) (hw : w ∈ ({v', z * v'} : Finset V)) :
    ({u * w, z * (u * w)} : Finset V) = {v * v', z * (v * v')} := by
  have key : ∀ x y : V, y = x ∨ y = z * x → ({y, z * y} : Finset V) = {x, z * x} := by
    intro x y h
    rcases h with h | h
    · rw [h]
    · rw [h]
      exact PointSet.p16_L_comm hB x
  have hu' : u = v ∨ u = z * v := by
    rcases Finset.mem_insert.1 hu with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.1 h)
  have hw' : w = v' ∨ w = z * v' := by
    rcases Finset.mem_insert.1 hw with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.1 h)
  apply key
  rcases hu' with h1 | h1 <;> rcases hw' with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1, h2]
    ac_rfl
  · right
    rw [h1, h2]
    ac_rfl
  · left
    rw [h1, h2, show z * v * (z * v') = (z * z) * (v * v') by ac_rfl, hB.sq_eq_one z, one_mul]

open Classical in
private theorem p16r_trip_nbr [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z j y v : V}
    (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (hq : (j, y) ∈ qPairs B S z)
    (hv : v ∈ ({j, y, j * y} : Finset V)) : v ∈ nbr B S z := by
  have hj := ((PointSet.mem_qPairs_iff).1 hq).1
  have hy := ((PointSet.mem_qPairs_iff).1 hq).2.1
  have hjy := p16r_qPair_mul_nbr hB hS hz hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h
  · rw [h]
    exact hj
  · rw [h]
    exact hy
  · rw [h]
    exact hjy

open Classical in
private theorem p16r_or [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {j y u w : V} (hq : (j, y) ∈ qPairs B S z) (hun : u ∈ nbr B S z) (hwn : w ∈ nbr B S z)
    (hu : g u ∈ p16Pl g (j, y)) (hw : g w ∈ p16Pl g (j, y)) : B u w = 0 := by
  obtain ⟨v, hv, hgv⟩ := p16r_mem_pl hu
  obtain ⟨v', hv', hgv'⟩ := p16r_mem_pl hw
  have hvN := p16r_trip_nbr hB hS hz hq hv
  have hv'N := p16r_trip_nbr hB hS hz hq hv'
  have hjy : B j y = 0 := ((PointSet.mem_qPairs_iff).1 hq).2.2.1
  have hu' : u ∈ ({v, z * v} : Finset V) := by
    rw [← (R.eq_iff u hun v hvN).1 hgv.symm]
    exact Finset.mem_insert_self _ _
  have hw' : w ∈ ({v', z * v'} : Finset V) := by
    rw [← (R.eq_iff w hwn v' hv'N).1 hgv'.symm]
    exact Finset.mem_insert_self _ _
  rw [PointSet.p16_B_L_inv hB hS hz hvN hv'N hu' hw']
  exact p16r_tri_orth hB hjy hv hv'

open Classical in
private theorem p16r_trip_prod {B : V → V → ZMod 2} (hB : SympForm B) {j y v v' : V}
    (hv : v ∈ ({j, y, j * y} : Finset V)) (hv' : v' ∈ ({j, y, j * y} : Finset V))
    (hne : v ≠ v') : v * v' ∈ ({j, y, j * y} : Finset V) := by
  have e1 : j * (j * y) = y := by rw [← mul_assoc, hB.sq_eq_one j, one_mul]
  have e2 : y * (j * y) = j := by
    rw [show y * (j * y) = j * (y * y) by ac_rfl, hB.sq_eq_one y, mul_one]
  have e3 : j * y * j = y := by
    rw [show j * y * j = j * j * y by ac_rfl, hB.sq_eq_one j, one_mul]
  have e4 : j * y * y = j := by
    rw [show j * y * y = j * (y * y) by ac_rfl, hB.sq_eq_one y, mul_one]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv' ⊢
  rcases hv with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  · exact absurd rfl hne
  · right
    right
    rfl
  · right
    left
    exact e1
  · right
    right
    exact mul_comm _ _
  · exact absurd rfl hne
  · left
    exact e2
  · right
    left
    exact e3
  · left
    exact e4
  · exact absurd rfl hne

open Classical in
private theorem p16r_pl_card [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {j y : V} (hq : (j, y) ∈ qPairs B S z) : (p16Pl g (j, y)).card = 3 := by
  obtain ⟨hj, hy, -, hne⟩ := (PointSet.p16_mem_qPairs_iff_L hB).1 hq
  have hjyN := p16r_qPair_mul_nbr hB hS hz hq
  have hyS : y ∈ S := ((PointSet.mem_nbr_iff).1 hy).1
  have hyz : y ≠ z := ((PointSet.mem_nbr_iff).1 hy).2.1
  have hjz : j ≠ z := ((PointSet.mem_nbr_iff).1 hj).2.1
  have hy1 : y ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hyS)
  have hj1 : j ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact ((PointSet.mem_nbr_iff).1 hj).1)
  have h1 : g j ≠ g y := fun h => hne ((R.eq_iff j hj y hy).1 h).symm
  have h2 : g j ≠ g (j * y) := by
    intro h
    have hm := (R.eq_iff j hj (j * y) hjyN).1 h
    have hmem : j * y ∈ ({j, z * j} : Finset V) := by
      rw [hm]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact hy1 (mul_eq_left.1 h')
    · have h'' : j * y = j * z := by rw [Finset.mem_singleton.1 h', mul_comm]
      exact hyz (mul_left_cancel h'')
  have h3 : g y ≠ g (j * y) := by
    intro h
    have hm := (R.eq_iff y hy (j * y) hjyN).1 h
    have hmem : j * y ∈ ({y, z * y} : Finset V) := by
      rw [hm]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact hj1 (mul_eq_right.1 h')
    · exact hjz (mul_right_cancel (Finset.mem_singleton.1 h'))
  have hnot : g j ∉ ({g y, g (j * y)} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, h2⟩
  show ({g j, g y, g (j * y)} : Finset (Fin 6)).card = 3
  rw [Finset.card_insert_of_notMem hnot, Finset.card_pair h3]

open Classical in
private theorem p16r_pl_sub {g : V → Fin 6} {q r : V × V} (h1 : g r.1 ∈ p16Pl g q)
    (h2 : g r.2 ∈ p16Pl g q) (h3 : g (r.1 * r.2) ∈ p16Pl g q) : p16Pl g r ⊆ p16Pl g q := by
  intro x hx
  unfold p16Pl at hx ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h <;> rw [h]
  · exact h1
  · exact h2
  · exact h3

open Classical in
private theorem p16r_closure [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {j y u w : V} (hq : (j, y) ∈ qPairs B S z) (hun : u ∈ nbr B S z) (hwn : w ∈ nbr B S z)
    (hu : g u ∈ p16Pl g (j, y)) (hw : g w ∈ p16Pl g (j, y)) (huw : g u ≠ g w) :
    g (u * w) ∈ p16Pl g (j, y) := by
  have hBuw := p16r_or hB hS hz R hq hun hwn hu hw
  have hne : ({w, z * w} : Finset V) ≠ {u, z * u} :=
    fun h => huw ((R.eq_iff u hun w hwn).2 h.symm)
  have hq' : (u, w) ∈ qPairs B S z := (PointSet.p16_mem_qPairs_iff_L hB).2 ⟨hun, hwn, hBuw, hne⟩
  have huwN := p16r_qPair_mul_nbr hB hS hz hq'
  obtain ⟨v, hv, hgv⟩ := p16r_mem_pl hu
  obtain ⟨v', hv', hgv'⟩ := p16r_mem_pl hw
  have hvN := p16r_trip_nbr hB hS hz hq hv
  have hv'N := p16r_trip_nbr hB hS hz hq hv'
  have hu' : u ∈ ({v, z * v} : Finset V) := by
    rw [← (R.eq_iff u hun v hvN).1 hgv.symm]
    exact Finset.mem_insert_self _ _
  have hw' : w ∈ ({v', z * v'} : Finset V) := by
    rw [← (R.eq_iff w hwn v' hv'N).1 hgv'.symm]
    exact Finset.mem_insert_self _ _
  have hsame : v ≠ v' := by
    intro h
    apply huw
    rw [← hgv, ← hgv', h]
  have hprod := p16r_trip_prod hB hv hv' hsame
  have hprodN := p16r_trip_nbr hB hS hz hq hprod
  have hLuw := p16r_line_mul_eq hB hu' hw'
  have hgeq' : g (u * w) = g (v * v') := (R.eq_iff _ huwN _ hprodN).2 hLuw
  rw [hgeq']
  unfold p16Pl
  simp only [Finset.mem_insert, Finset.mem_singleton]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hprod
  rcases hprod with h | h | h <;> rw [h]
  · simp
  · simp
  · simp

open Classical in
private theorem p16r_pl_ne [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {j y : V} (hq : (j, y) ∈ qPairs B S z) :
    g j ≠ g y ∧ g j ≠ g (j * y) ∧ g y ≠ g (j * y) := by
  obtain ⟨hj, hy, -, hne⟩ := (PointSet.p16_mem_qPairs_iff_L hB).1 hq
  have hjyN := p16r_qPair_mul_nbr hB hS hz hq
  have hyS : y ∈ S := ((PointSet.mem_nbr_iff).1 hy).1
  have hyz : y ≠ z := ((PointSet.mem_nbr_iff).1 hy).2.1
  have hjz : j ≠ z := ((PointSet.mem_nbr_iff).1 hj).2.1
  have hy1 : y ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hyS)
  have hj1 : j ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact ((PointSet.mem_nbr_iff).1 hj).1)
  refine ⟨fun h => hne ((R.eq_iff j hj y hy).1 h).symm, ?_, ?_⟩
  · intro h
    have hm := (R.eq_iff j hj (j * y) hjyN).1 h
    have hmem : j * y ∈ ({j, z * j} : Finset V) := by
      rw [hm]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact hy1 (mul_eq_left.1 h')
    · have h'' : j * y = j * z := by rw [Finset.mem_singleton.1 h', mul_comm]
      exact hyz (mul_left_cancel h'')
  · intro h
    have hm := (R.eq_iff y hy (j * y) hjyN).1 h
    have hmem : j * y ∈ ({y, z * y} : Finset V) := by
      rw [hm]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact hj1 (mul_eq_right.1 h')
    · exact hjz (mul_right_cancel (Finset.mem_singleton.1 h'))

open Classical in
private theorem p16r_count3 {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    {a1 a2 a3 : α} (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) :
    (({a1, a2, a3} : Finset α).filter P).card =
      (if P a1 then 1 else 0) + (if P a2 then 1 else 0) + (if P a3 then 1 else 0) := by
  rw [Finset.card_filter, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23]
  ring

open Classical in
private theorem p16r_parity (b1 b2 : ZMod 2) :
    (if b1 = 0 then 1 else 0) + (if b2 = 0 then 1 else 0) + (if b1 + b2 = 0 then 1 else 0) = 1 ∨
    (if b1 = 0 then 1 else 0) + (if b2 = 0 then 1 else 0) + (if b1 + b2 = 0 then 1 else 0) = 3 := by
  revert b1 b2
  decide

open Classical in
private theorem p16r_collinear_iff [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {u w : V} (hun : u ∈ nbr B S z) (hwn : w ∈ nbr B S z) (hne : g u ≠ g w) :
    (∃ q : V × V, q ∈ qPairs B S z ∧ g u ∈ p16Pl g q ∧ g w ∈ p16Pl g q) ↔ B u w = 0 := by
  constructor
  · rintro ⟨q, hq, hu, hw⟩
    exact p16r_or hB hS hz R (j := q.1) (y := q.2) hq hun hwn hu hw
  · intro hBuw
    have hne' : ({w, z * w} : Finset V) ≠ {u, z * u} :=
      fun h => hne ((R.eq_iff u hun w hwn).2 h.symm)
    have hq : (u, w) ∈ qPairs B S z := (PointSet.p16_mem_qPairs_iff_L hB).2 ⟨hun, hwn, hBuw, hne'⟩
    refine ⟨(u, w), hq, ?_, ?_⟩
    · unfold p16Pl
      exact Finset.mem_insert_self _ _
    · unfold p16Pl
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

open Classical in
private theorem p16r_plane_eq [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {q : V × V} (hq : q ∈ qPairs B S z) {u w : V} (hun : u ∈ nbr B S z) (hwn : w ∈ nbr B S z)
    (hne : g u ≠ g w) (hu : g u ∈ p16Pl g q) (hw : g w ∈ p16Pl g q) :
    p16Pl g (u, w) = p16Pl g q := by
  have hBuw := p16r_or hB hS hz R (j := q.1) (y := q.2) hq hun hwn hu hw
  have hne' : ({w, z * w} : Finset V) ≠ {u, z * u} :=
    fun h => hne ((R.eq_iff u hun w hwn).2 h.symm)
  have hq' : (u, w) ∈ qPairs B S z := (PointSet.p16_mem_qPairs_iff_L hB).2 ⟨hun, hwn, hBuw, hne'⟩
  have hcl : g (u * w) ∈ p16Pl g q :=
    p16r_closure (j := q.1) (y := q.2) hB hS hz R hq hun hwn hu hw hne
  have hsub := p16r_pl_sub (g := g) (q := q) (r := (u, w)) hu hw hcl
  exact Finset.eq_of_subset_of_card_le hsub (by
    rw [p16r_pl_card hB hS hz R hq', p16r_pl_card hB hS hz R hq])

open Classical in
private theorem p16r_planes_inter [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {q q' : V × V} (hq : q ∈ qPairs B S z) (hq' : q' ∈ qPairs B S z)
    (hne : p16Pl g q ≠ p16Pl g q') : (p16Pl g q ∩ p16Pl g q').card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hcon
  obtain ⟨hiP, hiP'⟩ := Finset.mem_inter.1 hi
  obtain ⟨hjP, hjP'⟩ := Finset.mem_inter.1 hj
  obtain ⟨u, hun, hgu⟩ := R.surj i
  obtain ⟨w, hwn, hgw⟩ := R.surj j
  have hne_uw : g u ≠ g w := by
    rw [hgu, hgw]
    exact hij
  have e1 := p16r_plane_eq hB hS hz R hq hun hwn hne_uw (by rw [hgu]; exact hiP)
    (by rw [hgw]; exact hjP)
  have e2 := p16r_plane_eq hB hS hz R hq' hun hwn hne_uw (by rw [hgu]; exact hiP')
    (by rw [hgw]; exact hjP')
  exact hne (e1.symm.trans e2)

open Classical in
private theorem p16r_H2 [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    (Qf : Finset (V × V)) (hQf : ∀ q, q ∈ Qf ↔ q ∈ qPairs B S z)
    {j y : V} (hq : (j, y) ∈ qPairs B S z) {p : Fin 6} (hp : p ∉ p16Pl g (j, y)) :
    ((p16Pl g (j, y)).filter fun x => ∃ m ∈ Qf.image (p16Pl g), p ∈ m ∧ x ∈ m).card = 1 ∨
    ((p16Pl g (j, y)).filter fun x => ∃ m ∈ Qf.image (p16Pl g), p ∈ m ∧ x ∈ m).card = 3 := by
  obtain ⟨w, hwn, hgw⟩ := R.surj p
  obtain ⟨h12, h13, h23⟩ := p16r_pl_ne hB hS hz R hq
  have hjN := ((PointSet.mem_qPairs_iff).1 hq).1
  have hyN := ((PointSet.mem_qPairs_iff).1 hq).2.1
  have hjyN := p16r_qPair_mul_nbr hB hS hz hq
  have hTmem : ∀ v ∈ ({j, y, j * y} : Finset V), g v ∈ p16Pl g (j, y) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    unfold p16Pl
    rcases hv with h | h | h <;> rw [h] <;> simp
  have hPv : ∀ v ∈ ({j, y, j * y} : Finset V), v ∈ nbr B S z →
      ((∃ m ∈ Qf.image (p16Pl g), p ∈ m ∧ g v ∈ m) ↔ B w v = 0) := by
    intro v hv hvn
    have hgv := hTmem v hv
    have hne : g w ≠ g v := by
      rw [hgw]
      exact fun h => hp (by rw [h]; exact hgv)
    constructor
    · rintro ⟨m, hm, hpm, hvm⟩
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hm
      exact (p16r_collinear_iff hB hS hz R hwn hvn hne).1
        ⟨q', (hQf q').1 hq', by rw [hgw]; exact hpm, hvm⟩
    · intro hBw
      obtain ⟨q', hq', h1, h2⟩ := (p16r_collinear_iff hB hS hz R hwn hvn hne).2 hBw
      exact ⟨p16Pl g q', Finset.mem_image.2 ⟨q', (hQf q').2 hq', rfl⟩,
        by rw [← hgw]; exact h1, h2⟩
  have hcnt := p16r_count3 (fun x => ∃ m ∈ Qf.image (p16Pl g), p ∈ m ∧ x ∈ m) h12 h13 h23
  have hmul : B w (j * y) = B w j + B w y := hB.mul_right w j y
  show (({g j, g y, g (j * y)} : Finset (Fin 6)).filter _).card = 1 ∨
    (({g j, g y, g (j * y)} : Finset (Fin 6)).filter _).card = 3
  rw [hcnt]
  simp only [hPv j (by simp) hjN, hPv y (by simp) hyN, hPv (j * y) (by simp) hjyN, hmul]
  exact p16r_parity (B w j) (B w y)

open Classical in
private theorem p16r_fib2 [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    {u0 : V} (hu0 : u0 ∈ nbr B S z) :
    ((Set.toFinite (nbr B S z)).toFinset.filter fun u => g u = g u0).card = 2 := by
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hz)
  have hzN := PointSet.mul_mem_nbr hB hS hz hu0
  have hset : (Set.toFinite (nbr B S z)).toFinset.filter (fun u => g u = g u0) =
      {u0, z * u0} := by
    ext u
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hun, hg⟩
      have hh := (R.eq_iff u hun u0 hu0).1 hg
      have hmem : u ∈ ({u0, z * u0} : Finset V) := by
        rw [← hh]
        exact Finset.mem_insert_self _ _
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    · rintro (h | h)
      · exact ⟨by rw [h]; exact hu0, by rw [h]⟩
      · exact ⟨by rw [h]; exact hzN.1, by
          rw [h]
          exact (R.eq_iff _ hzN.1 u0 hu0).2 (PointSet.p16_L_comm hB u0)⟩
  rw [hset, Finset.card_pair]
  exact fun h => hz1 (mul_eq_right.1 h.symm)

open Classical in
private theorem p16r_card_fam [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) (R : p16Res B S z g)
    (Qf : Finset (V × V)) (hQf : ∀ q, q ∈ Qf ↔ q ∈ qPairs B S z) (hQc : Qf.card = 72) :
    (Qf.image (p16Pl g)).card = 3 := by
  set Pairs : Finset (Fin 6 × Fin 6) := (Finset.univ : Finset (Fin 6 × Fin 6)).filter
    (fun p => p.1 ≠ p.2 ∧ ∃ q ∈ Qf, p.1 ∈ p16Pl g q ∧ p.2 ∈ p16Pl g q) with hPairs
  have hfib4 : ∀ p ∈ Pairs, (Qf.filter (fun q => (g q.1, g q.2) = p)).card = 4 := by
    rintro ⟨p1, p2⟩ hp
    obtain ⟨-, hpne, q0, hq0, hp1, hp2⟩ := Finset.mem_filter.1 hp
    dsimp only at hpne hp1 hp2
    have hprod : Qf.filter (fun q => (g q.1, g q.2) = (p1, p2)) =
        ((Set.toFinite (nbr B S z)).toFinset.filter fun u => g u = p1) ×ˢ
          ((Set.toFinite (nbr B S z)).toFinset.filter fun u => g u = p2) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, hQf,
        Prod.mk.injEq, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨hq, hgx, hgy⟩
        obtain ⟨hx, hy, -⟩ := (PointSet.mem_qPairs_iff).1 hq
        exact ⟨⟨hx, hgx⟩, ⟨hy, hgy⟩⟩
      · rintro ⟨⟨hx, hgx⟩, ⟨hy, hgy⟩⟩
        have hBxy : B x y = 0 := p16r_or hB hS hz R (j := q0.1) (y := q0.2)
          ((hQf q0).1 hq0) hx hy (by rw [hgx]; exact hp1) (by rw [hgy]; exact hp2)
        have hne' : ({y, z * y} : Finset V) ≠ {x, z * x} := by
          intro h
          apply hpne
          rw [← hgx, ← hgy]
          exact (R.eq_iff x hx y hy).2 h.symm
        exact ⟨(PointSet.p16_mem_qPairs_iff_L hB).2 ⟨hx, hy, hBxy, hne'⟩, hgx, hgy⟩
    rw [hprod, Finset.card_product]
    obtain ⟨u1, hu1, hgu1⟩ := R.surj p1
    obtain ⟨u2, hu2, hgu2⟩ := R.surj p2
    rw [← hgu1, ← hgu2, p16r_fib2 hB hS hz R hu1, p16r_fib2 hB hS hz R hu2]
  have hsumQ : Qf.card = ∑ p ∈ Pairs, (Qf.filter (fun q => (g q.1, g q.2) = p)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro q hq
    have hne : g q.1 ≠ g q.2 := (p16r_pl_ne hB hS hz R (j := q.1) (y := q.2) ((hQf q).1 hq)).1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, q, hq, ?_, ?_⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hP18 : Pairs.card = 18 := by
    rw [Finset.sum_congr rfl hfib4, Finset.sum_const, smul_eq_mul] at hsumQ
    omega
  have hbi : Pairs = (Qf.image (p16Pl g)).biUnion (fun π => π.offDiag) := by
    ext ⟨p1, p2⟩
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_offDiag, hPairs,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, q, hq, h1, h2⟩
      exact ⟨p16Pl g q, ⟨q, hq, rfl⟩, h1, h2, hne⟩
    · rintro ⟨π, ⟨q, hq, rfl⟩, h1, h2, hne⟩
      exact ⟨hne, q, hq, h1, h2⟩
  have hdisj : ∀ π ∈ Qf.image (p16Pl g), ∀ π' ∈ Qf.image (p16Pl g), π ≠ π' →
      Disjoint π.offDiag π'.offDiag := by
    intro π hπ π' hπ' hne
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hπ
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hπ'
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_offDiag] at hp hp'
    have hi := p16r_planes_inter hB hS hz R ((hQf q).1 hq) ((hQf q').1 hq') hne
    have h2 : 1 < (p16Pl g q ∩ p16Pl g q').card :=
      Finset.one_lt_card.2 ⟨p.1, Finset.mem_inter.2 ⟨hp.1, hp'.1⟩, p.2,
        Finset.mem_inter.2 ⟨hp.2.1, hp'.2.1⟩, hp.2.2⟩
    omega
  have hcardbi : Pairs.card = 6 * (Qf.image (p16Pl g)).card := by
    have hoff : ∀ π ∈ Qf.image (p16Pl g), π.offDiag.card = 6 := by
      intro π hπ
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hπ
      rw [Finset.offDiag_card, p16r_pl_card hB hS hz R ((hQf q).1 hq)]
    rw [hbi, Finset.card_biUnion (fun π hπ π' hπ' hne => hdisj π hπ π' hπ' hne),
      Finset.sum_congr rfl hoff, Finset.sum_const, smul_eq_mul, mul_comm]
  omega

open Classical in
private theorem p16r_lines_fib [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z : V}
    (hB : SympForm B) (hS : PointSet B S a) (hz : z ∈ S) {j0 : V} (hj0 : j0 ∈ nbr B S z) :
    ((Set.toFinite (nbr B S z)).toFinset.filter fun u =>
      ({u, z * u} : Finset V) = {j0, z * j0}).card = 2 := by
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hz)
  have hset : (Set.toFinite (nbr B S z)).toFinset.filter
      (fun u => ({u, z * u} : Finset V) = {j0, z * j0}) = {j0, z * j0} := by
    ext u
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, hL⟩
      have hmem : u ∈ ({j0, z * j0} : Finset V) := by
        rw [← hL]
        exact Finset.mem_insert_self _ _
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    · rintro (h | h)
      · exact ⟨by rw [h]; exact hj0, by rw [h]⟩
      · refine ⟨by rw [h]; exact (PointSet.mul_mem_nbr hB hS hz hj0).1, ?_⟩
        rw [h]
        exact PointSet.p16_L_comm hB j0
  rw [hset, Finset.card_pair]
  exact fun h => hz1 (mul_eq_right.1 h.symm)

open Classical in
private theorem p16r_exists_g [Finite V] {B : V → V → ZMod 2} {S : Set V} {z : V}
    (hB : SympForm B) (hS : PointSet B S 6) (hz : z ∈ S) :
    ∃ g : V → Fin 6, Nonempty (p16Res B S z g) := by
  set Nf : Finset V := (Set.toFinite (nbr B S z)).toFinset with hNf
  set Λ : Finset (Finset V) := Nf.image (fun u => ({u, z * u} : Finset V)) with hΛdef
  have hNc : Nf.card = 12 := by
    rw [hNf, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _), hS.card_nbr z hz]
  have hsum : Nf.card = ∑ P ∈ Λ, (Nf.filter fun u => ({u, z * u} : Finset V) = P).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    exact Finset.mem_image_of_mem _ hu
  have hfib : ∀ P ∈ Λ, (Nf.filter fun u => ({u, z * u} : Finset V) = P).card = 2 := by
    intro P hP
    obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.1 hP
    rw [hNf] at hj0 ⊢
    exact p16r_lines_fib hB hS hz (Set.Finite.mem_toFinset _ |>.1 hj0)
  have hΛc : Λ.card = 6 := by
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
    omega
  have hcardΛ : Fintype.card Λ = 6 := by rw [Fintype.card_coe, hΛc]
  let eΛ : Λ ≃ Fin 6 := Fintype.equivFinOfCardEq hcardΛ
  refine ⟨fun u => if h : ({u, z * u} : Finset V) ∈ Λ then eΛ ⟨_, h⟩ else 0, ⟨?_, ?_⟩⟩
  · intro u hu w hw
    have hu' : ({u, z * u} : Finset V) ∈ Λ :=
      Finset.mem_image_of_mem _ (Set.Finite.mem_toFinset _ |>.2 hu)
    have hw' : ({w, z * w} : Finset V) ∈ Λ :=
      Finset.mem_image_of_mem _ (Set.Finite.mem_toFinset _ |>.2 hw)
    simp only [dif_pos hu', dif_pos hw', eΛ.injective.eq_iff, Subtype.mk.injEq]
  · intro i
    obtain ⟨P, hP⟩ := eΛ.surjective i
    obtain ⟨u, hu, hPu⟩ := Finset.mem_image.1 P.2
    have hmemu : ({u, z * u} : Finset V) ∈ Λ := Finset.mem_image_of_mem _ hu
    refine ⟨u, Set.Finite.mem_toFinset _ |>.1 hu, ?_⟩
    show (if h : ({u, z * u} : Finset V) ∈ Λ then eΛ ⟨_, h⟩ else 0) = i
    rw [dif_pos hmemu, ← hP]
    congr 1
    exact Subtype.ext hPu

open Classical in
private theorem p16r_zero_iff [Finite V] {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {z t e : V}
    {x : V → V} {g : V → Fin 6} (hB : SympForm B) (hS : PointSet B S a)
    (hG : GridData B S z t e x) (R : p16Res B S z g) {v : V} (hvN : v ∈ nbr B S z) :
    B e v = 0 ↔ g v = g t ∨ g v = g (x z) := by
  have hz : z ∈ S := hG.z_mem
  have hzW : z ∈ lineW z t := GridData.mem_W_iff.2 (Or.inl rfl)
  have htN : t ∈ nbr B S z := (PointSet.mem_nbr_iff).2 ⟨hG.t_mem, hG.z_ne_t.symm, hG.orth_zt⟩
  have hxzN : x z ∈ nbr B S z := (PointSet.mem_nbr_iff).2 ⟨hG.x_mem z hzW,
    GridData.p16_legPts_ne hS hG hzW (GridData.mem_legPts_iff.2 (Or.inl rfl)),
    hG.x_orth z hzW⟩
  constructor
  · intro hv
    have hI : v ∈ nbr B S z ∩ sigma B S e := ⟨hvN, ((PointSet.mem_nbr_iff).1 hvN).1, hv⟩
    rw [GridData.p16_nbr_W hB hS hG hzW] at hI
    rcases hI with ⟨hvW, hvz⟩ | hvL
    · rcases GridData.mem_W_iff.1 hvW with h | h | h
      · exact absurd (Set.mem_singleton_iff.2 h) hvz
      · left
        rw [h]
      · left
        rw [h]
        exact (R.eq_iff _ (PointSet.mul_mem_nbr hB hS hz htN).1 t htN).2
          (PointSet.p16_L_comm hB t)
    · rcases GridData.mem_legPts_iff.1 hvL with h | h
      · right
        rw [h]
      · right
        rw [h]
        exact (R.eq_iff _ (PointSet.mul_mem_nbr hB hS hz hxzN).1 (x z) hxzN).2
          (PointSet.p16_L_comm hB (x z))
  · rintro (h | h)
    · have hL := (R.eq_iff v hvN t htN).1 h
      have hmem : v ∈ ({t, z * t} : Finset V) := by
        rw [← hL]
        exact Finset.mem_insert_self _ _
      have hvW : v ∈ lineW z t := by
        rcases Finset.mem_insert.1 hmem with h' | h'
        · exact GridData.mem_W_iff.2 (Or.inr (Or.inl h'))
        · exact GridData.mem_W_iff.2 (Or.inr (Or.inr (Finset.mem_singleton.1 h')))
      exact ((GridData.p16_mem_sigma_iff hS hG).2 (Or.inl hvW)).2
    · have hL := (R.eq_iff v hvN (x z) hxzN).1 h
      have hmem : v ∈ ({x z, z * x z} : Finset V) := by
        rw [← hL]
        exact Finset.mem_insert_self _ _
      have hvL : v ∈ GridData.legPts x z := by
        rcases Finset.mem_insert.1 hmem with h' | h'
        · exact GridData.mem_legPts_iff.2 (Or.inl h')
        · exact GridData.mem_legPts_iff.2 (Or.inr (Finset.mem_singleton.1 h'))
      exact ((GridData.p16_sigma_legPts_iff hS hG).2 (Or.inr (Or.inl hvL))).2

theorem false_of_a_six [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) {S : Set V}
    (hS : PointSet B S 6) {z t e : V} {x : V → V} (hG : GridData B S z t e x)
    (hq : (qPairs B S z).ncard = 72) : False := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨g, ⟨R⟩⟩ := p16r_exists_g hB hS hG.z_mem
  set Qf : Finset (V × V) := (Set.toFinite (qPairs B S z)).toFinset with hQfdef
  have hQf : ∀ q, q ∈ Qf ↔ q ∈ qPairs B S z := fun q => Set.Finite.mem_toFinset _
  have hQc : Qf.card = 72 := by
    rw [hQfdef, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact hq
  have hLc := p16r_card_fam hB hS hG.z_mem R Qf hQf hQc
  set Lfam : Finset (Finset (Fin 6)) := Qf.image (p16Pl g) with hLfam
  have hmem : Lfam ∈
      Finset.powersetCard 3 (Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))) := by
    rw [Finset.mem_powersetCard]
    refine ⟨fun π hπ => ?_, hLc⟩
    rw [Finset.mem_powersetCard]
    obtain ⟨q, hq', rfl⟩ := Finset.mem_image.1 hπ
    exact ⟨Finset.subset_univ _, p16r_pl_card hB hS hG.z_mem R ((hQf q).1 hq')⟩
  have H1 : ∀ l ∈ Lfam, ∀ l' ∈ Lfam, l ≠ l' → (l ∩ l').card ≤ 1 := by
    intro l hl l' hl' hne
    obtain ⟨q, hq1, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨q', hq2, rfl⟩ := Finset.mem_image.1 hl'
    exact p16r_planes_inter hB hS hG.z_mem R ((hQf q).1 hq1) ((hQf q').1 hq2) hne
  have H2 : ∀ l ∈ Lfam, ∀ p : Fin 6, p ∉ l →
      (l.filter fun q => ∃ m ∈ Lfam, p ∈ m ∧ q ∈ m).card = 1 ∨
      (l.filter fun q => ∃ m ∈ Lfam, p ∈ m ∧ q ∈ m).card = 3 := by
    intro l hl p hp
    obtain ⟨q, hq1, rfl⟩ := Finset.mem_image.1 hl
    exact p16r_H2 hB hS hG.z_mem R Qf hQf ((hQf q).1 hq1) hp
  have hzW : z ∈ lineW z t := GridData.mem_W_iff.2 (Or.inl rfl)
  have htW : t ∈ lineW z t := GridData.mem_W_iff.2 (Or.inr (Or.inl rfl))
  have htN : t ∈ nbr B S z := (PointSet.mem_nbr_iff).2 ⟨hG.t_mem, hG.z_ne_t.symm, hG.orth_zt⟩
  have hxzN : x z ∈ nbr B S z := (PointSet.mem_nbr_iff).2 ⟨hG.x_mem z hzW,
    GridData.p16_legPts_ne hS hG hzW (GridData.mem_legPts_iff.2 (Or.inl rfl)),
    hG.x_orth z hzW⟩
  have hAB : g t ≠ g (x z) := by
    intro h
    have hL := (R.eq_iff t htN (x z) hxzN).1 h
    have hmem : x z ∈ ({t, z * t} : Finset V) := by
      rw [hL]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hG.x_notMem z hzW (GridData.mem_W_iff.2 (Or.inr (Or.inl h1)))
    · exact hG.x_notMem z hzW (GridData.mem_W_iff.2 (Or.inr (Or.inr (Finset.mem_singleton.1 h1))))
  have hnc : ¬ ∃ l ∈ Lfam, g t ∈ l ∧ g (x z) ∈ l := by
    rintro ⟨l, hl, hA, hB'⟩
    obtain ⟨q, hq1, rfl⟩ := Finset.mem_image.1 hl
    have hBtx := p16r_or hB hS hG.z_mem R (j := q.1) (y := q.2) ((hQf q).1 hq1) htN hxzN hA hB'
    have h1 : B (x z) t = 1 := hG.leg_far z hzW (x z)
      ((GridData.mem_lineThrough_iff).2 (Or.inr (Or.inl rfl)))
      (GridData.p16_legPts_ne hS hG hzW (GridData.mem_legPts_iff.2 (Or.inl rfl))) t htW
      hG.z_ne_t.symm
    have h2 : B t (x z) = 1 := (hB.symm t (x z)).trans h1
    rw [hBtx] at h2
    exact absurd h2 (by decide)
  have H3 : ∀ l ∈ Lfam, (l ∩ {g t, g (x z)}).card = 1 := by
    intro l hl
    obtain ⟨q, hq1, rfl⟩ := Finset.mem_image.1 hl
    have hqq : (q.1, q.2) ∈ qPairs B S z := (hQf q).1 hq1
    obtain ⟨hjN, hyN, hjy, hne1, hne2⟩ := (PointSet.mem_qPairs_iff).1 hqq
    have hjyN := p16r_qPair_mul_nbr hB hS hG.z_mem hqq
    have hT : p16Pl g q ∩ ({g t, g (x z)} : Finset (Fin 6)) =
        (p16Pl g q).filter (fun w => w ∈ ({g t, g (x z)} : Finset (Fin 6))) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter]
    rw [hT]
    obtain ⟨h12, h13, h23⟩ := p16r_pl_ne hB hS hG.z_mem R hqq
    show (({g q.1, g q.2, g (q.1 * q.2)} : Finset (Fin 6)).filter _).card = 1
    rw [p16r_count3 _ h12 h13 h23]
    have Z1 : g q.1 ∈ ({g t, g (x z)} : Finset (Fin 6)) ↔ B e q.1 = 0 := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact (p16r_zero_iff hB hS hG R hjN).symm
    have Z2 : g q.2 ∈ ({g t, g (x z)} : Finset (Fin 6)) ↔ B e q.2 = 0 := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact (p16r_zero_iff hB hS hG R hyN).symm
    have Z3 : g (q.1 * q.2) ∈ ({g t, g (x z)} : Finset (Fin 6)) ↔ B e (q.1 * q.2) = 0 := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact (p16r_zero_iff hB hS hG R hjyN).symm
    simp only [Z1, Z2, Z3]
    rcases GridData.exactly_one_zero hB hS hG hjN hyN hjy hne1 hne2 with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]
  exact residue_six_false Lfam hmem H1 H2 (g t) (g (x z)) hAB hnc H3

private theorem p16_orth_closure {B : V → V → ZMod 2} (hB : SympForm B) (e : V) (T : Set V)
    (h : ∀ y ∈ T, B e y = 0) : ∀ g ∈ Subgroup.closure T, B e g = 0 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one =>
    have h1 := hB.mul_right e 1 1
    rw [mul_one] at h1
    exact p16_self_eq_add _ h1
  | mul x y _ _ hx hy => rw [hB.mul_right, hx, hy, add_zero]
  | inv x _ hx =>
    rw [inv_eq_of_mul_eq_one_right (hB.sq_eq_one x)]
    exact hx

theorem false_of_gridData [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) {S : Set V} {a : ℕ}
    (hS : PointSet B S a) (hspan : Subgroup.closure S = ⊤) (hcard : 64 ≤ Nat.card V)
    {z t e : V} {x : V → V} (hG : GridData B S z t e x) : False := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hz : z ∈ S := hG.z_mem
  obtain ⟨hE2, h9, ha2⟩ := GridData.edge_count hB hS hG
  have hcm := PointSet.card_mul hB hS hz
  have hdiv8 := PointSet.eight_dvd_card_qPairs hB hS hz
  have hs2 : 2 * a + 1 ≤ S.ncard := by
    have hzN : z ∉ nbr B S z := fun h => ((PointSet.mem_nbr_iff).1 h).2.1 rfl
    have hsub : insert z (nbr B S z) ⊆ S := by
      intro y hy
      rcases hy with h | h
      · rw [h]
        exact hz
      · exact ((PointSet.mem_nbr_iff).1 h).1
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hzN, hS.card_nbr z hz] at h1
    exact h1
  have hE3 : S.ncard * a + 36 = 27 * a := by
    have e1 : S.ncard * a = (S.ncard - 9) * a + 9 * a := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  have hE4 : (qPairs B S z).ncard + 30 * a = 6 * a * a + 36 := by
    nlinarith [hcm, hE3]
  have hdvd : a ∣ 36 := by
    have h1 : a ∣ (S.ncard - 9) * a + 36 := by
      rw [hE2]
      exact dvd_mul_left a 18
    exact (Nat.dvd_add_right (dvd_mul_left a (S.ncard - 9))).1 h1
  have hle36 : a ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 ∨ a = 9 ∨ a = 12 ∨ a = 18 ∨ a = 36 := by
    interval_cases a <;> first | omega | norm_num at hdvd
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hS9 : S.ncard = 9 := by omega
    have hsig := GridData.card_sigma hB hS hG
    have hSgEq : sigma B S e = S := by
      apply Set.eq_of_subset_of_ncard_le (fun y hy => hy.1)
      omega
    have hall : ∀ y ∈ S, B e y = 0 := fun y hy => by
      have hy' : y ∈ sigma B S e := by
        rw [hSgEq]
        exact hy
      exact hy'.2
    have hall' : ∀ g : V, B e g = 0 := fun g =>
      p16_orth_closure hB e S hall g (by rw [hspan]; exact Subgroup.mem_top g)
    exact hG.e_ne_one (hB.nondeg e hall')
  ·
    have hq0 : qPairs B S z = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 (by omega)
    have hbound := PointSet.natCard_le_of_qPairs_eq_empty hB hS hspan hz hq0 (by norm_num)
    have h32 : (2 : ℕ) ^ (3 + 2) = 32 := by norm_num
    rw [h32] at hbound
    omega
  ·
    have hq12 : (qPairs B S z).ncard = 12 := by omega
    rw [hq12] at hdiv8
    norm_num at hdiv8
  ·
    exact false_of_a_six hB hS hG (by omega)
  ·
    have hq : (qPairs B S z).ncard = 252 := by omega
    rw [hq] at hdiv8
    norm_num at hdiv8
  ·
    have hq : (qPairs B S z).ncard = 540 := by omega
    rw [hq] at hdiv8
    norm_num at hdiv8
  ·
    omega
  ·
    omega

end CFSG.ClassicalInvolution.Q3.Sec13.Polar
