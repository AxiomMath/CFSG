module

public import CFSG.GF2Type.SmithTypeE.E7.E23aModel
public import CFSG.GF2Type.SmithTypeE.E7.E23aRig
public import CFSG.Certificates.OrbitChain
public import Certificates.Certificate38803

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup
open CFSG.SmithD6 (tvImg ea7I ea7InX ea7InY ea7InF0 ea7IsA ea7Bases ea7Sizes)
open CFSG.GF2Type.SmithTypeE.DMod

section Checks

theorem ea7ChainCheck_holds : ∀ t < 5, ∃ S : List ℕ, S.length = ea7Sizes[t]! ∧ S.Nodup ∧
    ∀ x ∈ S, x < 365211 ∧ Relation.ReflTransGen
      (fun a b => ∃ q, ea7InY (ea7Bases.take t) q = true ∧ tvImg q a = b) ea7Bases[t]! x :=
  Certificates.certificate38803.1

theorem ea7OddCheck_holds : ea7I.length = 1578 ∧
    (∀ q ∈ ea7I, ∀ a, ea7IsA a = true → ea7IsA (tvImg q a) = true) ∧
    ea7InX 31 = true ∧ ea7InX 557 = true ∧ ea7InX 1083 = true ∧
    tvImg 557 31 = 1083 ∧ tvImg 1083 31 = 557 ∧
    ea7InX ea7Bases[0]! = true ∧ ea7IsA ea7Bases[0]! = false :=
  Certificates.certificate38803.2

end Checks

theorem exists_fixed_of_odd {α : Type} [Finite α] (N : Subgroup (Equiv.Perm α)) (hN : IsPGroup 2 N)
    (O : Set α) (hO : ∀ n ∈ N, ∀ a ∈ O, n a ∈ O) (hodd : Odd (Nat.card O)) :
    ∃ a ∈ O, ∀ n ∈ N, n a = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : SubMulAction N α :=
    { carrier := O
      smul_mem' := by
        intro c x hx
        exact hO (c : Equiv.Perm α) c.2 x hx }
  have hoddS : Odd (Nat.card S) := hodd
  have hmod : Nat.card S ≡ Nat.card (MulAction.fixedPoints N S) [MOD 2] :=
    IsPGroup.card_modEq_card_fixedPoints hN ↥S
  have hne : Nat.card (MulAction.fixedPoints N S) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hoddS
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨y⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  have hy := MulAction.mem_fixedPoints.mp y.2
  refine ⟨y.1.1, y.1.2, fun n hn => ?_⟩
  have h1 := congrArg Subtype.val (hy ⟨n, hn⟩)
  exact h1

theorem fixes_of_normal {α : Type} [Finite α] (L N : Subgroup (Equiv.Perm α)) (hNL : N ≤ L)
    (hN : IsPGroup 2 N) (hnorm : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (O : Set α) (b : α) (hb : b ∈ O)
    (hinv : ∀ l ∈ L, ∀ a ∈ O, l a ∈ O) (htrans : ∀ a ∈ O, ∃ l ∈ L, l b = a)
    (hodd : Odd (Nat.card O)) : ∀ a ∈ O, ∀ n ∈ N, n a = a := by
  have hO : ∀ n ∈ N, ∀ a ∈ O, n a ∈ O := fun n hn a ha => hinv n (hNL hn) a ha
  obtain ⟨a₀, ha₀, hfix⟩ := exists_fixed_of_odd N hN O hO hodd
  intro a ha n hn
  obtain ⟨l, hl, hlb⟩ := htrans a ha
  obtain ⟨l₀, hl₀, hl₀b⟩ := htrans a₀ ha₀
  obtain ⟨g, hgL, hga₀⟩ : ∃ g ∈ L, g a₀ = a :=
    ⟨l * l₀⁻¹, L.mul_mem hl (L.inv_mem hl₀), by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr hl₀b.symm, hlb]⟩
  have hm : g⁻¹ * n * g ∈ N := by
    have h := hnorm g⁻¹ (L.inv_mem hgL) n hn
    rwa [inv_inv] at h
  have hmfix : (g⁻¹ * n * g) a₀ = a₀ := hfix _ hm
  have key : n * g = g * (g⁻¹ * n * g) := by group
  calc n a = n (g a₀) := by rw [hga₀]
    _ = (n * g) a₀ := by rw [Equiv.Perm.mul_apply]
    _ = (g * (g⁻¹ * n * g)) a₀ := by rw [key]
    _ = g ((g⁻¹ * n * g) a₀) := by rw [Equiv.Perm.mul_apply]
    _ = g a₀ := by rw [hmfix]
    _ = a := hga₀

section Tree

theorem chain_witnesses {i : ℕ} (hi : i < 5) :
    ∃ (b' : Fin 365211) (S : Finset (Fin 365211)), b'.val = ea7Bases[i]! ∧ S.card = ea7Sizes[i]! ∧
      ∀ p ∈ S, ∃ g ∈ Subgroup.closure
        (tvP '' {q : Fin 365211 | ea7InY (ea7Bases.take i) q.val = true}), g b' = p := by
  obtain ⟨S, hlen, hnd, hS⟩ := ea7ChainCheck_holds i hi
  have hb : ea7Bases[i]! < 365211 := by
    interval_cases i <;> decide
  have key : ∀ x, Relation.ReflTransGen
      (fun a b => ∃ q, ea7InY (ea7Bases.take i) q = true ∧ tvImg q a = b) ea7Bases[i]! x →
      ∃ g ∈ Subgroup.closure (tvP '' {q : Fin 365211 | ea7InY (ea7Bases.take i) q.val = true}),
        ((g ⟨ea7Bases[i]!, hb⟩ : Fin 365211) : ℕ) = x := by
    intro x hx
    induction hx with
    | refl => exact ⟨1, Subgroup.one_mem _, rfl⟩
    | tail _ hst ih =>
      obtain ⟨g, hg, hgc⟩ := ih
      obtain ⟨q, hq, hqd⟩ := hst
      have hqlt : q < 365211 := by
        have h := hq
        simp only [ea7InY, CFSG.SmithD6.ea7InX, Bool.and_eq_true, decide_eq_true_eq,
          and_assoc] at h
        exact h.1
      refine ⟨tvP ⟨q, hqlt⟩ * g,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨q, hqlt⟩, hq, rfl⟩) hg, ?_⟩
      rw [Equiv.Perm.mul_apply, tvP_apply, hgc]
      exact hqd
  refine ⟨⟨ea7Bases[i]!, hb⟩, S.toFinset.image
      (fun x => (⟨x % 365211, Nat.mod_lt _ (by norm_num)⟩ : Fin 365211)), rfl, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro x hx y hy hxy
    have hv : x % 365211 = y % 365211 := congrArg Fin.val hxy
    rwa [Nat.mod_eq_of_lt (hS x (List.mem_toFinset.1 (Finset.mem_coe.1 hx))).1,
      Nat.mod_eq_of_lt (hS y (List.mem_toFinset.1 (Finset.mem_coe.1 hy))).1] at hv
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    have hx' := hS x (List.mem_toFinset.1 hx)
    obtain ⟨g, hg, hgx⟩ := key x hx'.2
    refine ⟨g, hg, Fin.ext ?_⟩
    change ((g ⟨ea7Bases[i]!, hb⟩ : Fin 365211) : ℕ) = x % 365211
    rw [hgx, Nat.mod_eq_of_lt hx'.1]

end Tree

theorem nodup_ea7I : ea7I.Nodup := by
  unfold ea7I
  exact List.Nodup.filter _ (List.nodup_range ..)

theorem card_fin_subtype_eq (n : ℕ) (P : ℕ → Bool) (S : Finset ℕ)
    (hS : ∀ x, x ∈ S ↔ x < n ∧ P x = true) :
    Nat.card {p : Fin n // P p.val = true} = S.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun p => ⟨p.1.val, (hS p.1.val).2 ⟨p.1.isLt, p.2⟩⟩,
      invFun := fun x => ⟨⟨x.1, ((hS x.1).1 x.2).1⟩, ((hS x.1).1 x.2).2⟩,
      left_inv := fun p => Subtype.ext (Fin.ext rfl),
      right_inv := fun x => Subtype.ext rfl }

theorem card_fin_subtype_filter (n : ℕ) (P Q : ℕ → Bool) (S : Finset ℕ)
    (hS : ∀ x, x ∈ S ↔ x < n ∧ P x = true) :
    Nat.card {p : Fin n // P p.val = true ∧ Q p.val = false} =
      (S.filter fun a => Q a = false).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun p => ⟨p.1.val, Finset.mem_filter.2 ⟨(hS p.1.val).2 ⟨p.1.isLt, p.2.1⟩, p.2.2⟩⟩,
      invFun := fun x => ⟨⟨x.1, ((hS x.1).1 (Finset.mem_filter.1 x.2).1).1⟩,
        ((hS x.1).1 (Finset.mem_filter.1 x.2).1).2, (Finset.mem_filter.1 x.2).2⟩,
      left_inv := fun p => Subtype.ext (Fin.ext rfl),
      right_inv := fun x => Subtype.ext rfl }

theorem card_filter_split (S : Finset ℕ) (Q : ℕ → Bool) (k : ℕ)
    (hk : (S.filter fun a => Q a = true).card = k) :
    (S.filter fun a => Q a = false).card + k = S.card := by
  have h : (S.filter fun a => Q a = true).card + (S.filter fun a => ¬ (Q a = true)).card = S.card :=
    Finset.card_filter_add_card_filter_not (fun a => Q a = true)
  have e : S.filter (fun a => ¬ (Q a = true)) = S.filter (fun a => Q a = false) := by
    apply Finset.filter_congr
    intro a _
    simp
  rw [e] at h
  omega

theorem mem_ASet (x : ℕ) : x ∈ ({31, 557, 1083} : Finset ℕ) ↔ x < 365211 ∧ ea7IsA x = true := by
  unfold ea7IsA
  simp only [Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (rfl | rfl | rfl) <;> simp
  · rintro ⟨-, h⟩
    rcases h with (h | h) | h <;> simp [h]

theorem ea7IsA_inX (h31 : ea7InX 31 = true) (h557 : ea7InX 557 = true) (h1083 : ea7InX 1083 = true)
    (x : ℕ) (h : ea7IsA x = true) : ea7InX x = true := by
  unfold ea7IsA at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact h31
  · exact h557
  · exact h1083

theorem mem_ea7I_toFinset (x : ℕ) : x ∈ ea7I.toFinset ↔ x < 365211 ∧ ea7InX x = true :=
  List.mem_toFinset.trans mem_ea7I_iff

theorem card_ASet : Nat.card {p : Fin 365211 // ea7IsA p.val = true} = 3 :=
  (card_fin_subtype_eq 365211 ea7IsA {31, 557, 1083} mem_ASet).trans (by decide)

theorem card_BSet (h31 : ea7InX 31 = true) (h557 : ea7InX 557 = true) (h1083 : ea7InX 1083 = true) :
    Nat.card {p : Fin 365211 // ea7InX p.val = true ∧ ea7IsA p.val = false} = ea7I.length - 3 := by
  have hA : (ea7I.toFinset.filter fun a => ea7IsA a = true).card = 3 := by
    have e : ea7I.toFinset.filter (fun a => ea7IsA a = true) = {31, 557, 1083} := by
      ext x
      rw [Finset.mem_filter, mem_ea7I_toFinset x, mem_ASet x]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, ea7IsA_inX h31 h557 h1083 x h2⟩, h2⟩
    rw [e]
    decide
  have hsplit := card_filter_split ea7I.toFinset ea7IsA 3 hA
  have hc : ea7I.toFinset.card = ea7I.length := List.toFinset_card_of_nodup nodup_ea7I
  rw [card_fin_subtype_filter 365211 ea7InX ea7IsA ea7I.toFinset mem_ea7I_toFinset]
  omega

section Chain

@[expose] def ea7Gen (i : ℕ) : Set (Fin 365211) := {q | ea7InY (ea7Bases.take i) q.val = true}

@[expose] def ea7L (i : ℕ) : Subgroup (Equiv.Perm (Fin 365211)) :=
  Subgroup.closure (tvP '' ea7Gen i)

theorem ea7InY_succ {i : ℕ} (hi : i < 5) (q : ℕ) :
    ea7InY (ea7Bases.take (i + 1)) q =
      (ea7InY (ea7Bases.take i) q && tvImg q ea7Bases[i]! == ea7Bases[i]!) := by
  interval_cases i <;>
    simp [ea7InY, ea7Bases, Bool.and_assoc]

theorem ea7Sizes_zero : ea7Sizes[0]! = 1575 := rfl
theorem ea7Sizes_one : ea7Sizes[1]! = 864 := rfl
theorem ea7Sizes_two : ea7Sizes[2]! = 128 := rfl
theorem ea7Sizes_three : ea7Sizes[3]! = 3 := rfl
theorem ea7Sizes_four : ea7Sizes[4]! = 2 := rfl

theorem level_step {i : ℕ} (hi : i < 5) :
    ea7Sizes[i]! * Nat.card ↥(ea7L (i + 1)) ≤ Nat.card ↥(ea7L i) := by
  obtain ⟨b', S, hb', hS, hSw⟩ := chain_witnesses hi
  have key := CFSG.Certificates.card_mul_card_inf_stabilizer_le (ea7L i) b' S hSw
  rw [hS] at key
  refine le_trans (Nat.mul_le_mul_left _ ?_) key
  apply Subgroup.card_le_of_le
  rw [ea7L, Subgroup.closure_le]
  rintro _ ⟨q, hq, rfl⟩
  have hq' : ea7InY (ea7Bases.take i) q.val = true ∧ tvImg q.val ea7Bases[i]! = ea7Bases[i]! := by
    have h := hq
    simp only [ea7Gen, Set.mem_setOf_eq] at h
    rw [ea7InY_succ hi] at h
    simpa using h
  refine ⟨Subgroup.subset_closure ⟨q, hq'.1, rfl⟩, ?_⟩
  show tvP q ∈ MulAction.stabilizer (Equiv.Perm (Fin 365211)) b'
  rw [MulAction.mem_stabilizer_iff]
  exact Fin.ext (by rw [Equiv.Perm.smul_def, tvP_apply, hb']; exact hq'.2)

theorem card_ea7L_zero : 1045094400 ≤ Nat.card ↥(ea7L 0) := by
  have h0 : 1575 * Nat.card ↥(ea7L 1) ≤ Nat.card ↥(ea7L 0) := by
    have := level_step (i := 0) (by norm_num)
    rwa [ea7Sizes_zero] at this
  have h1 : 864 * Nat.card ↥(ea7L 2) ≤ Nat.card ↥(ea7L 1) := by
    have := level_step (i := 1) (by norm_num)
    rwa [ea7Sizes_one] at this
  have h2 : 128 * Nat.card ↥(ea7L 3) ≤ Nat.card ↥(ea7L 2) := by
    have := level_step (i := 2) (by norm_num)
    rwa [ea7Sizes_two] at this
  have h3 : 3 * Nat.card ↥(ea7L 4) ≤ Nat.card ↥(ea7L 3) := by
    have := level_step (i := 3) (by norm_num)
    rwa [ea7Sizes_three] at this
  have h4 : 2 * Nat.card ↥(ea7L 5) ≤ Nat.card ↥(ea7L 4) := by
    have := level_step (i := 4) (by norm_num)
    rwa [ea7Sizes_four] at this
  have h5 : 1 ≤ Nat.card ↥(ea7L 5) := Nat.card_pos
  omega

end Chain

def setStab {α : Type} (Y : Set α) : Subgroup (Equiv.Perm α) where
  carrier := {g | g '' Y = Y}
  mul_mem' := by
    intro a b ha hb
    have ha' : a '' Y = Y := ha
    have hb' : b '' Y = Y := hb
    show (a * b) '' Y = Y
    rw [Equiv.Perm.coe_mul, Set.image_comp, hb', ha']
  one_mem' := by
    show (1 : Equiv.Perm α) '' Y = Y
    rw [Equiv.Perm.coe_one, Set.image_id]
  inv_mem' := by
    intro a ha
    have ha' : a '' Y = Y := ha
    show (⇑(a⁻¹) : α → α) '' Y = Y
    calc (⇑(a⁻¹) : α → α) '' Y = (⇑(a⁻¹) : α → α) '' (a '' Y) := by rw [ha']
      _ = Y := by
        rw [← Set.image_comp]
        have : (⇑(a⁻¹) ∘ ⇑a : α → α) = id := by
          funext x
          simp
        rw [this, Set.image_id]

theorem image_eq_of_invol {α : Type} {g : Equiv.Perm α} (hg : g * g = 1) {Y : Set α}
    (h : ∀ y ∈ Y, g y ∈ Y) : g '' Y = Y := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h y hy
  · intro hx
    refine ⟨g x, h x hx, ?_⟩
    have := congrArg (fun f : Equiv.Perm α => f x) hg
    simpa [Equiv.Perm.mul_apply] using this

section Lstd

abbrev Lstd : Subgroup (Equiv.Perm (Fin 365211)) :=
  closure (tvP '' {k : Fin 365211 | Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP stdOpp)})

theorem ea7L_zero_eq : ea7L 0 = Lstd := by
  have h : ea7Gen 0 =
      {k : Fin 365211 | Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP stdOpp)} := by
    ext q
    simp only [ea7Gen, Set.mem_setOf_eq, List.take_zero, ea7InY, List.all_nil, Bool.and_true]
    exact ea7InX_iff
  rw [ea7L, h]

theorem Lstd_le_TD6 : Lstd ≤ TD6 :=
  (Subgroup.closure_le _).mpr (by rintro _ ⟨k, -, rfl⟩; exact tvP_mem k)

theorem Lstd_fix {g : Equiv.Perm (Fin 365211)} (hg : g ∈ Lstd) : g 0 = 0 ∧ g stdOpp = stdOpp := by
  have hle : Lstd ≤ MulAction.stabilizer (Equiv.Perm (Fin 365211)) (0 : Fin 365211) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 365211)) stdOpp := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, ⟨h0, h1⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show tvP k ∈ MulAction.stabilizer (Equiv.Perm (Fin 365211)) (0 : Fin 365211)
      rw [MulAction.mem_stabilizer_iff]
      have e := tvImg_eq_of_commute (a := k) (b := 0) h0.eq
      exact Fin.ext (by rw [Equiv.Perm.smul_def, tvP_apply]; exact e)
    · show tvP k ∈ MulAction.stabilizer (Equiv.Perm (Fin 365211)) stdOpp
      rw [MulAction.mem_stabilizer_iff]
      have e := tvImg_eq_of_commute (a := k) (b := stdOpp) h1.eq
      exact Fin.ext (by rw [Equiv.Perm.smul_def, tvP_apply]; exact e)
  obtain ⟨h0, h1⟩ := hle hg
  exact ⟨h0, h1⟩

theorem card_Lstd_ge : 1045094400 ≤ Nat.card ↥Lstd := by
  have h := card_ea7L_zero
  rwa [ea7L_zero_eq] at h

end Lstd

section Odd

theorem odd_facts :
    ea7I.length = 1578 ∧
    (∀ q ∈ ea7I, ∀ a, ea7IsA a = true → ea7IsA (tvImg q a) = true) ∧
    ea7InX 31 = true ∧ ea7InX 557 = true ∧ ea7InX 1083 = true ∧
    tvImg 557 31 = 1083 ∧ tvImg 1083 31 = 557 ∧
    ea7InX ea7Bases[0]! = true ∧ ea7IsA ea7Bases[0]! = false :=
  ea7OddCheck_holds

@[expose] def XSet : Set (Fin 365211) := {p | ea7InX p.val = true}

@[expose] def ASet : Set (Fin 365211) := {p | ea7IsA p.val = true}

@[expose] def BSet : Set (Fin 365211) := {p | ea7InX p.val = true ∧ ea7IsA p.val = false}

theorem BSet_eq : BSet = XSet \ ASet := by
  ext p
  simp only [BSet, XSet, ASet, Set.mem_setOf_eq, Set.mem_diff, Bool.not_eq_true]

theorem lt_of_ea7InX {p : ℕ} (h : ea7InX p = true) : p < 365211 := by
  simp only [CFSG.SmithD6.ea7InX, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem isA_cases {a : ℕ} (h : ea7IsA a = true) : a = 31 ∨ a = 557 ∨ a = 1083 := by
  simpa [CFSG.SmithD6.ea7IsA, Bool.or_eq_true, beq_iff_eq, or_assoc] using h

theorem gen_preserves {q : Fin 365211} (hq : ea7InX q.val = true) :
    tvP q '' XSet = XSet ∧ tvP q '' ASet = ASet := by
  obtain ⟨-, hinvA, h31, h557, h1083, -, -, -, -⟩ := odd_facts
  have hqI : q.val ∈ ea7I := mem_ea7I_iff.mpr ⟨q.2, hq⟩
  have hinvol : ∀ a : Fin 365211, tvP q (tvP q a) = a := fun a => by
    have h := congrArg (fun f : Equiv.Perm (Fin 365211) => f a) (tvP_mul_self q)
    simpa [Equiv.Perm.mul_apply] using h
  have hX : ∀ p : Fin 365211, ea7InX p.val = true → ea7InX (tvP q p).val = true ∧
      ea7IsA (tvP q p).val = ea7IsA p.val := by
    intro p hp
    obtain ⟨hq0, hq1⟩ := ea7InX_iff.mp hq
    obtain ⟨hp0, hp1⟩ := ea7InX_iff.mp hp
    have hconj : tvP (tvP q p) = tvP q * tvP p * (tvP q)⁻¹ :=
      (mul_tvP_mul_inv (tvP_mem q) p).symm
    refine ⟨ea7InX_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hconj]
      exact (hq0.mul_left hp0).mul_left hq0.inv_left
    · rw [hconj]
      exact (hq1.mul_left hp1).mul_left hq1.inv_left
    · cases hA : ea7IsA p.val
      · by_contra hne
        have h2 := hinvA q.val hqI _ (by simpa using hne)
        rw [← tvP_apply, hinvol, hA] at h2
        exact Bool.false_ne_true h2
      · rw [tvP_apply]
        exact hinvA q.val hqI p.val hA
  refine ⟨image_eq_of_invol (tvP_mul_self q) fun p hp => (hX p hp).1, ?_⟩
  refine image_eq_of_invol (tvP_mul_self q) fun p hp => ?_
  have hpX : ea7InX p.val = true := by
    have := isA_cases hp
    rcases this with h | h | h <;> rw [h] <;> assumption
  show ea7IsA (tvP q p).val = true
  rw [(hX p hpX).2]
  exact hp

theorem Lstd_preserves {g : Equiv.Perm (Fin 365211)} (hg : g ∈ Lstd) :
    g '' XSet = XSet ∧ g '' ASet = ASet := by
  have hle : Lstd ≤ setStab XSet ⊓ setStab ASet := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, ⟨h0, h1⟩, rfl⟩
    have hk : ea7InX k.val = true := ea7InX_iff.mpr ⟨h0, h1⟩
    exact ⟨(gen_preserves hk).1, (gen_preserves hk).2⟩
  exact hle hg

theorem tvP_mem_Lstd {p : Fin 365211} (hp : ea7InX p.val = true) : tvP p ∈ Lstd :=
  Subgroup.subset_closure ⟨p, ea7InX_iff.mp hp, rfl⟩

theorem exists_mem_Lstd_A {a : Fin 365211} (ha : a ∈ ASet) :
    ∃ l ∈ Lstd, l ⟨31, by norm_num⟩ = a := by
  obtain ⟨-, -, h31, h557, h1083, h6, h7, -, -⟩ := odd_facts
  rcases isA_cases ha with h | h | h
  · exact ⟨1, Subgroup.one_mem _, Fin.ext (by rw [Equiv.Perm.one_apply, h])⟩
  · refine ⟨tvP ⟨1083, by norm_num⟩, tvP_mem_Lstd (p := ⟨1083, by norm_num⟩) h1083, ?_⟩
    exact Fin.ext (by rw [tvP_apply, h]; exact h7)
  · refine ⟨tvP ⟨557, by norm_num⟩, tvP_mem_Lstd (p := ⟨557, by norm_num⟩) h557, ?_⟩
    exact Fin.ext (by rw [tvP_apply, h]; exact h6)

theorem exists_mem_Lstd_B {a : Fin 365211} (ha : a ∈ BSet) :
    ∃ l ∈ Lstd, l ⟨ea7Bases[0]!, lt_of_ea7InX odd_facts.2.2.2.2.2.2.2.1⟩ = a := by
  obtain ⟨hlen, -, h31, h557, h1083, -, -, hb1, hb2⟩ := odd_facts
  obtain ⟨b', S, hb', hS, hSw⟩ := chain_witnesses (i := 0) (by norm_num)
  have hb'eq : b' = ⟨ea7Bases[0]!, lt_of_ea7InX hb1⟩ := Fin.ext hb'
  have hbB : b' ∈ BSet := by
    rw [hb'eq]
    exact ⟨hb1, hb2⟩
  have hSB : (S : Set (Fin 365211)) ⊆ BSet := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := hSw p hp
    have hg' : g ∈ Lstd := by rwa [← ea7L_zero_eq]
    rw [BSet_eq]
    have hX := (Lstd_preserves hg').1
    have hA := (Lstd_preserves hg').2
    have hmem : g b' ∈ g '' (XSet \ ASet) := ⟨b', by rw [← BSet_eq]; exact hbB, rfl⟩
    rwa [Set.image_diff g.injective, hX, hA] at hmem
  have hcardB : Nat.card ↥BSet = 1575 := by
    have := card_BSet h31 h557 h1083
    rw [hlen] at this
    exact this
  have hSeq : (S : Set (Fin 365211)) = BSet := by
    refine Set.eq_of_subset_of_ncard_le hSB ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hS, ← Nat.card_coe_set_eq, hcardB]
    exact le_of_eq ea7Sizes_zero.symm
  have hap : a ∈ (S : Set (Fin 365211)) := by rw [hSeq]; exact ha
  obtain ⟨g, hg, hga⟩ := hSw a hap
  refine ⟨g, by rwa [← ea7L_zero_eq], ?_⟩
  rw [← hb'eq]
  exact hga

theorem fixes_X_of_normal {N : Subgroup (Equiv.Perm (Fin 365211))} (hNL : N ≤ Lstd)
    (hN : IsPGroup 2 N) (hnorm : ∀ l ∈ Lstd, ∀ n ∈ N, l * n * l⁻¹ ∈ N) :
    ∀ p : Fin 365211, ea7InX p.val = true → ∀ n ∈ N, n p = p := by
  obtain ⟨hlen, -, h31, h557, h1083, -, -, hb1, hb2⟩ := odd_facts
  intro p hp n hn
  by_cases hpA : ea7IsA p.val = true
  ·
    have hA := fixes_of_normal Lstd N hNL hN hnorm ASet ⟨31, by norm_num⟩
      (by show ea7IsA 31 = true; rfl)
      (fun l hl a ha => by
        rw [← (Lstd_preserves hl).2]
        exact Set.mem_image_of_mem l ha)
      (fun a ha => exists_mem_Lstd_A ha)
      (by rw [show Nat.card ↥ASet = 3 from card_ASet]; decide)
    exact hA p hpA n hn
  ·
    have hpB : p ∈ BSet := ⟨hp, by simpa using hpA⟩
    have hB := fixes_of_normal Lstd N hNL hN hnorm BSet
      ⟨ea7Bases[0]!, lt_of_ea7InX hb1⟩ ⟨hb1, hb2⟩
      (fun l hl a ha => by
        rw [BSet_eq] at ha ⊢
        rw [← (Lstd_preserves hl).1, ← (Lstd_preserves hl).2, ← Set.image_diff l.injective]
        exact Set.mem_image_of_mem l ha)
      (fun a ha => exists_mem_Lstd_B ha)
      (by
        rw [show Nat.card ↥BSet = 1575 from by
          have := card_BSet h31 h557 h1083
          rw [hlen] at this
          exact this]
        decide)
    exact hB p hpB n hn

theorem eq_one_of_normal_pgroup_std {K : Type} [Group K] (f : ↥Lstd →* K)
    (hf : Function.Injective f) {P : Subgroup K} (hP2 : IsPGroup 2 P)
    (hnorm : ∀ g : ↥Lstd, ∀ p ∈ P, f g * p * (f g)⁻¹ ∈ P) {g : ↥Lstd} (hg : f g ∈ P) : g = 1 := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (Equiv.Perm (Fin 365211)),
      N = (P.comap f).map Lstd.subtype := ⟨_, rfl⟩
  have hmemN : ∀ n : Equiv.Perm (Fin 365211), n ∈ N ↔ ∃ n₀ : ↥Lstd, f n₀ ∈ P ∧ (n₀ : _) = n := by
    intro n
    rw [hN, Subgroup.mem_map]
    constructor
    · rintro ⟨n₀, hn₀, rfl⟩
      exact ⟨n₀, hn₀, rfl⟩
    · rintro ⟨n₀, hn₀, rfl⟩
      exact ⟨n₀, hn₀, rfl⟩
  have hNL : N ≤ Lstd := by
    rw [hN]
    exact Subgroup.map_subtype_le _
  have hN2 : IsPGroup 2 N := by
    rw [hN]
    exact (hP2.comap_of_injective f hf).map _
  have hnormN : ∀ l ∈ Lstd, ∀ n ∈ N, l * n * l⁻¹ ∈ N := by
    intro l hl n hn
    obtain ⟨n₀, hn₀, rfl⟩ := (hmemN n).mp hn
    refine (hmemN _).mpr ⟨⟨l, hl⟩ * n₀ * ⟨l, hl⟩⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hnorm ⟨l, hl⟩ _ hn₀
  have hfix := fixes_X_of_normal hNL hN2 hnormN
  have hgN : (g : Equiv.Perm (Fin 365211)) ∈ N := (hmemN _).mpr ⟨g, hg, rfl⟩
  have h1 : (g : Equiv.Perm (Fin 365211)) = 1 := by
    refine eq_one_of_fixes_F0 (Lstd_le_TD6 g.2) fun p hp => ?_
    simp only [CFSG.SmithD6.ea7InF0, Bool.or_eq_true, beq_iff_eq] at hp
    rcases hp with (h0 | h1) | hX
    · have : p = 0 := Fin.ext (by rw [h0, fin_val_zero])
      rw [this]
      exact (Lstd_fix g.2).1
    · have : p = stdOpp := Fin.ext (by rw [h1, stdOpp_val])
      rw [this]
      exact (Lstd_fix g.2).2
    · exact hfix p hX g hgN
  exact Subtype.ext h1

end Odd

end CFSG.GF2Type.SmithTypeE.E7
