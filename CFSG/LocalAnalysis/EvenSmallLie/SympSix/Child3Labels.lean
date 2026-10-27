module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixRadicalLabels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCongruenceOrbits
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetMiddleSubgroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Labels

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (hinf : L ⊓ zpowers z = ⊥)

theorem tauSet_subset (P : M₃ → Prop) : tauSet φ e P ⊆ (L : Set G) := by
  rintro a ⟨ha, -⟩
  exact ha

include hz hinf in
theorem not_mem_L : z ∉ L := by
  intro hzL
  have h1 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨hzL, mem_zpowers z⟩
  rw [hinf, mem_bot] at h1
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem mem_tauSet_tauHom_iff (P : M₃ → Prop) (B : 𝕍) :
    tauHom φ he (Multiplicative.ofAdd B) ∈ tauSet φ e P ↔ P (B : M₃) := by
  rw [mem_tauSet_iff φ he]
  constructor
  · rintro ⟨B', hP, hB'⟩
    rw [tauHom_injective φ he hB'] at hP
    exact hP
  · intro hP
    exact ⟨Multiplicative.ofAdd B, hP, rfl⟩

theorem zmod_two_cases (ε : ZMod 2) : ε = 0 ∨ ε = 1 := by
  fin_cases ε
  · exact Or.inl rfl
  · exact Or.inr rfl

include hinf in
theorem radHom_mem_smul_tauSet (P : M₃ → Prop) (x : 𝕍 × ZMod 2) :
    radHom φ he hzC hz (Multiplicative.ofAdd x) ∈ z • tauSet φ e P ↔ x.2 = 1 ∧ P (x.1 : M₃) := by
  obtain ⟨B, ε⟩ := x
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, radHom_apply]
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zPow_zero, mul_one]
    simp only [zero_ne_one, false_and, iff_false]
    intro h
    have h1 := tauSet_subset φ P h
    have h2 : z⁻¹ ∈ L := by
      have := L.mul_mem h1 (L.inv_mem (tauHom_mem φ he (Multiplicative.ofAdd B)))
      rwa [mul_inv_cancel_right] at this
    exact not_mem_L hz hinf (by simpa using L.inv_mem h2)
  · rw [zPow_one, mul_comm_z hzC (tauHom_mem φ he _), inv_mul_cancel_left]
    simp only [true_and]
    exact mem_tauSet_tauHom_iff φ he P B

include hinf in
theorem radHom_mem_tauSet (P : M₃ → Prop) (x : 𝕍 × ZMod 2) :
    radHom φ he hzC hz (Multiplicative.ofAdd x) ∈ tauSet φ e P ↔ x.2 = 0 ∧ P (x.1 : M₃) := by
  obtain ⟨B, ε⟩ := x
  rw [radHom_apply]
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zPow_zero, mul_one]
    simp only [true_and]
    exact mem_tauSet_tauHom_iff φ he P B
  · rw [zPow_one]
    simp only [one_ne_zero, false_and, iff_false]
    intro h
    have h1 := tauSet_subset φ P h
    have h2 := L.mul_mem (L.inv_mem (tauHom_mem φ he (Multiplicative.ofAdd B))) h1
    rw [inv_mul_cancel_left] at h2
    exact not_mem_L hz hinf h2

include hinf in
theorem radHom_eq_z_iff (x : 𝕍 × ZMod 2) :
    radHom φ he hzC hz (Multiplicative.ofAdd x) = z ↔ x = (0, 1) := by
  have hz0 := radHom_z φ he hzC hz
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf (h.trans hz0.symm))
  · rintro rfl
    exact hz0

include he in
theorem smul_tauSet_subset_radSub (P : M₃ → Prop) :
    z • tauSet φ e P ⊆ (radSub φ z e : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨B, -, rfl⟩ := (mem_tauSet_iff φ he).1 ha
  exact mul_mem (mem_sup_right (mem_zpowers z))
    (mem_sup_left ((mem_pullSub_iff φ he).2 ⟨B, rfl⟩))

end Labels

section Rank

theorem rkBits_values : ∀ x : SixBits,
    rkBits x = 1 ∨ rkBits x = 2 ∨ rkBits x = 4 ∨ rkBits x = 8 := by
  decide +kernel

theorem symDet_eq_one_iff : ∀ x : SixBits, binarySymDetThree (symMat x) = 1 ↔ rkBits x = 8 := by
  decide +kernel

theorem rkBits_one_iff : ∀ x : SixBits, rkBits x = 1 ↔ x = (0, 0, 0, 0, 0, 0) := by
  decide +kernel

theorem altBits_ne_zero_iff : ∀ x : SixBits,
    (x ≠ (0, 0, 0, 0, 0, 0) ∧ altBits x) ↔ (rkBits x = 4 ∧ altBits x) := by
  decide +kernel

theorem symEquiv_eq_zero_iff (B : 𝕍) : symEquiv B = (0, 0, 0, 0, 0, 0) ↔ B = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    rw [← symMat_symEquiv B, h]
    decide
  · rintro rfl
    rfl

theorem rank_cases (B : 𝕍) : (B : M₃).rank = 0 ∨ (B : M₃).rank = 1 ∨ (B : M₃).rank = 2 ∨
    (B : M₃).rank = 3 := by
  rcases rkBits_values (symEquiv B) with h | h | h | h
  · exact Or.inl ((rkBits_symEquiv_eq_iff B 0).1 h)
  · exact Or.inr (Or.inl ((rkBits_symEquiv_eq_iff B 1).1 h))
  · exact Or.inr (Or.inr (Or.inl ((rkBits_symEquiv_eq_iff B 2).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((rkBits_symEquiv_eq_iff B 3).1 h)))

theorem rank_eq_zero_iff (B : 𝕍) : (B : M₃).rank = 0 ↔ B = 0 := by
  rw [← rkBits_symEquiv_eq_iff, pow_zero, rkBits_one_iff, symEquiv_eq_zero_iff]

theorem det_eq_one_iff (B : 𝕍) : (B : M₃).det = 1 ↔ (B : M₃).rank = 3 := by
  rw [det_eq_binarySymDetThree B.2, ← symMat_symEquiv B, symDet_eq_one_iff, symMat_symEquiv,
    ← rkBits_symEquiv_eq_iff]
  rfl

theorem det_eq_zero_iff (B : 𝕍) : (B : M₃).det = 0 ↔ (B : M₃).rank ≠ 3 := by
  rw [Ne, ← det_eq_one_iff]
  rcases zmod_two_cases (B : M₃).det with h | h <;> simp [h]

theorem alt_ne_zero_iff (B : 𝕍) : (B ≠ 0 ∧ ∀ i, (B : M₃) i i = 0) ↔
    ((B : M₃).rank = 2 ∧ ∀ i, (B : M₃) i i = 0) := by
  rw [← altBits_symEquiv_iff, ← rkBits_symEquiv_eq_iff, Ne, ← symEquiv_eq_zero_iff]
  exact altBits_ne_zero_iff (symEquiv B)

end Rank

section Pieces

@[expose] def pieceP : Fin 5 → M₃ → Prop
  | 0 => fun B => B.rank = 1
  | 1 => fun B => B.rank = 2 ∧ ∀ i, B i i = 0
  | 2 => fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0
  | 3 => fun B => B.rank = 3
  | 4 => fun B => B.rank = 3

@[expose] def pieceE : Fin 5 → ZMod 2
  | 4 => 0
  | _ => 1

@[expose] def piece (i : Fin 5) : Set (𝕍 × ZMod 2) := {x | x.2 = pieceE i ∧ pieceP i (x.1 : M₃)}

@[expose] def pieceCard : Fin 5 → ℕ := ![7, 7, 21, 28, 28]

theorem card_pieceP (i : Fin 5) : Nat.card {B : 𝕍 // pieceP i (B : M₃)} = pieceCard i := by
  fin_cases i
  · exact card_sym_rank_one
  · exact card_sym_rank_two_alternating
  · exact card_sym_rank_two_nonalternating
  · exact card_sym_rank_three
  · exact card_sym_rank_three

theorem card_piece (i : Fin 5) : Nat.card (piece i) = pieceCard i := by
  rw [← card_pieceP i]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.2.2⟩
      invFun := fun B => ⟨(B.1, pieceE i), rfl, B.2⟩
      left_inv := fun x => ?_
      right_inv := fun B => rfl }
  obtain ⟨⟨B, ε⟩, hε, hB⟩ := x
  change ε = pieceE i at hε
  subst hε
  rfl

theorem zero_one_not_mem_piece (i : Fin 5) : ((0 : 𝕍), (1 : ZMod 2)) ∉ piece i := by
  rintro ⟨h1, h2⟩
  have h0 : ((0 : 𝕍) : M₃).rank = 0 := (rank_eq_zero_iff 0).2 rfl
  fin_cases i
  · exact absurd (h2.symm.trans h0) (by norm_num)
  · exact absurd (h2.1.symm.trans h0) (by norm_num)
  · exact absurd (h2.1.symm.trans h0) (by norm_num)
  · exact absurd (h2.symm.trans h0) (by norm_num)
  · exact absurd h1 (by decide)

theorem disjoint_piece {i j : Fin 5} (hij : i ≠ j) : Disjoint (piece i) (piece j) := by
  rw [Set.disjoint_left]
  rintro ⟨B, ε⟩ ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  change ε = pieceE i at hi1
  change ε = pieceE j at hj1
  fin_cases i <;> fin_cases j <;> simp_all [pieceP, pieceE]

@[expose] def patternSet (S : Finset (Fin 5)) : Set (𝕍 × ZMod 2) :=
  {((0 : 𝕍), (1 : ZMod 2))} ∪ ⋃ i ∈ S, piece i

theorem patternSet_insert {a : Fin 5} {S : Finset (Fin 5)} :
    patternSet (insert a S) = patternSet S ∪ piece a := by
  ext x
  simp only [patternSet, Finset.mem_insert, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (h | ⟨i, hi | hi, hx⟩)
    · exact Or.inl (Or.inl h)
    · subst hi
      exact Or.inr hx
    · exact Or.inl (Or.inr ⟨i, hi, hx⟩)
  · rintro ((h | ⟨i, hi, hx⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨i, Or.inr hi, hx⟩
    · exact Or.inr ⟨a, Or.inl rfl, h⟩

theorem card_patternSet (S : Finset (Fin 5)) :
    Nat.card (patternSet S) = 1 + ∑ i ∈ S, pieceCard i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [patternSet]
  | insert a S ha ih =>
    have hdisj : Disjoint (patternSet S) (piece a) := by
      rw [Set.disjoint_right]
      intro x hx hxS
      simp only [patternSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion,
        exists_prop] at hxS
      rcases hxS with rfl | ⟨i, hi, hxi⟩
      · exact zero_one_not_mem_piece a hx
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        exact Set.disjoint_left.1 (disjoint_piece hia) hxi hx
    rw [patternSet_insert, Finset.sum_insert ha, Nat.card_coe_set_eq,
      Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, ih, card_piece]
    ring

end Pieces

section Kinds

theorem alt_rank (B : 𝕍) (h : ∀ i, (B : M₃) i i = 0) : (B : M₃).rank = 0 ∨ (B : M₃).rank = 2 := by
  by_cases hB : B = 0
  · exact Or.inl ((rank_eq_zero_iff B).2 hB)
  · exact Or.inr ((alt_ne_zero_iff B).1 ⟨hB, h⟩).1

theorem kind_cases (B : 𝕍) :
    B = 0 ∨ (B : M₃).rank = 1 ∨ ((B : M₃).rank = 2 ∧ ∀ i, (B : M₃) i i = 0) ∨
      ((B : M₃).rank = 2 ∧ ¬ ∀ i, (B : M₃) i i = 0) ∨ (B : M₃).rank = 3 := by
  rcases rank_cases B with h | h | h | h
  · exact Or.inl ((rank_eq_zero_iff B).1 h)
  · exact Or.inr (Or.inl h)
  · by_cases ha : ∀ i, (B : M₃) i i = 0
    · exact Or.inr (Or.inr (Or.inl ⟨h, ha⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem alt_of_eq_zero {B : 𝕍} (h : B = 0) : ∀ i, (B : M₃) i i = 0 := by
  subst h
  intro i
  rfl

theorem mem_binaryAltMatrices_iff (B : 𝕍) :
    (B : M₃) ∈ binaryAltMatrices 3 ↔ ∀ i, (B : M₃) i i = 0 :=
  ⟨fun h => h.2, fun h => ⟨B.2, h⟩⟩

end Kinds

section KindOf

open Classical in
@[expose] noncomputable def kindOf (B : 𝕍) : Fin 5 :=
  if B = 0 then 0 else if (B : M₃).rank = 1 then 1 else
    if (B : M₃).rank = 2 ∧ ∀ i, (B : M₃) i i = 0 then 2 else
      if (B : M₃).rank = 2 then 3 else 4

theorem kindOf_eq_zero_iff (B : 𝕍) : kindOf B = 0 ↔ B = 0 := by
  unfold kindOf
  split_ifs <;> simp_all

theorem kindOf_eq_one_iff (B : 𝕍) : kindOf B = 1 ↔ (B : M₃).rank = 1 := by
  unfold kindOf
  split_ifs with h0 h1 h2 h3 <;> simp_all

theorem kindOf_eq_two_iff (B : 𝕍) :
    kindOf B = 2 ↔ ((B : M₃).rank = 2 ∧ ∀ i, (B : M₃) i i = 0) := by
  unfold kindOf
  split_ifs with h0 h1 h2 h3 <;> simp_all

theorem kindOf_eq_three_iff (B : 𝕍) :
    kindOf B = 3 ↔ ((B : M₃).rank = 2 ∧ ¬ ∀ i, (B : M₃) i i = 0) := by
  unfold kindOf
  split_ifs with h0 h1 h2 h3 <;> simp_all

theorem kindOf_eq_four_iff (B : 𝕍) : kindOf B = 4 ↔ (B : M₃).rank = 3 := by
  unfold kindOf
  split_ifs with h0 h1 h2 h3
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp only [true_iff]
    rcases kind_cases B with h | h | h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h.1 h3
    · exact h

theorem alt_iff_kindOf (B : 𝕍) :
    (∀ i, (B : M₃) i i = 0) ↔ (kindOf B = 0 ∨ kindOf B = 2) := by
  rw [kindOf_eq_zero_iff, kindOf_eq_two_iff]
  constructor
  · intro h
    rcases alt_rank B h with h' | h'
    · exact Or.inl ((rank_eq_zero_iff B).1 h')
    · exact Or.inr ⟨h', h⟩
  · rintro (h | h)
    · exact alt_of_eq_zero h
    · exact h.2

theorem det_eq_one_iff_kindOf (B : 𝕍) : (B : M₃).det = 1 ↔ kindOf B = 4 := by
  rw [det_eq_one_iff, kindOf_eq_four_iff]

theorem det_eq_zero_iff_kindOf (B : 𝕍) : (B : M₃).det = 0 ↔ kindOf B ≠ 4 := by
  rw [det_eq_zero_iff, Ne, Ne, kindOf_eq_four_iff]

theorem mem_piece_iff (i : Fin 5) (x : 𝕍 × ZMod 2) :
    x ∈ piece i ↔ x.2 = pieceE i ∧ kindOf x.1 = ![1, 2, 3, 4, 4] i := by
  obtain ⟨B, ε⟩ := x
  fin_cases i
  · exact and_congr Iff.rfl (kindOf_eq_one_iff B).symm
  · exact and_congr Iff.rfl (kindOf_eq_two_iff B).symm
  · exact and_congr Iff.rfl (kindOf_eq_three_iff B).symm
  · exact and_congr Iff.rfl (kindOf_eq_four_iff B).symm
  · exact and_congr Iff.rfl (kindOf_eq_four_iff B).symm

theorem mem_patternSet_iff (S : Finset (Fin 5)) (x : 𝕍 × ZMod 2) :
    x ∈ patternSet S ↔ (kindOf x.1 = 0 ∧ x.2 = 1) ∨
      ∃ i ∈ S, x.2 = pieceE i ∧ kindOf x.1 = ![1, 2, 3, 4, 4] i := by
  obtain ⟨B, ε⟩ := x
  simp only [patternSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop,
    mem_piece_iff, Prod.mk.injEq, kindOf_eq_zero_iff]

end KindOf

section Congruence

theorem kindOf_symThreeCongr (D : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    kindOf (symThreeCongr D B) = kindOf B := by
  obtain ⟨hr, ha⟩ := (sym_congruent_iff B (symThreeCongr D B)).1 ⟨D, rfl⟩
  rcases kind_cases B with h | h | h | h | h
  · rw [(kindOf_eq_zero_iff B).2 h, kindOf_eq_zero_iff, ← rank_eq_zero_iff, ← hr,
      rank_eq_zero_iff]
    exact h
  · rw [(kindOf_eq_one_iff B).2 h, kindOf_eq_one_iff, ← hr]
    exact h
  · rw [(kindOf_eq_two_iff B).2 h, kindOf_eq_two_iff, ← hr, ← ha h.1]
    exact h
  · rw [(kindOf_eq_three_iff B).2 h, kindOf_eq_three_iff, ← hr, ← ha h.1]
    exact h
  · rw [(kindOf_eq_four_iff B).2 h, kindOf_eq_four_iff, ← hr]
    exact h

theorem exists_symThreeCongr_of_kindOf_eq {B B' : 𝕍} (h : kindOf B = kindOf B') :
    ∃ D : GL (Fin 3) (ZMod 2), symThreeCongr D B = B' := by
  obtain ⟨D, hD⟩ := (sym_congruent_iff B B').2 (by
    rcases kind_cases B with hB | hB | hB | hB | hB
    · have hB' : B' = 0 := (kindOf_eq_zero_iff B').1 (h ▸ (kindOf_eq_zero_iff B).2 hB)
      subst hB hB'
      exact ⟨rfl, fun h2 => Iff.rfl⟩
    · have hB' := (kindOf_eq_one_iff B').1 (h ▸ (kindOf_eq_one_iff B).2 hB)
      exact ⟨hB.trans hB'.symm, fun h2 => by omega⟩
    · have hB' := (kindOf_eq_two_iff B').1 (h ▸ (kindOf_eq_two_iff B).2 hB)
      exact ⟨hB.1.trans hB'.1.symm, fun _ => ⟨fun _ => hB'.2, fun _ => hB.2⟩⟩
    · have hB' := (kindOf_eq_three_iff B').1 (h ▸ (kindOf_eq_three_iff B).2 hB)
      exact ⟨hB.1.trans hB'.1.symm, fun _ => ⟨fun h' => absurd h' hB.2,
        fun h' => absurd h' hB'.2⟩⟩
    · have hB' := (kindOf_eq_four_iff B').1 (h ▸ (kindOf_eq_four_iff B).2 hB)
      exact ⟨hB.trans hB'.symm, fun h2 => by omega⟩)
  exact ⟨D, Subtype.ext hD⟩

end Congruence

end CFSG.EvenSmallLie.Child3
