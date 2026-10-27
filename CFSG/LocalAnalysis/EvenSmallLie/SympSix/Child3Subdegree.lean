module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Orbits
public import CFSG.GroupTheory.TransitiveDegree36Subdegrees

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module Matrix MulAction CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (hinf : L ⊓ zpowers z = ⊥)

theorem conjClass_subset_radSub : conjClass (radN φ e z) z ⊆ (radSub φ z e : Set G) := by
  rintro _ ⟨n, hn, rfl⟩
  exact conj_mem_radSub φ hn (mem_sup_right (mem_zpowers z))

theorem exists_lab_of_mem {y : G} (hy : y ∈ conjClass (radN φ e z) z) :
    ∃ x ∈ labSet φ he hzC hz (conjClass (radN φ e z) z),
      radHom φ he hzC hz (Multiplicative.ofAdd x) = y := by
  obtain ⟨m, hm⟩ := (range_radHom φ he hzC hz).symm ▸ conjClass_subset_radSub φ hy
  refine ⟨Multiplicative.toAdd m, ?_, hm⟩
  change radHom φ he hzC hz m ∈ conjClass (radN φ e z) z
  rw [hm]
  exact hy

theorem card_kindOf_eq (j : Fin 5) :
    Nat.card {B : 𝕍 // kindOf B = ![1, 2, 3, 4, 4] j} = pieceCard j := by
  rw [← card_pieceP j]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun B => ?_)
  fin_cases j
  · exact kindOf_eq_one_iff B
  · exact kindOf_eq_two_iff B
  · exact kindOf_eq_three_iff B
  · exact kindOf_eq_four_iff B
  · exact kindOf_eq_four_iff B

theorem exists_kindOf (j : Fin 5) : ∃ B : 𝕍, kindOf B = ![1, 2, 3, 4, 4] j := by
  have h := card_kindOf_eq j
  have hpos : 0 < Nat.card {B : 𝕍 // kindOf B = ![1, 2, 3, 4, 4] j} := by
    rw [h]
    fin_cases j <;> decide
  obtain ⟨⟨B, hB⟩⟩ := Nat.card_pos_iff.1 hpos |>.1
  exact ⟨B, hB⟩

section Subdegree

variable (σ : ↥((radN φ e z) ⊓ centralizer ({z} : Set G)) →* GL (Fin 3) (ZMod 2))
  (hσs : Function.Surjective σ)
  (hσ : ∀ (n : ↥((radN φ e z) ⊓ centralizer ({z} : Set G))) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B → LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)

abbrev permK (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G) :
    Subgroup (Equiv.Perm (conjClass (radN φ e z) z)) :=
  (toPermHom (radN φ e z) (conjClass (radN φ e z) z)).range

instance : IsPretransitive (permK φ e z) (conjClass (radN φ e z) z) :=
  ⟨fun x y => by
    obtain ⟨n, hn⟩ := exists_smul_eq (radN φ e z) x y
    exact ⟨⟨toPermHom (radN φ e z) (conjClass (radN φ e z) z) n, n, rfl⟩, hn⟩⟩

abbrev zPt (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G) : conjClass (radN φ e z) z :=
  ⟨z, self_mem_conjClass _ z⟩

include hσs hσ in
theorem orbit_stabilizer_eq (y : conjClass (radN φ e z) z) (B₀ : 𝕍) (ε₀ : ZMod 2)
    (hy : (y : G) = radHom φ he hzC hz (Multiplicative.ofAdd (B₀, ε₀))) :
    orbit (stabilizer (permK φ e z) (zPt φ e z)) y =
      {y' : conjClass (radN φ e z) z | ∃ B : 𝕍, kindOf B = kindOf B₀ ∧
        (y' : G) = radHom φ he hzC hz (Multiplicative.ofAdd (B, ε₀))} := by
  have hconj := conj_radHom_of_sigma φ he hzC hz (N₀ := (radN φ e z) ⊓ centralizer ({z} : Set G))
    inf_le_right σ hσ
  ext y'
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨⟨⟨k, ⟨n, rfl⟩⟩, hk⟩, rfl⟩
    have hnz : (n : G) * z * (n : G)⁻¹ = z := by
      have := congrArg Subtype.val (mem_stabilizer_iff.1 hk)
      exact this
    have hnC : (n : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * n := by group
        _ = z * n := by rw [hnz]
    refine ⟨symThreeCongr (σ ⟨n, n.2, hnC⟩) B₀, kindOf_symThreeCongr _ _, ?_⟩
    change (n : G) * y * (n : G)⁻¹ = _
    rw [hy]
    exact hconj ⟨n, n.2, hnC⟩ B₀ ε₀
  · rintro ⟨B, hB, hy'⟩
    obtain ⟨D, hD⟩ := exists_symThreeCongr_of_kindOf_eq hB.symm
    obtain ⟨n, hn⟩ := hσs D
    let nN : radN φ e z := ⟨n, (mem_inf.1 n.2).1⟩
    have hnz : (n : G) * z * (n : G)⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2, mul_inv_cancel_right]
    refine ⟨⟨⟨toPermHom (radN φ e z) (conjClass (radN φ e z) z) nN, nN, rfl⟩,
      mem_stabilizer_iff.2 (Subtype.ext hnz)⟩, Subtype.ext ?_⟩
    change (n : G) * y * (n : G)⁻¹ = y'
    rw [hy, hy', hconj n B₀ ε₀, hn, hD]

include hinf hσs hσ in
theorem labSet_conjClass_ne_subdegree [Finite G] {j : Fin 5} (hj : j = 0 ∨ j = 1) :
    labSet φ he hzC hz (conjClass (radN φ e z) z) ≠ patternSet {j, 3} := by
  intro hΛ
  classical
  have hlab : ∀ y : conjClass (radN φ e z) z, ∃ B₀ : 𝕍, ∃ ε₀ : ZMod 2,
      (y : G) = radHom φ he hzC hz (Multiplicative.ofAdd (B₀, ε₀)) ∧
        ((kindOf B₀ = 0 ∧ ε₀ = 1) ∨ (kindOf B₀ = ![1, 2, 3, 4, 4] j ∧ ε₀ = 1) ∨
          (kindOf B₀ = 4 ∧ ε₀ = 1)) := by
    intro y
    obtain ⟨⟨B₀, ε₀⟩, hx, hxy⟩ := exists_lab_of_mem φ he hzC hz y.2
    rw [hΛ, mem_patternSet_iff] at hx
    refine ⟨B₀, ε₀, hxy.symm, ?_⟩
    rcases hx with h | ⟨i, hi, h1, h2⟩
    · exact Or.inl h
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine Or.inr (Or.inl ⟨h2, ?_⟩)
        rcases hj with rfl | rfl <;> exact h1
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
  have hmem : ∀ B₀ : 𝕍, (kindOf B₀ = 0 ∨ kindOf B₀ = ![1, 2, 3, 4, 4] j ∨ kindOf B₀ = 4) →
      radHom φ he hzC hz (Multiplicative.ofAdd (B₀, 1)) ∈ conjClass (radN φ e z) z := by
    intro B₀ hk
    have : (B₀, (1 : ZMod 2)) ∈ labSet φ he hzC hz (conjClass (radN φ e z) z) := by
      rw [hΛ, mem_patternSet_iff]
      rcases hk with hk | hk | hk
      · exact Or.inl ⟨hk, rfl⟩
      · refine Or.inr ⟨j, Finset.mem_insert_self _ _, ?_, hk⟩
        rcases hj with rfl | rfl <;> rfl
      · exact Or.inr ⟨3, by simp, rfl, hk⟩
    exact this
  let Ok : Fin 5 → Set (conjClass (radN φ e z) z) := fun k =>
    {y' | ∃ B : 𝕍, kindOf B = k ∧
      (y' : G) = radHom φ he hzC hz (Multiplicative.ofAdd (B, 1))}
  have horb : ∀ y : conjClass (radN φ e z) z,
      orbit (stabilizer (permK φ e z) (zPt φ e z)) y = Ok 0 ∨
        orbit (stabilizer (permK φ e z) (zPt φ e z)) y = Ok (![1, 2, 3, 4, 4] j) ∨
        orbit (stabilizer (permK φ e z) (zPt φ e z)) y = Ok 4 := by
    intro y
    obtain ⟨B₀, ε₀, hy, hk⟩ := hlab y
    rw [orbit_stabilizer_eq φ he hzC hz σ hσs hσ y B₀ ε₀ hy]
    rcases hk with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩
    · exact Or.inl (by rw [hk])
    · exact Or.inr (Or.inl (by rw [hk]))
    · exact Or.inr (Or.inr (by rw [hk]))
  have horb' : ∀ k : Fin 5, (k = 0 ∨ k = ![1, 2, 3, 4, 4] j ∨ k = 4) →
      ∃ y : conjClass (radN φ e z) z, orbit (stabilizer (permK φ e z) (zPt φ e z)) y = Ok k := by
    intro k hk
    obtain ⟨B₀, hB₀⟩ : ∃ B₀ : 𝕍, kindOf B₀ = k := by
      rcases hk with rfl | rfl | rfl
      · exact ⟨0, (kindOf_eq_zero_iff 0).2 rfl⟩
      · exact exists_kindOf j
      · exact exists_kindOf 3
    refine ⟨⟨_, hmem B₀ (hB₀ ▸ hk)⟩, ?_⟩
    rw [orbit_stabilizer_eq φ he hzC hz σ hσs hσ _ B₀ 1 rfl, hB₀]
  have hO0 : Ok 0 = {zPt φ e z} := by
    ext y'
    simp only [Ok, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨B, hB, hy'⟩
      rw [(kindOf_eq_zero_iff B).1 hB] at hy'
      exact Subtype.ext (hy'.trans (radHom_z φ he hzC hz))
    · rintro rfl
      exact ⟨0, (kindOf_eq_zero_iff 0).2 rfl, (radHom_z φ he hzC hz).symm⟩
  have hcardO : ∀ k : Fin 5, (k = ![1, 2, 3, 4, 4] j ∨ k = 4) →
      (Ok k).ncard = Nat.card {B : 𝕍 // kindOf B = k} := by
    intro k hk
    have hk' : k = 0 ∨ k = ![1, 2, 3, 4, 4] j ∨ k = 4 := Or.inr hk
    rw [← Nat.card_coe_set_eq]
    refine (Nat.card_congr
      { toFun := fun B => ⟨⟨_, hmem B.1 (by rw [B.2]; exact hk')⟩, B.1, B.2, rfl⟩
        invFun := fun y => ⟨Classical.choose y.2, (Classical.choose_spec y.2).1⟩
        left_inv := fun B => ?_
        right_inv := fun y => ?_ }).symm
    · apply Subtype.ext
      have h := (Classical.choose_spec
        (show ∃ B' : 𝕍, kindOf B' = k ∧ radHom φ he hzC hz (Multiplicative.ofAdd (B.1, 1)) =
          radHom φ he hzC hz (Multiplicative.ofAdd (B', 1)) from ⟨B.1, B.2, rfl⟩)).2
      exact (Prod.mk.inj (lab_ext φ he hzC hz hinf h)).1.symm
    · apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec y.2).2.symm
  have hcard : Nat.card (conjClass (radN φ e z) z) = 36 := by
    rw [← card_labSet φ he hzC hz (conjClass_subset_radSub φ) hinf, hΛ, card_patternSet]
    rcases hj with rfl | rfl <;> rfl
  have hj' : ![1, 2, 3, 4, 4] j = (1 : Fin 5) ∨ ![1, 2, 3, 4, 4] j = (2 : Fin 5) := by
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  apply CFSG.GroupTheory.TransitiveDegree36.transitive_degree36_subdegrees_obstruction hcard
    (permK φ e z) (zPt φ e z) (Ok (![1, 2, 3, 4, 4] j)) (Ok 4)
  · rw [hcardO _ (Or.inl rfl)]
    rcases hj with rfl | rfl
    · exact card_kindOf_eq 0
    · exact card_kindOf_eq 1
  · rw [hcardO _ (Or.inr rfl)]
    exact card_kindOf_eq 3
  · ext O
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl⟩
      rcases horb y with h | h | h
      · exact Or.inl (h.trans hO0)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl)
      · obtain ⟨y, hy⟩ := horb' 0 (Or.inl rfl)
        exact ⟨y, hy.trans hO0⟩
      · exact horb' _ (Or.inr (Or.inl rfl))
      · exact horb' 4 (Or.inr (Or.inr rfl))

end Subdegree

end CFSG.EvenSmallLie.Child3
