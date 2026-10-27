module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Labels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits

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

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (hinf : L ⊓ zpowers z = ⊥)

@[expose] def labSet (Ω : Set G) : Set (𝕍 × ZMod 2) :=
  {x | radHom φ he hzC hz (Multiplicative.ofAdd x) ∈ Ω}

include hinf in
theorem labSet_singleton_z : labSet φ he hzC hz {z} = {((0 : 𝕍), (1 : ZMod 2))} := by
  ext x
  exact radHom_eq_z_iff φ he hzC hz hinf x

include hinf in
theorem labSet_smul_tauSet (P : M₃ → Prop) :
    labSet φ he hzC hz (z • tauSet φ e P) = {x | x.2 = 1 ∧ P (x.1 : M₃)} := by
  ext x
  exact radHom_mem_smul_tauSet φ he hzC hz hinf P x

include hinf in
theorem labSet_tauSet (P : M₃ → Prop) :
    labSet φ he hzC hz (tauSet φ e P) = {x | x.2 = 0 ∧ P (x.1 : M₃)} := by
  ext x
  exact radHom_mem_tauSet φ he hzC hz hinf P x

theorem labSet_union (Ω Ω' : Set G) :
    labSet φ he hzC hz (Ω ∪ Ω') = labSet φ he hzC hz Ω ∪ labSet φ he hzC hz Ω' :=
  rfl

theorem eq_of_labSet_eq {Ω Ω' : Set G} (hΩ : Ω ⊆ (radSub φ z e : Set G))
    (hΩ' : Ω' ⊆ (radSub φ z e : Set G))
    (h : labSet φ he hzC hz Ω = labSet φ he hzC hz Ω') : Ω = Ω' := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := (range_radHom φ he hzC hz).symm ▸ hΩ hg
    have h1 : Multiplicative.toAdd x ∈ labSet φ he hzC hz Ω := by
      change radHom φ he hzC hz x ∈ Ω
      rw [hx]
      exact hg
    rw [h] at h1
    change radHom φ he hzC hz x ∈ Ω' at h1
    rwa [hx] at h1
  · intro hg
    obtain ⟨x, hx⟩ := (range_radHom φ he hzC hz).symm ▸ hΩ' hg
    have h1 : Multiplicative.toAdd x ∈ labSet φ he hzC hz Ω' := by
      change radHom φ he hzC hz x ∈ Ω'
      rw [hx]
      exact hg
    rw [← h] at h1
    change radHom φ he hzC hz x ∈ Ω at h1
    rwa [hx] at h1

abbrev radN (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G) : Subgroup G :=
  normalizer (radSub φ z e : Set G)

theorem conj_mem_radSub {n : G} (hn : n ∈ radN φ e z) {x : G} (hx : x ∈ radSub φ z e) :
    n * x * n⁻¹ ∈ radSub φ z e :=
  (mem_normalizer_iff.1 hn x).1 hx

@[expose] def conjLab (n : radN φ e z) (x : 𝕍 × ZMod 2) : 𝕍 × ZMod 2 :=
  Multiplicative.toAdd (radLabel φ he hzC hz hinf
    ⟨(n : G) * radHom φ he hzC hz (Multiplicative.ofAdd x) * (n : G)⁻¹,
      conj_mem_radSub φ n.2 (by
        rw [← range_radHom φ he hzC hz]
        exact ⟨_, rfl⟩)⟩)

theorem radHom_conjLab (n : radN φ e z) (x : 𝕍 × ZMod 2) :
    radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf n x)) =
      (n : G) * radHom φ he hzC hz (Multiplicative.ofAdd x) * (n : G)⁻¹ := by
  rw [conjLab, ofAdd_toAdd, ← coe_radLabel_symm φ he hzC hz hinf, MulEquiv.symm_apply_apply]

include hinf in
theorem lab_ext {x y : 𝕍 × ZMod 2}
    (h : radHom φ he hzC hz (Multiplicative.ofAdd x) =
      radHom φ he hzC hz (Multiplicative.ofAdd y)) : x = y :=
  Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf h)

@[expose, instance_reducible] def conjLabAction : DistribMulAction (radN φ e z) (𝕍 × ZMod 2) where
  smul n x := conjLab φ he hzC hz hinf n x
  one_smul x := lab_ext φ he hzC hz hinf (by
    change radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf 1 x)) = _
    rw [radHom_conjLab]
    simp)
  mul_smul m n x := lab_ext φ he hzC hz hinf (by
    change radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf (m * n) x)) =
      radHom φ he hzC hz (Multiplicative.ofAdd
        (conjLab φ he hzC hz hinf m (conjLab φ he hzC hz hinf n x)))
    rw [radHom_conjLab, radHom_conjLab, radHom_conjLab, coe_mul]
    group)
  smul_zero n := lab_ext φ he hzC hz hinf (by
    change radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf n 0)) = _
    rw [radHom_conjLab, ofAdd_zero, map_one]
    group)
  smul_add n x y := lab_ext φ he hzC hz hinf (by
    change radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf n (x + y))) =
      radHom φ he hzC hz (Multiplicative.ofAdd
        (conjLab φ he hzC hz hinf n x + conjLab φ he hzC hz hinf n y))
    rw [ofAdd_add, map_mul, radHom_conjLab, ofAdd_add, map_mul, radHom_conjLab, radHom_conjLab]
    group)

theorem labSet_conjClass_image (n : radN φ e z) :
    (fun x => conjLab φ he hzC hz hinf n x) ''
        labSet φ he hzC hz (conjClass (radN φ e z) z) =
      labSet φ he hzC hz (conjClass (radN φ e z) z) := by
  have key : ∀ (m : radN φ e z) (x : 𝕍 × ZMod 2),
      x ∈ labSet φ he hzC hz (conjClass (radN φ e z) z) →
        conjLab φ he hzC hz hinf m x ∈ labSet φ he hzC hz (conjClass (radN φ e z) z) := by
    intro m x hx
    change radHom φ he hzC hz (Multiplicative.ofAdd (conjLab φ he hzC hz hinf m x)) ∈
      conjClass (radN φ e z) z
    rw [radHom_conjLab]
    exact conj_mem_conjClass m.2 hx
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact key n x hx
  · intro hy
    refine ⟨conjLab φ he hzC hz hinf n⁻¹ y, key n⁻¹ y hy, lab_ext φ he hzC hz hinf ?_⟩
    rw [radHom_conjLab, radHom_conjLab, coe_inv]
    group

theorem labSet_conjClass_transitive {p q : 𝕍 × ZMod 2}
    (hp : p ∈ labSet φ he hzC hz (conjClass (radN φ e z) z))
    (hq : q ∈ labSet φ he hzC hz (conjClass (radN φ e z) z)) :
    ∃ n : radN φ e z, conjLab φ he hzC hz hinf n p = q := by
  obtain ⟨m₁, hm₁, h₁⟩ := hp
  obtain ⟨m₂, hm₂, h₂⟩ := hq
  refine ⟨⟨m₂ * m₁⁻¹, (radN φ e z).mul_mem hm₂ ((radN φ e z).inv_mem hm₁)⟩,
    lab_ext φ he hzC hz hinf ?_⟩
  rw [radHom_conjLab, ← h₁, ← h₂]
  group

include hinf in
theorem labSet_conjClass_ne_of_obstruction {Λ : Set (𝕍 × ZMod 2)}
    (hobs : ∀ (H : Type) [Group H] [DistribMulAction H (𝕍 × ZMod 2)],
      (∀ g : H, (fun x => g • x) '' Λ = Λ) → ¬ ∀ p ∈ Λ, ∀ q ∈ Λ, ∃ g : H, g • p = q) :
    labSet φ he hzC hz (conjClass (radN φ e z) z) ≠ Λ := by
  intro hΛ
  let _ := conjLabAction φ he hzC hz hinf
  refine hobs (radN φ e z) (fun g => ?_) (fun p hp q hq => ?_)
  · rw [← hΛ]
    exact labSet_conjClass_image φ he hzC hz hinf g
  · rw [← hΛ] at hp hq
    exact labSet_conjClass_transitive φ he hzC hz hinf hp hq

@[expose] def pieceG (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G) : Fin 5 → Set G
  | 4 => tauSet φ e (pieceP 4)
  | i => z • tauSet φ e (pieceP i)

include hinf in
theorem labSet_pieceG (i : Fin 5) : labSet φ he hzC hz (pieceG φ e z i) = piece i := by
  fin_cases i
  · exact labSet_smul_tauSet φ he hzC hz hinf (pieceP 0)
  · exact labSet_smul_tauSet φ he hzC hz hinf (pieceP 1)
  · exact labSet_smul_tauSet φ he hzC hz hinf (pieceP 2)
  · exact labSet_smul_tauSet φ he hzC hz hinf (pieceP 3)
  · exact labSet_tauSet φ he hzC hz hinf (pieceP 4)

theorem labSet_mono {Ω Ω' : Set G} (h : Ω ⊆ Ω') :
    labSet φ he hzC hz Ω ⊆ labSet φ he hzC hz Ω' :=
  fun _ hx => h hx

theorem labSet_disjoint {Ω Ω' : Set G} (h : Disjoint Ω Ω') :
    Disjoint (labSet φ he hzC hz Ω) (labSet φ he hzC hz Ω') :=
  Set.disjoint_left.2 fun _ hx hx' => Set.disjoint_left.1 h hx hx'

include hinf in
open Classical in
theorem labSet_eq_patternSet {Ω : Set G} {A : Set G}
    (hpat : FusionOrbitPattern Ω z A (tauSet φ e (pieceP 0)) (tauSet φ e (pieceP 1))
      (tauSet φ e (pieceP 2)) (tauSet φ e (pieceP 3))) :
    labSet φ he hzC hz Ω = patternSet (Finset.univ.filter fun i =>
      piece i ⊆ labSet φ he hzC hz Ω) := by
  classical
  obtain ⟨hzΩ, hsub, h1, h2, h3, h4, h5, -⟩ := hpat
  have hdich : ∀ i : Fin 5, piece i ⊆ labSet φ he hzC hz Ω ∨
      Disjoint (piece i) (labSet φ he hzC hz Ω) := by
    intro i
    rw [← labSet_pieceG φ he hzC hz hinf i]
    fin_cases i
    · exact h1.imp (labSet_mono φ he hzC hz) (labSet_disjoint φ he hzC hz)
    · exact h2.imp (labSet_mono φ he hzC hz) (labSet_disjoint φ he hzC hz)
    · exact h3.imp (labSet_mono φ he hzC hz) (labSet_disjoint φ he hzC hz)
    · exact h4.imp (labSet_mono φ he hzC hz) (labSet_disjoint φ he hzC hz)
    · exact h5.imp (labSet_mono φ he hzC hz) (labSet_disjoint φ he hzC hz)
  have hcover : labSet φ he hzC hz Ω ⊆ {((0 : 𝕍), (1 : ZMod 2))} ∪ ⋃ i, piece i := by
    intro x hx
    have hx' := labSet_mono φ he hzC hz hsub hx
    simp only [labSet_union] at hx'
    rw [labSet_singleton_z φ he hzC hz hinf] at hx'
    have hp : ∀ i : Fin 5, x ∈ labSet φ he hzC hz (pieceG φ e z i) →
        x ∈ {((0 : 𝕍), (1 : ZMod 2))} ∪ ⋃ i, piece i := fun i h =>
      Or.inr (Set.mem_iUnion.2 ⟨i, by rw [← labSet_pieceG φ he hzC hz hinf i]; exact h⟩)
    rcases hx' with ((((h | h) | h) | h) | h) | h
    · exact Or.inl h
    · exact hp 0 h
    · exact hp 1 h
    · exact hp 2 h
    · exact hp 3 h
    · exact hp 4 h
  ext x
  simp only [patternSet, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    rcases hcover hx with h | h
    · exact Or.inl h
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h
      rcases hdich i with hsub' | hdis
      · exact Or.inr ⟨i, hsub', hi⟩
      · exact absurd hx (Set.disjoint_left.1 hdis hi)
  · rintro (rfl | ⟨i, hsub', hi⟩)
    · change radHom φ he hzC hz (Multiplicative.ofAdd ((0 : 𝕍), (1 : ZMod 2))) ∈ Ω
      rw [radHom_z]
      exact hzΩ
    · exact hsub' hi

theorem card_labSet {Ω : Set G} (hΩ : Ω ⊆ (radSub φ z e : Set G)) (hinf : L ⊓ zpowers z = ⊥) :
    Nat.card (labSet φ he hzC hz Ω) = Nat.card Ω := by
  have himg : (fun x => radHom φ he hzC hz (Multiplicative.ofAdd x)) ''
      labSet φ he hzC hz Ω = Ω := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      obtain ⟨x, hx⟩ := (range_radHom φ he hzC hz).symm ▸ hΩ hg
      exact ⟨Multiplicative.toAdd x, by
        change radHom φ he hzC hz x ∈ Ω
        rw [hx]
        exact hg, hx⟩
  have hinj : Function.Injective fun x : 𝕍 × ZMod 2 =>
      radHom φ he hzC hz (Multiplicative.ofAdd x) :=
    (radHom_injective φ he hzC hz hinf).comp Multiplicative.ofAdd.injective
  rw [← Nat.card_image_of_injective hinj, himg]

theorem patternSet_cases : ∀ S : Finset (Fin 5),
    (1 + ∑ i ∈ S, pieceCard i = 8 ∨ 1 + ∑ i ∈ S, pieceCard i = 15 ∨
      1 + ∑ i ∈ S, pieceCard i = 36 ∨ 1 + ∑ i ∈ S, pieceCard i = 64) →
    S = {0} ∨ S = {1} ∨ S = {0, 1} ∨ S = {0, 3} ∨ S = {1, 3} ∨ S = {0, 4} ∨ S = {1, 4} ∨
      S = {0, 1, 2} ∨ S = {0, 1, 2, 3} ∨ S = {0, 3, 4} ∨ S = {1, 3, 4} ∨ S = {0, 1, 2, 4} := by
  decide

end CFSG.EvenSmallLie.Child3
