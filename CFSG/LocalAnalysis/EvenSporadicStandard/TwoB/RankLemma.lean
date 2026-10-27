module

public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.TwoB

namespace RankLemma

universe u

theorem finite_hom (X : Type*) [Group X] [Finite X] : Finite (X →* Multiplicative (ZMod 2)) :=
  Finite.of_injective _ DFunLike.coe_injective

private theorem two_mul_card_ker_le {X : Type u} [Group X] [Finite X]
    {φ : X →* Multiplicative (ZMod 2)} {x₀ : X} (hx₀ : φ x₀ ≠ 1) :
    2 * Nat.card φ.ker ≤ Nat.card X := by
  have hxM : x₀ ∉ φ.ker := fun h => hx₀ (MonoidHom.mem_ker.1 h)
  have hindex : 2 ≤ φ.ker.index :=
    Subgroup.one_lt_index_of_ne_top fun h => hxM (h ▸ Subgroup.mem_top x₀)
  calc 2 * Nat.card φ.ker ≤ φ.ker.index * Nat.card φ.ker := Nat.mul_le_mul_right _ hindex
    _ = Nat.card X := by rw [mul_comm, Subgroup.card_mul_index]

private theorem hom_ext_of_ker {X : Type u} [Group X] {φ : X →* Multiplicative (ZMod 2)}
    {x₀ : X} (hx₀ : φ x₀ ≠ 1) {ψ ψ' : X →* Multiplicative (ZMod 2)}
    (h1 : ψ.comp φ.ker.subtype = ψ'.comp φ.ker.subtype) (h2 : ψ x₀ = ψ' x₀) : ψ = ψ' := by
  have key : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a⁻¹ * b = 1 := by decide
  ext g
  by_cases hg : g ∈ φ.ker
  · exact DFunLike.congr_fun h1 ⟨g, hg⟩
  · have hmem : x₀⁻¹ * g ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact key _ _ hx₀ fun h' => hg (MonoidHom.mem_ker.2 h')
    have h3 : ψ (x₀⁻¹ * g) = ψ' (x₀⁻¹ * g) := DFunLike.congr_fun h1 ⟨x₀⁻¹ * g, hmem⟩
    calc ψ g = ψ (x₀ * (x₀⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = ψ x₀ * ψ (x₀⁻¹ * g) := map_mul ψ _ _
      _ = ψ' x₀ * ψ' (x₀⁻¹ * g) := by rw [h2, h3]
      _ = ψ' (x₀ * (x₀⁻¹ * g)) := (map_mul ψ' _ _).symm
      _ = ψ' g := by rw [mul_inv_cancel_left]

private theorem card_hom_le_card_aux : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X],
    Nat.card X = n → Nat.card (X →* Multiplicative (ZMod 2)) ≤ Nat.card X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hn
    have := finite_hom X
    by_cases h : ∀ φ : X →* Multiplicative (ZMod 2), φ = 1
    · have : Subsingleton (X →* Multiplicative (ZMod 2)) :=
        ⟨fun a b => (h a).trans (h b).symm⟩
      rw [Nat.card_unique]
      exact Nat.card_pos
    · obtain ⟨φ, hφ⟩ := not_forall.1 h
      obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.1 hφ
      rw [MonoidHom.one_apply] at hx₀
      have hcard := two_mul_card_ker_le hx₀
      have hpos : 0 < Nat.card φ.ker := Nat.card_pos
      have ihM := ih (Nat.card φ.ker) (by omega) φ.ker rfl
      have := finite_hom φ.ker
      have hΘ : Function.Injective fun ψ : X →* Multiplicative (ZMod 2) =>
          (ψ.comp φ.ker.subtype, ψ x₀) := fun ψ ψ' h =>
        hom_ext_of_ker hx₀ (Prod.mk.inj h).1 (Prod.mk.inj h).2
      calc Nat.card (X →* Multiplicative (ZMod 2))
          ≤ Nat.card ((φ.ker →* Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) :=
            Nat.card_le_card_of_injective _ hΘ
        _ = Nat.card (φ.ker →* Multiplicative (ZMod 2)) * 2 := by
            rw [Nat.card_prod]
            simp
        _ ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_right 2 ihM
        _ ≤ Nat.card X := by omega

theorem card_hom_le_card (X : Type*) [Group X] [Finite X] :
    Nat.card (X →* Multiplicative (ZMod 2)) ≤ Nat.card X :=
  card_hom_le_card_aux _ X rfl

theorem index_centralizer_le_card_commutator {X : Type*} [Group X] [Finite X] (t : X) :
    (Subgroup.centralizer ({t} : Set X)).index ≤ Nat.card (commutator X) := by
  set C := Subgroup.centralizer ({t} : Set X) with hC
  let g : X → commutator X := fun x =>
    ⟨x * t * x⁻¹ * t⁻¹, by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top t)⟩
  have hg : ∀ x y : X, g x = g y ↔ x⁻¹ * y ∈ C := by
    intro x y
    rw [hC, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    constructor
    · intro h
      have h2 : x * t * x⁻¹ = y * t * y⁻¹ := mul_right_cancel h
      calc x⁻¹ * y * t = x⁻¹ * (y * t * y⁻¹) * y := by group
        _ = x⁻¹ * (x * t * x⁻¹) * y := by rw [h2]
        _ = t * (x⁻¹ * y) := by group
    · intro h
      calc x * t * x⁻¹ * t⁻¹ = x * (t * (x⁻¹ * y)) * y⁻¹ * t⁻¹ := by group
        _ = x * (x⁻¹ * y * t) * y⁻¹ * t⁻¹ := by rw [h]
        _ = y * t * y⁻¹ * t⁻¹ := by group
  rw [Subgroup.index_eq_card]
  let f : X ⧸ C → commutator X :=
    Quotient.lift g fun x y hxy => (hg x y).2 (QuotientGroup.leftRel_apply.1 hxy)
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨x⟩ ⟨y⟩ h
  exact Quotient.sound (QuotientGroup.leftRel_apply.2 ((hg x y).1 h))

theorem card_abelianization_le_card_centralizer {X : Type*} [Group X] [Finite X] (t : X) :
    Nat.card (Abelianization X) ≤ Nat.card (Subgroup.centralizer ({t} : Set X)) := by
  have h1 := Subgroup.card_mul_index (commutator X)
  have h2 := Subgroup.card_mul_index (Subgroup.centralizer ({t} : Set X))
  have h3 := index_centralizer_le_card_commutator t
  have hD : 0 < Nat.card (commutator X) := Nat.card_pos
  have h4 : Nat.card (Abelianization X) = (commutator X).index :=
    (Subgroup.index_eq_card _).symm
  rw [h4]
  refine Nat.le_of_mul_le_mul_left ?_ hD
  calc Nat.card (commutator X) * (commutator X).index = Nat.card X := h1
    _ = Nat.card (Subgroup.centralizer ({t} : Set X)) *
        (Subgroup.centralizer ({t} : Set X)).index := h2.symm
    _ ≤ Nat.card (Subgroup.centralizer ({t} : Set X)) * Nat.card (commutator X) :=
        Nat.mul_le_mul_left _ h3
    _ = Nat.card (commutator X) * Nat.card (Subgroup.centralizer ({t} : Set X)) :=
        mul_comm _ _

theorem card_hom_le_card_centralizer_of_finite {X : Type*} [Group X] [Finite X] (t : X) :
    Nat.card (X →* Multiplicative (ZMod 2)) ≤ Nat.card (Subgroup.centralizer ({t} : Set X)) :=
  calc Nat.card (X →* Multiplicative (ZMod 2))
      = Nat.card (Abelianization X →* Multiplicative (ZMod 2)) :=
        Nat.card_congr Abelianization.lift
    _ ≤ Nat.card (Abelianization X) := card_hom_le_card _
    _ ≤ _ := card_abelianization_le_card_centralizer t

theorem card_hom_le_card_inf_centralizer_of_mem {G : Type*} [Group G] {X : Subgroup G}
    [Finite X] {t : G} (htX : t ∈ X) :
    Nat.card (X →* Multiplicative (ZMod 2)) ≤
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have h := card_hom_le_card_centralizer_of_finite (⟨t, htX⟩ : X)
  have e : Subgroup.centralizer ({(⟨t, htX⟩ : X)} : Set X) =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.mem_subgroupOf]
  rw [e] at h
  refine h.trans_eq ?_
  calc Nat.card ((Subgroup.centralizer ({t} : Set G)).subgroupOf X)
      = Nat.card ↥(((Subgroup.centralizer ({t} : Set G)).subgroupOf X).map X.subtype) :=
        (Subgroup.card_map_of_injective X.subtype_injective).symm
    _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) := by
        rw [Subgroup.subgroupOf_map_subtype]
    _ = Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by rw [inf_comm]

end RankLemma

end CFSG.EvenSporadicStandard.TwoB
