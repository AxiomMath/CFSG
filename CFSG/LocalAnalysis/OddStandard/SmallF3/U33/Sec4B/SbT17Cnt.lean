module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private def conjMap (ρ : G) {P : Subgroup G}
    (hPρ : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P) : P → P :=
  fun x => ⟨ρ * (x : G) * ρ⁻¹, hPρ x x.2⟩

private lemma conjMap_iterate_three (ρ : G) {P : Subgroup G}
    (hPρ : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P) (hρ : ρ ^ 3 = 1) :
    (conjMap ρ hPρ)^[3] = id := by
  funext x
  apply Subtype.ext
  have hp3 : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ
  have hpi3 : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    have : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = (ρ * ρ * ρ)⁻¹ := by group
    rw [this, hp3, inv_one]
  show ρ * (ρ * (ρ * (x : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (x : G)
  calc ρ * (ρ * (ρ * (x : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
      = (ρ * ρ * ρ) * (x : G) * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
    _ = 1 * (x : G) * 1 := by rw [hp3, hpi3]
    _ = (x : G) := by group

private theorem card_fixed_modEq {α : Type*} [Finite α] (f : α → α) {p : ℕ} [Fact p.Prime]
    (hf : f^[p] = id) : Nat.card α ≡ (Function.fixedPoints f).ncard [MOD p] := by
  classical
  haveI := Fintype.ofFinite α
  have hE : (show Function.End α from f) ^ (p ^ 1) = 1 := by
    rw [pow_one]
    exact hf
  have h := Equiv.Perm.card_fixedPoints_modEq hE
  rw [Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  convert h using 2

private theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

private theorem card_le_mul_card_orbit {H : Subgroup G} (x : G) {n : ℕ}
    (hn : Nat.card (Set.range fun h : H => (h : G) * x * (h : G)⁻¹) ≤ n) :
    Nat.card H ≤ n * Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have h1 := card_conj_orbit H.subtype x
  have h2 := Subgroup.card_mul_index ((centralizer ({x} : Set G)).comap H.subtype)
  have h3 : Nat.card ((centralizer ({x} : Set G)).comap H.subtype) =
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({x} : Set G)) H
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : H ⊓ centralizer ({x} : Set G) ≤ H)).toEquiv, e]
    rfl
  have h4 : ((centralizer ({x} : Set G)).comap H.subtype).index ≤ n := by
    rw [← h1]
    exact hn
  rw [← h3, ← h2]
  calc Nat.card ((centralizer ({x} : Set G)).comap H.subtype) *
        ((centralizer ({x} : Set G)).comap H.subtype).index
      ≤ Nat.card ((centralizer ({x} : Set G)).comap H.subtype) * n := Nat.mul_le_mul_left _ h4
    _ = n * Nat.card ((centralizer ({x} : Set G)).comap H.subtype) := mul_comm _ _

theorem relIndex_mod_three {P Q : Subgroup G} (hQP : Q ≤ P) {ρ : G} (hρ : ρ ^ 3 = 1)
    (hPρ : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P) (hQρ : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q)
    (hfix : ∀ x ∈ P, ρ * x * ρ⁻¹ = x → x = 1) (hQ : Nat.card Q % 3 = 1) :
    Q.relIndex P % 3 = 1 := by
  have hiter := conjMap_iterate_three ρ hPρ hρ
  have hmod := card_fixed_modEq (conjMap ρ hPρ) hiter
  have hset : Function.fixedPoints (conjMap ρ hPρ) = ({1} : Set P) := by
    ext x
    rw [Function.mem_fixedPoints_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      apply hfix (x : G) x.2
      simpa [conjMap] using congrArg Subtype.val hx
    · intro hx
      rw [hx]
      apply Subtype.ext
      simp [conjMap]
  have hfixcard : (Function.fixedPoints (conjMap ρ hPρ)).ncard = 1 := by
    rw [hset, Set.ncard_singleton]
  rw [hfixcard] at hmod
  have hcardP : Nat.card P % 3 = 1 := by
    have hmod' := hmod
    unfold Nat.ModEq at hmod'
    simpa using hmod'
  have hPQ : Nat.card P = Nat.card Q * Q.relIndex P := by
    have h := Subgroup.card_mul_index (Q.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv] at h
    rw [← h]
    rfl
  have h1 : (Nat.card Q * Q.relIndex P) % 3 = 1 := by
    rw [← hPQ]
    exact hcardP
  have hm : (Nat.card Q * Q.relIndex P) % 3 = Q.relIndex P % 3 := by
    rw [Nat.mul_mod, hQ, one_mul, Nat.mod_mod]
  rw [hm] at h1
  exact h1

theorem card_le_mul_card_centralizer {R A : Subgroup G} (hA : ∀ r ∈ R, ∀ x ∈ A, r * x * r⁻¹ ∈ A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hAR : A ≤ R) :
    Nat.card R ≤ (Nat.card A - 1) * Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  refine card_le_mul_card_orbit (H := R) a ?_
  have hsub : Set.range (fun h : R => (h : G) * a * (h : G)⁻¹) ⊆ (A : Set G) \ {1} := by
    rintro y ⟨r, rfl⟩
    refine ⟨hA r r.2 a ha, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    apply ha1
    have h' := congrArg (fun z : G => (r : G)⁻¹ * z * (r : G)) h
    rwa [show (r : G)⁻¹ * ((r : G) * a * (r : G)⁻¹) * (r : G) = a by group,
      show (r : G)⁻¹ * 1 * (r : G) = 1 by group] at h'
  have hAncard : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  calc Nat.card (Set.range fun h : R => (h : G) * a * (h : G)⁻¹)
      = (Set.range fun h : R => (h : G) * a * (h : G)⁻¹).ncard := Nat.card_coe_set_eq _
    _ ≤ ((A : Set G) \ {1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (A : Set G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem A.one_mem
    _ = Nat.card A - 1 := by rw [hAncard]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
