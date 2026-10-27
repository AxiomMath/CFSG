module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenA

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_commutator_subgroup {A : Subgroup G} {x : G}
    (h : ∀ a ∈ A, ⁅a, x⁆ ∈ A ⊓ centralizer (A : Set G)) :
    ∃ W : Subgroup G, (∀ w, w ∈ W ↔ ∃ a ∈ A, ⁅a, x⁆ = w) ∧
      Nat.card A = Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card W := by
  let φ : A →* G :=
    { toFun := fun a => ⁅(a : G), x⁆
      map_one' := commutatorElement_one_left x
      map_mul' := fun a b => by
        obtain ⟨-, hbC⟩ := h b b.2
        have haA : ⁅(a : G), x⁆ ∈ A := (h a a.2).1
        have h1 : (a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹ = ⁅(b : G), x⁆ := by
          rw [Subgroup.mem_centralizer_iff.mp hbC a a.2, mul_inv_cancel_right]
        change ⁅(a : G) * b, x⁆ = ⁅(a : G), x⁆ * ⁅(b : G), x⁆
        rw [commutatorElement_mul_left_eq_conj_mul, h1]
        exact (Subgroup.mem_centralizer_iff.mp hbC _ haA).symm }
  refine ⟨φ.range, fun w => ?_, ?_⟩
  · rw [MonoidHom.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, a.2, ha⟩, fun ⟨a, ha, haw⟩ => ⟨⟨a, ha⟩, haw⟩⟩
  · have hker : φ.ker = (A ⊓ centralizer ({x} : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        mem_centralizer_singleton_iff]
      change ⁅(a : G), x⁆ = 1 ↔ _
      exact ⟨fun ha => ⟨a.2, commutatorElement_eq_one_iff_mul_comm.mp ha⟩,
        fun ha => commutatorElement_eq_one_iff_mul_comm.mpr ha.2⟩
    rw [← Subgroup.card_ker_mul_card_range φ, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem commutator_mem_of_mem_closure {T : Subgroup G} {X : Set G} {a : G}
    (hX : X ⊆ centralizer (T : Set G)) (h : ∀ x ∈ X, ⁅x, a⁆ ∈ T) {y : G}
    (hy : y ∈ closure X) : ⁅y, a⁆ ∈ T := by
  have key : y ∈ centralizer (T : Set G) ∧ ⁅y, a⁆ ∈ T := by
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact ⟨hX hx, h x hx⟩
    | one => exact ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
    | mul x y _ _ hx hy =>
      refine ⟨mul_mem hx.1 hy.1, ?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul,
        ← Subgroup.mem_centralizer_iff.mp hx.1 _ hy.2, mul_inv_cancel_right]
      exact mul_mem hy.2 hx.2
    | inv x _ hx =>
      refine ⟨inv_mem hx.1, ?_⟩
      have hw : ⁅x, a⁆⁻¹ ∈ T := inv_mem hx.2
      rw [commutatorElement_inv_left, ← commutatorElement_inv,
        ← Subgroup.mem_centralizer_iff.mp (inv_mem hx.1) _ hw, inv_mul_cancel_right]
      exact hw
  exact key.2

theorem commutator_mem_of_mem_closure_right {T : Subgroup G} {X : Set G} {a : G}
    (hX : X ⊆ centralizer (T : Set G)) (h : ∀ x ∈ X, ⁅a, x⁆ ∈ T) {y : G}
    (hy : y ∈ closure X) : ⁅a, y⁆ ∈ T := by
  rw [← commutatorElement_inv]
  refine inv_mem (commutator_mem_of_mem_closure hX (fun x hx => ?_) hy)
  rw [← commutatorElement_inv]
  exact inv_mem (h x hx)

theorem card_conj_orbit_mul (K : Subgroup G) (x : G) :
    Nat.card {y : G // ∃ k ∈ K, k * x * k⁻¹ = y} *
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card K := by
  let f : G →* ConjAct G := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
  let K' : Subgroup (ConjAct G) := K.map f
  have hsmul : ∀ k : G, f k • x = k * x * k⁻¹ := fun k => by
    simp [f, ConjAct.smul_def]
  have h1 : Nat.card (MulAction.orbit K' x) =
      Nat.card {y : G // ∃ k ∈ K, k * x * k⁻¹ = y} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun y => ?_
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
      exact ⟨k', hk', (hsmul k').symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨f k, Subgroup.mem_map_of_mem f hk⟩, hsmul k⟩
  have h2 : Nat.card (MulAction.stabilizer K' x) =
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have hmem : ∀ k : G, f k ∈ K' ↔ k ∈ K := fun k =>
      Subgroup.mem_map_iff_mem (ConjAct.toConjAct : G ≃* ConjAct G).injective
    refine Nat.card_congr
      { toFun := fun k => ⟨ConjAct.ofConjAct ((k : K') : ConjAct G), ?_⟩
        invFun := fun k => ⟨⟨f k, (hmem k).mpr k.2.1⟩, ?_⟩
        left_inv := fun k => by ext; simp [f]
        right_inv := fun k => by ext; simp [f] }
    · obtain ⟨⟨k, hkK⟩, hk⟩ := k
      have hk2 : (⟨k, hkK⟩ : K') • x = x := hk
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkK
      have hk3 : k' * x * k'⁻¹ = x := (hsmul k').symm.trans hk2
      refine ⟨by simpa [f] using hk', mem_centralizer_singleton_iff.mpr ?_⟩
      simp only [f, MulEquiv.coe_toMonoidHom, ConjAct.ofConjAct_toConjAct]
      calc k' * x = k' * x * k'⁻¹ * k' := by group
        _ = x * k' := by rw [hk3]
    · have hk := mem_centralizer_singleton_iff.mp k.2.2
      change f k • x = x
      rw [hsmul, hk]
      group
  have h3 : Nat.card K' = Nat.card K :=
    Subgroup.card_map_of_injective (ConjAct.toConjAct : G ≃* ConjAct G).injective
  rw [← h1, ← h2, ← h3, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K' x),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem exists_conj_of_card_le [Finite G] {K A : Subgroup G}
    (hKA : ∀ k ∈ K, ∀ y ∈ A, k * y * k⁻¹ ∈ A) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hcard : (Nat.card A - 1) * Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      Nat.card K) {y : G} (hyA : y ∈ A) (hy1 : y ≠ 1) : ∃ k ∈ K, k * x * k⁻¹ = y := by
  let O : Set G := {y | ∃ k ∈ K, k * x * k⁻¹ = y}
  let X : Set G := (A : Set G) \ {1}
  have hOX : O ⊆ X := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨hKA k hk x hxA, fun h => hx1 ?_⟩
    rwa [Set.mem_singleton_iff, mul_inv_eq_one, mul_eq_left] at h
  have hX : X.ncard = Nat.card A - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem A), ← Nat.card_coe_set_eq]
    rfl
  have hO : O.ncard * Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card K := by
    rw [← Nat.card_coe_set_eq]
    exact card_conj_orbit_mul K x
  have hpos : 0 < Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
  have hle : X.ncard ≤ O.ncard := by
    rw [hX]
    exact Nat.le_of_mul_le_mul_right (hcard.trans hO.ge) hpos
  have hOX' : O = X := Set.eq_of_subset_of_ncard_le hOX hle (Set.toFinite X)
  have hy : y ∈ X := ⟨hyA, hy1⟩
  rw [← hOX'] at hy
  exact hy

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
