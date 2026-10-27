module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.Q3.TL3Sub
public import CFSG.ClassicalInvolution.Q3.TL3Lift
public import CFSG.ClassicalInvolution.Q3.TL3QuatAut

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def TightSubnormalLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) ∧ x ^ 3 ^ k = 1 ∧
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
      IsSubnormal (R ⊔ Subgroup.zpowers x ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G)))
        (Subgroup.centralizer ({t} : Set G))

@[expose] def TightThreeElementLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) ∧ x ^ 3 ^ k = 1 ∧
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
        ⁅x, y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))

theorem tl3_nonempty_mulEquiv_q8 {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) {C : Subgroup G}
    (hCR : C ≤ Subgroup.normalizer (R : Set G)) {x : G} (hxC : x ∈ C) {k : ℕ}
    (hx3 : x ^ 3 ^ k = 1) (hxR : ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) :
    Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hS
  by_cases hr3 : r = 3
  · subst hr3
    exact ⟨e⟩
  · exfalso
    have hr4 : 2 ≤ r - 2 := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2 S
    set P : MulAut (R ⧸ oddCore R) := tl3Act R ⟨x, hCR hxC⟩ with hP
    have hPk : P ^ 3 ^ k = 1 := by
      rw [hP, ← map_pow]
      have : (⟨x, hCR hxC⟩ : Subgroup.normalizer (R : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hP1 : P = 1 := tl3_aut_pow_three_of_equiv hr4 (e1.trans e) P hPk
    obtain ⟨r', hr', hnr⟩ := hxR
    exact hnr ((tl3Act_eq_one_iff R ⟨x, hCR hxC⟩).mp hP1 r' hr')

theorem tightLift3_of_tightSubnormalLarge (h : TightSubnormalLarge) : TightLift3 := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨x, k, hxC, hx3, hxR, hsub⟩ := h G hnab hlarge R S hS t ht hto hRC hRn h2
  have hCR : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hS8 := tl3_nonempty_mulEquiv_q8 S hS h2 hCR hxC hx3 hxR
  exact ⟨_, le_sup_left.trans le_sup_left,
    isClassicalMember3_of_subnormal S hS8 ht hto hRC hRn h2 hxC hx3 hxR hsub⟩

theorem tightSubnormalLarge_of_tightThreeElementLarge (h : TightThreeElementLarge) :
    TightSubnormalLarge := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨x, k, hxC, hx3, hxR, hxD⟩ := h G hnab hlarge R S hS t ht hto hRC hRn h2
  have hCR : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2 S
  obtain ⟨e2⟩ := tl3_nonempty_mulEquiv_q8 S hS h2 hCR hxC hx3 hxR
  exact ⟨x, k, hxC, hx3, hxR, isSubnormal_threeElement_join hRC hCR (e1.trans e2) hxC hx3 hxR hxD⟩

theorem tightLift3_of_tightThreeElementLarge (h : TightThreeElementLarge) : TightLift3 :=
  tightLift3_of_tightSubnormalLarge (tightSubnormalLarge_of_tightThreeElementLarge h)

end CFSG.ClassicalInvolution.Q3
