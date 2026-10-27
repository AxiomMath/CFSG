module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open scoped Pointwise

variable {G X ι : Type*} [Group G] [MulAction G X] [DecidableEq X]

def familyStab [Finite ι] (ℓ : ι → Finset X) (hℓ : Function.Injective ℓ) : Subgroup G where
  carrier := {g | ∀ i, ∃ j, g • ℓ i = ℓ j}
  mul_mem' := by
    intro g h hg hh i
    obtain ⟨j, hj⟩ := hh i
    obtain ⟨k, hk⟩ := hg j
    exact ⟨k, by rw [mul_smul, hj, hk]⟩
  one_mem' := fun i => ⟨i, one_smul _ _⟩
  inv_mem' := by
    intro g hg i
    choose σ hσ using hg
    have hinj : Function.Injective σ := by
      intro i i' h
      apply hℓ
      have : g • ℓ i = g • ℓ i' := by rw [hσ, hσ, h]
      exact MulAction.injective g this
    obtain ⟨i₀, hi₀⟩ := Finite.surjective_of_injective hinj i
    exact ⟨i₀, by rw [inv_smul_eq_iff, hσ, hi₀]⟩

theorem closure_le_familyStab [Finite ι] {ℓ : ι → Finset X} (hℓ : Function.Injective ℓ)
    {S : Set G} (hS : ∀ g ∈ S, ∀ i, ∃ j, g • ℓ i = ℓ j) :
    Subgroup.closure S ≤ familyStab ℓ hℓ :=
  (Subgroup.closure_le _).2 hS

variable [Finite ι] [Nonempty ι] (ℓ : ι → Finset X) (hℓ : Function.Injective ℓ)

noncomputable def famAct (g : G) (i : ι) : ι := Function.invFun ℓ (g • ℓ i)

theorem smul_eq_famAct {g : G} (hg : g ∈ familyStab ℓ hℓ) (i : ι) :
    g • ℓ i = ℓ (famAct ℓ g i) := by
  obtain ⟨j, hj⟩ := hg i
  unfold famAct
  rw [hj, Function.leftInverse_invFun hℓ j]

theorem famAct_mul {g h : G} (hg : g ∈ familyStab ℓ hℓ) (hh : h ∈ familyStab ℓ hℓ) (i : ι) :
    famAct ℓ (g * h) i = famAct ℓ g (famAct ℓ h i) := by
  apply hℓ
  rw [← smul_eq_famAct ℓ hℓ ((familyStab ℓ hℓ).mul_mem hg hh), mul_smul,
    smul_eq_famAct ℓ hℓ hh, smul_eq_famAct ℓ hℓ hg]

include hℓ in
theorem famAct_one (i : ι) : famAct ℓ (1 : G) i = i := by
  apply hℓ
  rw [← smul_eq_famAct ℓ hℓ ((familyStab ℓ hℓ).one_mem : (1 : G) ∈ familyStab ℓ hℓ), one_smul]

noncomputable def familyHom : familyStab (G := G) ℓ hℓ →* Equiv.Perm ι where
  toFun g :=
    { toFun := famAct ℓ (g : G)
      invFun := famAct ℓ ((g⁻¹ : familyStab (G := G) ℓ hℓ) : G)
      left_inv := fun i => by
        have h := famAct_mul ℓ hℓ (g⁻¹ : familyStab (G := G) ℓ hℓ).2 g.2 i
        have h1 : (((g⁻¹ : familyStab (G := G) ℓ hℓ) : G) * (g : G)) = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        rw [h1, famAct_one ℓ hℓ] at h
        exact h.symm
      right_inv := fun i => by
        have h := famAct_mul ℓ hℓ g.2 (g⁻¹ : familyStab (G := G) ℓ hℓ).2 i
        have h1 : ((g : G) * ((g⁻¹ : familyStab (G := G) ℓ hℓ) : G)) = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
        rw [h1, famAct_one ℓ hℓ] at h
        exact h.symm }
  map_one' := by
    ext i
    exact famAct_one ℓ hℓ i
  map_mul' g h := by
    ext i
    exact famAct_mul ℓ hℓ g.2 h.2 i

theorem smul_familyHom (g : familyStab (G := G) ℓ hℓ) (i : ι) :
    (g : G) • ℓ i = ℓ (familyHom ℓ hℓ g i) :=
  smul_eq_famAct ℓ hℓ g.2 i

include hℓ in
theorem exists_permHom_of_closure {S : Set G} (hS : ∀ g ∈ S, ∀ i, ∃ j, g • ℓ i = ℓ j) :
    ∃ π : Subgroup.closure S →* Equiv.Perm ι,
      ∀ (g : Subgroup.closure S) (i : ι), (g : G) • ℓ i = ℓ (π g i) :=
  ⟨(familyHom ℓ hℓ).comp (Subgroup.inclusion (closure_le_familyStab hℓ hS)),
    fun g i => smul_familyHom ℓ hℓ ⟨g, closure_le_familyStab hℓ hS g.2⟩ i⟩

end CFSG.EvenSporadicStandard.Induction.AutBound
