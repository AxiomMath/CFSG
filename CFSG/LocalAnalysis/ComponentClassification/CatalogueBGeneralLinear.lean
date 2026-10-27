module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.ComponentClassification.CatalogueBGeneralLinear

noncomputable section

universe u

theorem perfect_le_specialLinearRange (n : ℕ) (K : Type u) [Field K]
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) [Group.IsPerfect L] :
    L ≤ specialLinearRange n K := by
  rw [specialLinearRange_eq_detKernel]
  intro A hA
  exact Abelianization.commutator_subset_ker
    ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) K →* Kˣ).comp
      L.subtype) (Group.IsPerfect.mem_commutator (g := (⟨A, hA⟩ : L)))

theorem perfect_subnormal_eq_specialLinearRange (n : ℕ) (K : Type u)
    [Field K] [Finite K] (hn : 2 ≤ n)
    (h22 : n ≠ 2 ∨ Nat.card K ≠ 2) (h23 : n ≠ 2 ∨ Nat.card K ≠ 3)
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    [Group.IsPerfect L] [Nontrivial L] (hsubnormal : L.IsSubnormal) :
    L = specialLinearRange n K := by
  have hle := perfect_le_specialLinearRange n K L
  let J := L.subgroupOf (specialLinearRange n K)
  let e : J ≃* L := Subgroup.subgroupOfEquivOfLe hle
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial J := e.toEquiv.nontrivial
  have hJ : J.IsSubnormal := hsubnormal.subgroupOf
  have hquasi : CFSG.Open.IsQuasisimple (specialLinearRange n K) :=
    CatalogueBAlternating.quasisimple_iff_native.mp
      (specialLinearRange_quasisimple n K hn h22 h23)
  have htop : J = ⊤ :=
    (Quasisimple.perfect_subnormal_eq_bot_or_eq_top hquasi J
      (Components.chain_of_mathlib_subnormal hJ)).resolve_left
        (J.nontrivial_iff_ne_bot.mp inferInstance)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

theorem pComponent_eq_specialLinearRange (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) (p : ℕ)
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hL : CFSG.IsPComponent p L) : L = specialLinearRange n K := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact perfect_subnormal_eq_specialLinearRange n K hn h22 h23 L
    hL.choose_spec.2.1

theorem pComponent_retained_classification (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) (p : ℕ)
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hL : CFSG.IsPComponent p L) :
    L = specialLinearRange n K ∧ CFSG.IsQuasisimple L := by
  have heq := pComponent_eq_specialLinearRange n K hn h22 h23 p L hL
  refine ⟨heq, ?_⟩
  rw [heq]
  exact specialLinearRange_quasisimple n K hn h22 h23

theorem retained_parameters (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n)
    (hretained : ¬ (n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3))) :
    2 ≤ n ∧ (n ≠ 2 ∨ Nat.card K ≠ 2) ∧ (n ≠ 2 ∨ Nat.card K ≠ 3) := by
  omega

theorem retained_quasisimple_and_pComponents (n : ℕ) (K : Type u)
    [Field K] [Finite K] (hn : 1 ≤ n)
    (hretained : ¬ (n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3))) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin n) K) ∧
      CFSG.IsQuasisimple (specialLinearRange n K) ∧
      ∀ (p : ℕ), p.Prime →
        ∀ L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K),
          CFSG.IsPComponent p L → L = specialLinearRange n K ∧ CFSG.IsQuasisimple L := by
  obtain ⟨hn2, h22, h23⟩ := retained_parameters n K hn hretained
  exact ⟨specialLinear_quasisimple n K hn2 h22 h23,
    specialLinearRange_quasisimple n K hn2 h22 h23,
    fun p _ L hL => pComponent_retained_classification n K hn2 h22 h23 p L hL⟩

theorem pComponent_classification (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (p : ℕ) (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hL : CFSG.IsPComponent p L) :
    2 ≤ n ∧ (n ≠ 2 ∨ Nat.card K ≠ 2) ∧ (n ≠ 2 ∨ Nat.card K ≠ 3) ∧
      L = specialLinearRange n K ∧ CFSG.IsQuasisimple L := by
  have hretained : ¬ (n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)) := by
    intro hsmall
    exact generalLinear_small_no_pComponent n K hsmall p L hL
  obtain ⟨hn2, h22, h23⟩ := retained_parameters n K hn hretained
  exact ⟨hn2, h22, h23, pComponent_retained_classification n K hn2 h22 h23 p L hL⟩

theorem pComponent_quasisimple (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (p : ℕ) (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  (pComponent_classification n K hn p L hL).2.2.2.2

theorem generalLinear_p_components (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) :
    Nonempty (specialLinearRange n K ≃* Matrix.SpecialLinearGroup (Fin n) K) ∧
      ((n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3) →
        Group.IsSolvable (Matrix.GeneralLinearGroup (Fin n) K) ∧
          ∀ (p : ℕ), p.Prime →
            ∀ L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K), ¬ CFSG.IsPComponent p L) ∧
      (¬ (n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)) →
        CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin n) K) ∧
          CFSG.IsQuasisimple (specialLinearRange n K) ∧
          ∀ (p : ℕ), p.Prime →
            ∀ L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K),
              CFSG.IsPComponent p L →
                L = specialLinearRange n K ∧ CFSG.IsQuasisimple L)) := by
  refine ⟨⟨rangeEquivSpecialLinear n K⟩, ?_, ?_⟩
  · intro hsmall
    exact ⟨generalLinear_small_solvable n K hsmall,
      fun p _ L => generalLinear_small_no_pComponent n K hsmall p L⟩
  · exact retained_quasisimple_and_pComponents n K hn

end

end CFSG.ComponentClassification.CatalogueBGeneralLinear
