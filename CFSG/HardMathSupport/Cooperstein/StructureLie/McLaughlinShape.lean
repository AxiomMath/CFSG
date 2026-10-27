module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin
import CFSG.ClassicalGroups.Symplectic.Perfect
import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem commutator_le_of_relIndex_two {G : Type*} [Group G] {H L : Subgroup G}
    (hidx : L.relIndex H = 2) : ⁅H, H⁆ ≤ L := by
  have hN : (L.subgroupOf H).index = 2 := hidx
  have : (L.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (H ⧸ L.subgroupOf H) = 2 := hN
  have : IsCyclic (H ⧸ L.subgroupOf H) := isCyclic_of_prime_card hcard
  have : IsMulCommutative (H ⧸ L.subgroupOf H) := inferInstance
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆ : H) ∈ L.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff]
    have h2 := map_commutatorElement (QuotientGroup.mk' (L.subgroupOf H)) (⟨x, hx⟩ : H)
      (⟨y, hy⟩ : H)
    have h3 : (QuotientGroup.mk' (L.subgroupOf H)) ⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆ = 1 := by
      rw [h2, commutatorElement_eq_one_iff_mul_comm]
      exact Std.Commutative.comm (op := (· * ·)) _ _
    exact h3
  exact h1

theorem false_of_perfect_of_relIndex_two {G : Type*} [Group G] {H L : Subgroup G}
    (hidx : L.relIndex H = 2) (hperf : ⁅H, H⁆ = H) : False := by
  have hle : H ≤ L := hperf ▸ commutator_le_of_relIndex_two hidx
  have h1 : L.relIndex H = 1 := Subgroup.relIndex_eq_one.mpr hle
  omega

section Perfect

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem commutator_top_eq_top_of_three_le (h3 : 3 ≤ finrank (ZMod 2) W) :
    ⁅(⊤ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)),
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))⁆ = ⊤ := by
  have := CFSG.GroupTheory.GLnTwoSplitting.isPerfect_linearEquiv (E := W) h3
  have : Group.IsPerfect (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
    Group.IsPerfect.ofSurjective
      (f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.toMonoidHom)
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.surjective
  exact Group.isPerfect_def.mp this

private noncomputable def bilinIsometryGroupEquiv' (B : LinearMap.BilinForm (ZMod 2) W) :
    bilinIsometryGroup B ≃*
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).subgroupMap
      (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
          B _).mpr hh
      · intro hg
        refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm g, ?_,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).apply_symm_apply g⟩
        exact (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
          B g).mp hg))

theorem commutator_bilinIsometryGroup_eq_self {f : LinearMap.BilinForm (ZMod 2) W}
    (hnd : f.Nondegenerate) (halt : f.IsAlt) (h6 : 6 ≤ finrank (ZMod 2) W) :
    ⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ = bilinIsometryGroup f := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      f halt hnd
  have hperf := CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin (ZMod 2) m
    (Or.inr (Or.inr ⟨Nat.card_zmod 2, by omega⟩))
  let φ : bilinIsometryGroup f ≃* TauCeti.GLSymplecticFin m (ZMod 2) :=
    ((bilinIsometryGroupEquiv' f).trans e).trans
      (TauCeti.GLSymplecticFin.mulEquivGLSymplectic m (ZMod 2)).symm
  have : Group.IsPerfect (bilinIsometryGroup f) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

end Perfect

section Small

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem eq_bot_of_isPerfect_of_finrank_le_two (h2 : finrank (ZMod 2) W ≤ 2)
    (L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (hperf : ⁅L, L⁆ = L) : L = ⊥ := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite W
  let π : (W ≃ₗ[ZMod 2] W) →* Equiv.Perm W :=
    { toFun := fun e => e.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : LinearMap.GeneralLinearGroup (ZMod 2) W →* Equiv.Perm W :=
    π.comp (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).injective
    ext x
    exact congrArg (fun p : Equiv.Perm W => p x) hab
  have hcard : Nat.card W ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod]
    calc 2 ^ finrank (ZMod 2) W ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  have hsolv : Group.IsSolvable (Equiv.Perm W) := Equiv.Perm.isSolvable hcard
  have hsolvL : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := ψ.comp L.subtype) (hψ.comp Subtype.val_injective)
  by_contra hne
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable L hsolvL

end Small

theorem shape_of_perfect_index_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hn : 1 ≤ Module.finrank (ZMod 2) W)
    (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ t ∈ S, IsF2Transvection t) ∧ H = Subgroup.closure S)
    (hirr : ∀ U : Submodule (ZMod 2) W,
      (∀ g ∈ H, ∀ u ∈ U, (g : W →ₗ[ZMod 2] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hLH : L ≤ H) (hidx : L.relIndex H = 2) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) :
    L = ⁅H, H⁆ ∧
      ((Module.finrank (ZMod 2) W = 4 ∧ ∃ f : LinearMap.BilinForm (ZMod 2) W,
          f.Nondegenerate ∧ f.IsAlt ∧ H = bilinIsometryGroup f) ∨
        (∃ Q : QuadraticForm (ZMod 2) W, (QuadraticMap.polarBilin Q).Nondegenerate ∧
          H = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
            (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom) ∨
        (Even (finrank (ZMod 2) W) ∧
          ((∃ β : W ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) W + 1),
              H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
                (sumZeroRep (finrank (ZMod 2) W + 1)).range) ∨
            ∃ β : W ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) W + 2) ⧸
                onesLine (finrank (ZMod 2) W + 2),
              H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
                (heartRep (finrank (ZMod 2) W + 2)).range))) := by
  have h3 : 3 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    exact hL1 (eq_bot_of_isPerfect_of_finrank_le_two (by omega) L hperf)
  refine ⟨le_antisymm ?_ (commutator_le_of_relIndex_two hidx), ?_⟩
  · calc L = ⁅L, L⁆ := hperf.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hLH hLH
  rcases mclaughlin_transvection_groups_F2 hn H hgen hirr with
    hH | ⟨he, f, hnd, halt, hH⟩ | ⟨-, Q, hQ, hH⟩ | hSym
  · exfalso
    refine false_of_perfect_of_relIndex_two hidx ?_
    rw [hH]
    exact commutator_top_eq_top_of_three_le h3
  · obtain ⟨k, hk⟩ := he
    by_cases hk2 : k = 2
    · exact Or.inl ⟨by omega, f, hnd, halt, hH⟩
    · exfalso
      refine false_of_perfect_of_relIndex_two hidx ?_
      rw [hH]
      exact commutator_bilinIsometryGroup_eq_self hnd halt (by omega)
  · exact Or.inr (Or.inl ⟨Q, hQ, hH⟩)
  · exact Or.inr (Or.inr hSym)

end CFSG.HardMathSupport.Cooperstein.StructureLie
