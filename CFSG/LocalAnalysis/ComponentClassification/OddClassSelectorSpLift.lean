module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem map_fixedSubgroup_of_comm {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    (α : MulAut P) (α' : MulAut P') (h : ∀ x, e (α x) = α' (e x)) :
    (fixedSubgroup α).map e.toMonoidHom = fixedSubgroup α' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α' (e x) = e x
    rw [← h]
    exact congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change α (e.symm y) = e.symm y
    apply e.injective
    rw [h, e.apply_symm_apply]
    exact hy

theorem central_lift {S : Type*} [Group S] [Finite S] (Z : Subgroup S) [Z.Normal]
    (hZ : Z ≤ center S) (φ : MulAut S) (hφZ : Z.map φ.toMonoidHom = Z)
    (hφφ : ∀ g, φ (φ g) = g) {X : Subgroup (S ⧸ Z)}
    (hX : CFSG.Assembly.IsComponentOf X
      (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ))) :
    ∃ Y : Subgroup S, CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      (∃ σ : Y →* X, Function.Surjective σ ∧ σ.ker ≤ center Y ∧
        ∀ y : Y, (σ y : S ⧸ Z) = QuotientGroup.mk' Z (y : S)) ∧
      (NoTightWitness X → ∀ t s : S, t * t ∈ Z → t ∉ Z → (∀ y ∈ Y, y * t = t * y) →
        s * t = t * s → s ∈ normalizer (Y : Set S)) := by
  classical
  obtain ⟨-, hYm, hYmap, -⟩ := LocalAnalysis.ComponentInitial.lift_isComponentOf_fixed
    (π := QuotientGroup.mk' Z) (a := φ) (α := CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ)
    (QuotientGroup.mk'_surjective Z) (by rw [QuotientGroup.ker_mk']; exact hZ) hφφ
    (fun x => (CatalogueBFixedCentralQuotient.onQuotient_mk Z φ hφZ x).symm) hX
  refine ⟨_, hYm, ?_, ?_⟩
  · have hρ : ∀ y : ↥⁅X.comap (QuotientGroup.mk' Z), X.comap (QuotientGroup.mk' Z)⁆,
        QuotientGroup.mk' Z (y : S) ∈ X := fun y => by
      have h1 := mem_map_of_mem (QuotientGroup.mk' Z) y.2
      rwa [hYmap] at h1
    refine ⟨((QuotientGroup.mk' Z).comp (Subgroup.subtype _)).codRestrict X hρ, ?_, ?_,
      fun _ => rfl⟩
    · intro x
      have hx : (x : S ⧸ Z) ∈ (⁅X.comap (QuotientGroup.mk' Z),
          X.comap (QuotientGroup.mk' Z)⁆).map (QuotientGroup.mk' Z) := by
        rw [hYmap]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · intro y hy
      have h1 : QuotientGroup.mk' Z (y : S) = 1 := congrArg Subtype.val hy
      have h2 : (y : S) ∈ center S := hZ ((QuotientGroup.eq_one_iff _).mp h1)
      rw [mem_center_iff] at h2 ⊢
      intro z
      exact Subtype.ext (h2 z)
  · intro hW t s ht2 htZ htY hst
    have htP1 : QuotientGroup.mk' Z t ≠ 1 := fun h => htZ ((QuotientGroup.eq_one_iff t).mp h)
    have htP2 : QuotientGroup.mk' Z t * QuotientGroup.mk' Z t = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr ht2
    have hord : orderOf (QuotientGroup.mk' Z t) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact htP2) htP1
    have hcomm : ∀ x ∈ X, x * QuotientGroup.mk' Z t = QuotientGroup.mk' Z t * x := by
      intro x hx
      rw [← hYmap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← map_mul, ← map_mul, htY y hy]
    have hst' : QuotientGroup.mk' Z s * QuotientGroup.mk' Z t =
        QuotientGroup.mk' Z t * QuotientGroup.mk' Z s := by
      rw [← map_mul, ← map_mul, hst]
    have hN := hW _ _ hord hcomm hst'
    have hN' : s ∈ normalizer ((X.comap (QuotientGroup.mk' Z) : Subgroup S) : Set S) := by
      rw [mem_normalizer_iff] at hN ⊢
      intro z
      rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
      exact hN _
    exact mem_normalizer_commutator hN'

end CFSG.ComponentClassification.OddClassSelector
