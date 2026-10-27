module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Solomon.Coordinator

private theorem charP_of_card_eq_cube (ℓ f : ℕ) (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) : CharP K ℓ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      have := Finite.one_lt_card (α := K)
      rw [pow_zero, one_pow] at hK
      omega
    · exact h
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3

private theorem exists_noncomm_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hnc : ∃ a b : H, a * b ≠ b * a) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at h'
  exact h'

section FieldActor

theorem map_subtype_fixSubgroup_fieldActor (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ σ := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 (mem_fixSubgroup.1 hg)
  · intro hx
    exact ⟨⟨x, d4_trialityFieldImage_self_le σ hx⟩,
      (d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hx, rfl⟩

noncomputable def fixSubgroupFieldActorEquiv (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) ≃* trialityFieldImage σ σ :=
  (Subgroup.equivMapOfInjective (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_fixSubgroup_fieldActor K σ hσ3))

theorem isSimpleGroup_fixSubgroup_fieldActor_D4 (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    IsSimpleGroup (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  haveI := charP_of_card_eq_cube ℓ f hℓ K hK
  obtain ⟨hsimple, -⟩ := d4_trialityFieldImage_self_simple hℓ2 σ
  haveI := hsimple
  exact (fixSubgroupFieldActorEquiv K σ (ringEquiv_cube_apply_eq hK hσ)).isSimpleGroup

theorem nonabelian_fixSubgroup_fieldActor_D4 (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ x y : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ), x * y ≠ y * x := by
  haveI := charP_of_card_eq_cube ℓ f hℓ K hK
  obtain ⟨-, hnc⟩ := d4_trialityFieldImage_self_simple hℓ2 σ
  simp only [not_forall, ne_eq] at hnc
  exact exists_noncomm_of_mulEquiv (fixSubgroupFieldActorEquiv K σ (ringEquiv_cube_apply_eq hK hσ))
    hnc

end FieldActor

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
