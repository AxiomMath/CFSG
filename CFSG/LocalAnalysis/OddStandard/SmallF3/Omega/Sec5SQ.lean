module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private noncomputable def sec5sq_det (Q : QuadraticForm (ZMod 3) V) :
    simGroup Q →* (ZMod 3)ˣ :=
  (LinearEquiv.det : (V ≃ₗ[ZMod 3] V) →* (ZMod 3)ˣ).comp (simGroup Q).subtype

private theorem sec5sq_det_orthToSim (g : OGroup Q) :
    sec5sq_det Q (orthToSim Q g) = QuadraticMap.orthogonalDet Q g := by
  rw [QuadraticMap.orthogonalDet_apply]
  rfl

private theorem sec5sq_unit_sq (u : (ZMod 3)ˣ) : u * u = 1 := by
  revert u
  decide

private theorem sec5sq_det_omega (hQ : Q.Nondegenerate) {ω : OGroup Q}
    (hω : ω ∈ omegaGroup hQ) : QuadraticMap.orthogonalDet Q ω = 1 := by
  exact congrArg Prod.fst ((mem_omegaGroup_iff hQ).mp hω)

theorem sec5sq_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {t₀ : OGroup Q} (h0 : t₀ * t₀ = 1) (h01 : invDim t₀ = 1) {ω : OGroup Q}
    (hω : ω ∈ omegaGroup hQ) (x : simGroup Q) :
    (QuotientGroup.mk x : ProjSim Q) * QuotientGroup.mk x ≠
      projOrthToProjSim Q (toProj Q (t₀ * ω)) := by
  intro hEq
  rw [projOrthToProjSim_toProj, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hEq
  have hxx : sec5sq_det Q (x * x) = 1 := by
    rw [map_mul]
    exact sec5sq_unit_sq _
  have hdet : sec5sq_det Q (orthToSim Q (t₀ * ω)) = -1 := by
    rw [sec5sq_det_orthToSim, map_mul, orthogonalDet_involution h0, h01, sec5sq_det_omega hQ hω]
    simp
  rcases mem_piSim_iff.mp hEq with h | h
  · have h' := congrArg (sec5sq_det Q) h
    rw [map_mul, map_inv, hxx, hdet, map_one] at h'
    revert h'
    decide
  · have h' := congrArg (sec5sq_det Q) h
    rw [map_mul, map_inv, hxx, hdet, sec5sq_det_orthToSim, orthogonalDet_piOrth, hdim] at h'
    revert h'
    decide

theorem sec5sq_not_sq (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOm6Z2 L) {σ : G} (hσN : σ ∈ normalizer (L : Set G))
    (hσ : ∃ α : ℤˣ, InducesTypeSome L σ 6 (-1) 1 α) {y : G}
    (hyN : y ∈ normalizer (L : Set G)) {l : G} (hl : l ∈ L) : y * y ≠ σ * l := by
  obtain ⟨α, hα⟩ := hσ
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hdim, hsgn⟩
  have hlN : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
  let Φ := ffInducesHom hm e (L := L)
  obtain ⟨t₀, h0, h01, h0Φ⟩ := simHasDim_of_inducesTypeSome hm e hσN hα
  have hΦl : Φ ⟨l, hlN⟩ =
      projOrthToProjSim Q (toProj Q ((φ ⟨l, hl⟩ : omegaGroup hQ) : OGroup Q)) := by
    rw [show Φ ⟨l, hlN⟩ = ffInducesHom hm e ⟨(⟨l, hl⟩ : ↥L), hlN⟩ from rfl,
      ffInducesHom_of_mem hm e ⟨l, hl⟩ hlN, he]
    rfl
  intro hyy
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Φ ⟨y, hyN⟩)
  have hΦ : Φ ⟨y, hyN⟩ * Φ ⟨y, hyN⟩ = Φ ⟨σ, hσN⟩ * Φ ⟨l, hlN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (Subtype.ext hyy)
  have hEq : (QuotientGroup.mk x : ProjSim Q) * QuotientGroup.mk x =
      projOrthToProjSim Q (toProj Q (t₀ * ((φ ⟨l, hl⟩ : omegaGroup hQ) : OGroup Q))) := by
    simp only [map_mul]
    rw [h0Φ, ← hΦl, hx]
    exact hΦ
  exact sec5sq_model hQ hdim h0 h01 (φ ⟨l, hl⟩).2 x hEq

theorem asc82FactSqReflQ6_of (hS : Asc82SchurU43) : Asc82FactSqReflQ6 := by
  intro G _ _ L z hL _ Q₁ Q₂ hQ₁L hQ₂L _ _ _ _ hcen _ σ hσN _ _ hσ _ y hyN _
  have hzc : z ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [hcen]
    exact Subgroup.mem_zpowers z
  obtain ⟨c, -, hcz⟩ := Subgroup.mem_map.mp hzc
  have hzL : z ∈ L := by
    rw [← hcz]
    exact (sup_le hQ₁L hQ₂L) c.2
  refine ⟨?_, sec5sq_not_sq hS hL hσN hσ hyN hzL⟩
  have h := sec5sq_not_sq hS hL hσN hσ hyN L.one_mem
  rwa [mul_one] at h

end CFSG.OddStandard.SmallF3.Omega
