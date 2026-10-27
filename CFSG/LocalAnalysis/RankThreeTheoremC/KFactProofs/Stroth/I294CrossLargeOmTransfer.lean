module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Module QuadraticMap
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega

namespace I294Large

theorem CommOrRank.of_projOmega {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : CommOrRank p ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :
    CommOrRank p (StatedProj (StatedOmega Q₀)) := by
  classical
  obtain ⟨-, -, -, -, -, hsq', -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun g =>
    mem_commutator_of_coe_mem (by simpa using hsq' (g : (ι → F) ≃ₗ[F] (ι → F)) g.2)
  haveI : Nontrivial (ι → F) := by
    obtain ⟨T, hT3, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    have := Submodule.finrank_le T
    omega
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO'
  let Θ₁ : ↥O →* GL ι F := (toLinEquiv ι F).symm.toMonoidHom.comp O.subtype
  have hΘ₁ : ∀ x : ↥O, toLinEquiv ι F (Θ₁ x) = (x : (ι → F) ≃ₗ[F] (ι → F)) := fun x =>
    MulEquiv.apply_symm_apply _ _
  have hmemΩ : ∀ A : GL ι F, A ∈ StatedOmega Q₀ ↔ toLinEquiv ι F A ∈ ⁅O, O⁆ := fun A => by
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    rfl
  have hΘ₁Ω : ∀ x ∈ commutator ↥O, Θ₁ x ∈ StatedOmega Q₀ := by
    intro x hx
    rw [hmemΩ, hΘ₁]
    have : (x : (ι → F) ≃ₗ[F] (ι → F)) ∈ (commutator ↥O).map O.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at this
  let Θ₂ : ↥(commutator ↥O) →* ↥(StatedOmega Q₀) :=
    (Θ₁.comp (commutator ↥O).subtype).codRestrict (StatedOmega Q₀) (fun x => hΘ₁Ω x x.2)
  let pj : ↥(commutator ↥O) →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀))).comp Θ₂
  have hker : ∀ x : ↥(commutator ↥O), pj x = 1 → x ^ 2 = 1 := by
    intro x hx
    have h1 : Θ₂ x ∈ (StatedScalars ι F).subgroupOf (StatedOmega Q₀) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : ↥O) : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) := by
      have := (mem_statedScalars_iff _).1 h1
      rwa [show ((Θ₂ x : ↥(StatedOmega Q₀)) : GL ι F) = Θ₁ (x : ↥O) from rfl, hΘ₁] at this
    obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc, hcv⟩ :=
      CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars h2 (x : ↥O).2 ha₀
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply, hcv v, map_smul, hcv v, smul_smul, ← _root_.sq, hc,
      one_smul]
    rfl
  have hsurj : Function.Surjective pj := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : toLinEquiv ι F (z : GL ι F) ∈ ⁅O, O⁆ := (hmemΩ _).1 z.2
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : Θ₂ ⟨x, hx⟩ = z := Subtype.ext (by
      show Θ₁ x = (z : GL ι F)
      apply (toLinEquiv ι F).injective
      rw [hΘ₁]
      exact hxz)
    show QuotientGroup.mk' _ (Θ₂ ⟨x, hx⟩) = _
    rw [h1]
    rfl
  have hN : CommOrRank p ↥(commutator ↥O) :=
    CommOrRank.of_normal_coprime_index hp (commutator ↥O)
      (not_dvd_index_commutator_of_sq hp hp2 hsq) hO
  exact CommOrRank.of_surjective_coprime_ker hp pj hsurj
    (not_dvd_card_ker_of_sq hp hp2 pj hker) hN

end I294Large

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
