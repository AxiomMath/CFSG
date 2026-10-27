module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactPiece

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll twistedFix mem_twistedFix)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective)

section Generic

variable {S M : Type*} [Group S] [Group M] {ι : Type*}

theorem map_perfectCore_fixAll_of_surjective [Finite S] [Finite M] (π : S →* M)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center S) (α : ι → MulAut S)
    (β : ι → MulAut M) (hαβ : ∀ i x, π (α i x) = β i (π x)) :
    (perfectCore (fixAll α)).map π = perfectCore (fixAll β) := by
  have htw : twistedFix α π.ker hker = (fixAll β).comap π := by
    ext x
    rw [mem_twistedFix, mem_comap, mem_fixAll]
    refine forall_congr' fun i => ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, mul_inv_eq_one]
  rw [← LinearPilot.perfectCore_twistedFix α π.ker hker, htw, CFSG.Quasithin.map_perfectCore,
    map_comap_eq_self_of_surjective hπ]

variable {G : Type*} [Group G]

theorem map_centralizerPerfectCore_subgroupOf_eq [Finite G] [Finite M] {X T : Subgroup G}
    (hXT : X ≤ T) (π : centralizerPerfectCore X →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (centralizerPerfectCore X))
    (α : T → MulAut (centralizerPerfectCore X))
    (hα : ∀ (d : T) (x : centralizerPerfectCore X), ((α d x : centralizerPerfectCore X) : G) =
      (d : G) * x * (d : G)⁻¹)
    (β : T → MulAut M) (hαβ : ∀ d x, π (α d x) = β d (π x)) :
    ((centralizerPerfectCore T).subgroupOf (centralizerPerfectCore X)).map π =
      perfectCore (fixAll β) := by
  have h1 := LinearPilot.centralizerPerfectCore_eq_map_of_le (centralizerPerfectCore X).subtype
    (by rw [(MonoidHom.ker_eq_bot_iff _).2 (centralizerPerfectCore X).subtype_injective]
        exact bot_le)
    hXT (range_subtype _) α hα
  have h2 : (centralizerPerfectCore T).subgroupOf (centralizerPerfectCore X) =
      perfectCore (fixAll α) := by
    rw [h1, subgroupOf, comap_map_eq_self_of_injective (centralizerPerfectCore X).subtype_injective]
  rw [h2, map_perfectCore_fixAll_of_surjective π hπ hker α β hαβ]

end Generic

section Frame

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d} (h : IsHypFrame Q a b)
  (e : L ≃* matrixProjectiveDerived Q)

include h in
theorem modelToG_frameTorusOf_le_centralizer (P P' : Subgroup (Fin m → Kˣ)) :
    modelToG e (frameTorusOf Q a b P) ≤
      centralizer (modelToG e (frameTorusOf Q a b P') : Set G) :=
  UnitaryPilot.modelToG_le_centralizer e (h.frameTorusOf_le_centralizer P P')

include h in
theorem mem_normalizer_centralizerPerfectCore_of_mem_frame {P : Subgroup (Fin m → Kˣ)}
    {X : Subgroup G} (hXP : X ≤ modelToG e (frameTorusOf Q a b P)) {g : G}
    (hg : g ∈ modelToG e (frameTorusOf Q a b P)) :
    g ∈ normalizer (centralizerPerfectCore X : Set G) := by
  have hc : g ∈ centralizer (X : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_iff.1 (modelToG_frameTorusOf_le_centralizer h e P P hg) x (hXP hx)
  exact F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
    (Subgroup.centralizer_le_normalizer _ hc)

variable [Finite G] {F : Type} [Field F] [Finite F]

theorem map_frameCore_eq_of_conjDiag_quot {m' : ℕ} (δ : (Fin m → Kˣ) →* GL (Fin m' ⊕ Fin m') F)
    (hδ : ∀ t, δ t ∈ normalizer (StatedOmega (StatedQuadPlus m' F) : Set (GL (Fin m' ⊕ Fin m') F)))
    {P : Subgroup (Fin m → Kˣ)} {X : Subgroup G} (hXP : X ≤ modelToG e (frameTorusOf Q a b P))
    (π : centralizerPerfectCore X →* StatedOmega (StatedQuadPlus m' F))
    (hπ : Function.Surjective π) (hker : π.ker ≤ center (centralizerPerfectCore X))
    (hequiv : ∀ t ∈ P, ∀ (hn : ((e.symm (h.frameHom t) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G)) (x : centralizerPerfectCore X),
      π ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hn⟩ x) =
        (StatedOmega (StatedQuadPlus m' F)).normalizerMonoidHom ⟨δ t, hδ t⟩ (π x)) :
    (((centralizerPerfectCore (modelToG e (frameTorusOf Q a b P))).subgroupOf
        (centralizerPerfectCore X)).map π).map (StatedOmega (StatedQuadPlus m' F)).subtype =
      perfectCore (StatedOmega (StatedQuadPlus m' F) ⊓
        centralizer (δ '' (P : Set (Fin m → Kˣ)))) := by
  set T := modelToG e (frameTorusOf Q a b P)
  let τ : T → Fin m → Kˣ := fun x => (exists_param_of_mem_modelToG_frameTorusOf h e x.2).choose
  have hτ : ∀ x : T, τ x ∈ P ∧ ((e.symm (h.frameHom (τ x)) : L) : G) = x :=
    fun x => (exists_param_of_mem_modelToG_frameTorusOf h e x.2).choose_spec
  have hN : ∀ g : T, (g : G) ∈ normalizer (centralizerPerfectCore X : Set G) :=
    fun g => mem_normalizer_centralizerPerfectCore_of_mem_frame h e hXP g.2
  let α : T → MulAut (centralizerPerfectCore X) := fun g =>
    (centralizerPerfectCore X).normalizerMonoidHom ⟨g, hN g⟩
  let β : T → MulAut (StatedOmega (StatedQuadPlus m' F)) := fun g =>
    (StatedOmega (StatedQuadPlus m' F)).normalizerMonoidHom ⟨δ (τ g), hδ (τ g)⟩
  have hαβ : ∀ g x, π (α g x) = β g (π x) := by
    intro g x
    have hn : ((e.symm (h.frameHom (τ g)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G) := by
      rw [(hτ g).2]
      exact hN g
    have hg : (⟨(g : G), hN g⟩ : normalizer (centralizerPerfectCore X : Set G)) =
        ⟨((e.symm (h.frameHom (τ g)) : L) : G), hn⟩ := Subtype.ext (hτ g).2.symm
    change π ((centralizerPerfectCore X).normalizerMonoidHom ⟨g, hN g⟩ x) = _
    rw [hg]
    exact hequiv (τ g) (hτ g).1 hn x
  rw [map_centralizerPerfectCore_subgroupOf_eq hXP π hπ hker α (fun _ _ => rfl) β hαβ,
    CFSG.Quasithin.map_perfectCore, map_fixAll_normalizerMonoidHom_eq_frame h e δ hδ τ hτ]

end Frame

end CFSG.SeitzReduction.OmegaPilot
