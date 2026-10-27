module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinWeyl
public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.LocalTwinDict
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (conjSub modelUniv centralizingMembers ConjInvariant)

variable {p f : ℕ} [Fact p.Prime]

theorem map_conj_map_hom {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y) (k : X) (S : Subgroup X) :
    (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom = (conjSub k S).map ψ := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem exists_adapted_y_of_reach {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    {t : G} (ht : t * z * t⁻¹ = z) (v : Fin Y.D.rank → ZMod 2)
    (hT : ∀ γ ∈ Y.D.roots, (∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ,
      Gaps.locAut hΩ ht x = x) ↔ charOf v γ = 0)
    {w : Fin Y.D.rank → ZMod 2} (hw : CharReach Y.D.cartan v w)
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), Gaps.locAut hΩ ht x = x) ↔ w a = 0) := by
  obtain ⟨W₀, k, hk, hW₀⟩ := exists_actsAs_of_charReach hct hw
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ψ k)
  refine ⟨(y : G), y.2, fun a => ?_⟩
  have hroot : weylAction Y.D.isFiniteType W₀ (Pi.single a 1) ∈ Y.D.roots :=
    weylAction_mem_roots _ W₀ (single_mem_roots _ a)
  have himg : locImg Ω z (conjSub (y : G) (j a)) =
      (Y.D.rootGroup (weylAction Y.D.isFiniteType W₀ (Pi.single a 1)) ⊔
        Y.D.rootGroup (-weylAction Y.D.isFiniteType W₀ (Pi.single a 1))).map ψ := by
    rw [Gaps.locImg_conjSub_layer, hjimg a, show Gaps.locMk Ω z y = ψ k from hy,
      map_conj_map_hom]
    congr 1
    exact conjSub_rankOne_of_actsAs hk (single_mem_roots _ a)
      (CFSG.Timmesfeld.LevisExtras.neg_mem_roots (single_mem_roots _ a))
  rw [himg, hT _ hroot, hW₀ a]

theorem exists_adapted_y {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    (hPat : PatternLemma Y.D.cartan) {t : G} (ht : t * z * t⁻¹ = z)
    (v : Fin Y.D.rank → ZMod 2) (hv : v ≠ 0)
    (hT : ∀ γ ∈ Y.D.roots, (∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ,
      Gaps.locAut hΩ ht x = x) ↔ charOf v γ = 0)
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∃ p₀ : Fin Y.D.rank, ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), Gaps.locAut hΩ ht x = x) ↔ a ≠ p₀) := by
  obtain ⟨w, hw, p₀, rfl⟩ := hPat v hv
  obtain ⟨y, hy, h⟩ := exists_adapted_y_of_reach hΩ ψ hct ht v hT hw hjimg
  refine ⟨y, hy, p₀, fun a => ?_⟩
  rw [h a, Pi.single_apply]
  by_cases hap : a = p₀
  · simp [hap]
  · simp [hap]

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
  {tY : StatedLieTag} {nY : ℕ}

omit [Finite G] in
theorem exists_adapted_y_of_reach (c : TCtx p f tY nY Ω K z)
    {n : Fin (modelUniv tY nY p f Fact.out).D.rank → (modelUniv tY nY p f Fact.out).K}
    {H : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup (modelUniv tY nY p f Fact.out).K}
    (hct : IsCTGroupDatum
      (coxeterMatrix (modelUniv tY nY p f Fact.out).D.isFiniteType).toCoxeterSystem
      (weylAction (modelUniv tY nY p f Fact.out).D.isFiniteType)
      (modelUniv tY nY p f Fact.out).D.roots (modelUniv tY nY p f Fact.out).D.rootGroup n H)
    {t : G} (ht : t * z * t⁻¹ = z)
    (v : Fin (modelUniv tY nY p f Fact.out).D.rank → ZMod 2)
    (hT : ∀ γ ∈ (modelUniv tY nY p f Fact.out).D.roots,
      (∀ x ∈ ((modelUniv tY nY p f Fact.out).D.rootGroup γ ⊔
          (modelUniv tY nY p f Fact.out).D.rootGroup (-γ)).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)
    {w : Fin (modelUniv tY nY p f Fact.out).D.rank → ZMod 2}
    (hw : CharReach (modelUniv tY nY p f Fact.out).D.cartan v w)
    {j : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv tY nY p f Fact.out).D.rootGroup a).map c.d.ψ) :
    ∃ y ∈ locLayer Ω z, ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔
        w a = 0) :=
  CFSG.ClassicalInvolution.RouteD.exists_adapted_y_of_reach c.hΩ.conjInvariant c.d.ψ hct ht v hT hw
    hjimg

end TCtx

end CFSG.ClassicalInvolution.RouteD
