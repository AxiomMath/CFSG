module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem unit_pow_card_sub_one [Finite F] (u : Fˣ) : u ^ (Nat.card F - 1) = 1 := by
  rw [← Nat.card_units]
  exact pow_card_eq_one'

theorem statedScalars_pow_eq_one [Finite F] {g : GL ι F} (hg : g ∈ StatedScalars ι F) :
    g ^ (Nat.card F - 1) = 1 := by
  obtain ⟨u, rfl⟩ := hg
  rw [← map_pow, unit_pow_card_sub_one, map_one]

theorem mk_eq_one_mem_center (H : Subgroup (GL ι F)) {x : H}
    (hx : (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) x = 1) :
    x ∈ Subgroup.center H := by
  have hx' : (x : GL ι F) ∈ StatedScalars ι F :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hx)
  have hc : (x : GL ι F) ∈ Subgroup.center (GL ι F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx'
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.1 hc g)

theorem mk_eq_one_pow [Finite F] (H : Subgroup (GL ι F)) {x : H}
    (hx : (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) x = 1) :
    x ^ (Nat.card F - 1) = 1 := by
  have hx' : (x : GL ι F) ∈ StatedScalars ι F :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hx)
  exact Subtype.ext (statedScalars_pow_eq_one hx')

theorem borelQuotient_of_stated [Finite F] [CharP F 2] {H : Subgroup (GL ι F)} {Y : Type}
    [Group Y] (e : Y ≃* StatedProj H) {D : UniversalRootDatum ↥H} {n : Fin D.rank → ↥H}
    {T : Fin D.rank → Subgroup ↥H}
    (ct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n T)
    (extras : SteinbergExtras D n T) (pGroup : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (torus_pow : ∀ i, ∀ g ∈ T i, g ^ (Nat.card F - 1) = 1) :
    BorelQuotient D n T (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (Nat.card F - 1) where
  ct := ct
  extras := extras
  pGroup := pGroup
  surj := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  odd := odd_card_sub_one F
  torus_pow := torus_pow
  ker_central := fun z hz => mk_eq_one_mem_center H (e.symm.injective (by simpa using hz))
  ker_pow := fun z hz => mk_eq_one_pow H (e.symm.injective (by simpa using hz))

end Stated

end CFSG.AGLEmbedding.ParabHub
