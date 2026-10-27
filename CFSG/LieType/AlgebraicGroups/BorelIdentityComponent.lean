module

public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupComponent
public import CFSG.LieType.AlgebraicGroups.ConeIncidence
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem geometricallySolvable_of_isSolvable_points (Q : _root_.CommHopfAlgCat.{u} k)
    (hQ : Group.IsSolvable (WithConv (Q →ₐ[k] k))) :
    TauCeti.geometricallySolvablePointsCommHopfAlgProperty k Q := by
  rw [TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff]
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := AlgebraicClosure k)
  let e : k ≃ₐ[k] AlgebraicClosure k := AlgEquiv.ofBijective (Algebra.ofId k _) hb
  refine Group.isSolvable_of_surjective
    (f := TauCeti.AlgHom.mapValue (H := Q) (e : k →ₐ[k] AlgebraicClosure k)) ?_
  intro p
  refine ⟨toConv ((e.symm : AlgebraicClosure k →ₐ[k] k).comp p.ofConv), ?_⟩
  rw [TauCeti.AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.comp_assoc]
  simp

variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)

theorem isBorelCandidate_closureIdentityComponent (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hsol : Group.IsSolvable P)
    (hclosed : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj
      (TauCeti.HopfIdeal.vanishingIdeal P) (CommAlgCat.of k k) ≤ P) :
    TauCeti.HopfIdeal.IsBorelCandidate k H (closureIdentityComponent H P) := by
  let QC := TauCeti.FiniteTypeCommHopfAlgCat.quotient H (closureIdentityComponent H P)
  let : IsDomain QC := isDomain_quotient_closureIdentityComponent H P
  refine TauCeti.HopfIdeal.IsBorelCandidate.mk ?_ ?_ ?_
  · exact TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _
  · exact (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
      inferInstance
  · apply geometricallySolvable_of_isSolvable_points
    let ψ := (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj (closureIdentityComponent H P)
      (CommAlgCat.of k k)).hom
    have hψ : Function.Injective ψ :=
      TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj _ (CommAlgCat.of k k)
    have hmem : ∀ q, ψ q ∈ P := fun q =>
      hclosed (quotientPointsSubgroup_closureIdentityComponent_le H P ⟨q, rfl⟩)
    exact Group.isSolvable_of_isSolvable_injective (f := ψ.codRestrict P hmem)
      (fun a b h => hψ (congrArg Subtype.val h))

theorem closureIdentityComponent_eq_of_isBorelOverAlgClosed (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B) (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hBP : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) ≤ P)
    (hsol : Group.IsSolvable P)
    (hclosed : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj
      (TauCeti.HopfIdeal.vanishingIdeal P) (CommAlgCat.of k k) ≤ P) :
    closureIdentityComponent H P = B := by
  have hcand := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H B).mp hB).2
  have hcB := (TauCeti.HopfIdeal.isBorelCandidate_iff k H B).mp hcand.1
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H B
  let : Algebra.Smooth k Q := (TauCeti.smoothCommHopfAlgProperty_iff _).mp hcB.1
  let : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  let : ConnectedSpace (PrimeSpectrum Q) :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mp hcB.2.1
  have hle : closureIdentityComponent H P ≤ B := closureIdentityComponent_le H hBP
  exact le_antisymm hle
    (hcand.2 (isBorelCandidate_closureIdentityComponent H P hsol hclosed) hle)

theorem relIndex_ne_zero_of_isBorelOverAlgClosed (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B) (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hBP : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) ≤ P)
    (hsol : Group.IsSolvable P)
    (hclosed : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj
      (TauCeti.HopfIdeal.vanishingIdeal P) (CommAlgCat.of k k) ≤ P) :
    (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k)).relIndex P ≠ 0 := by
  rw [← closureIdentityComponent_eq_of_isBorelOverAlgClosed H B hB P hBP hsol hclosed]
  exact relIndex_closureIdentityComponent_ne_zero H P

omit [IsAlgClosed k] in
theorem quotientPointsSubgroup_vanishingIdeal_le_of_forall_iff
    (P : Subgroup (WithConv (H →ₐ[k] k))) (J : Ideal H)
    (hJ : ∀ g, g ∈ P ↔ ∀ a ∈ J, g.ofConv a = 0) :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (TauCeti.HopfIdeal.vanishingIdeal P)
      (CommAlgCat.of k k) ≤ P := by
  intro g hg
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg
  refine (hJ g).mpr fun a ha => hg a ?_
  rw [TauCeti.HopfIdeal.mem_vanishingIdeal]
  exact fun p => (hJ p.val).mp p.2 a ha

theorem exists_ideal_forall_iff_mem_span_self {W : Type u} [AddCommGroup W] [Module k W]
    [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W} (hw₁ : w₁ ≠ 0) :
    ∃ J : Ideal H, ∀ g : WithConv (H →ₐ[k] k), (∀ a ∈ J, g.ofConv a = 0) ↔
      TauCeti.Comodule.basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁ := by
  have hX := ClosedCone.isZariskiClosed_submodule (k := k) (k ∙ w₁)
  have hc : ClosedCone.IsCone k ((k ∙ w₁ : Submodule k W) : Set W) :=
    fun c x hx => Submodule.smul_mem _ c hx
  obtain ⟨J, hJ⟩ := ClosedCone.exists_ideal_forall_iff_exists_mem_span (H := H) hX hc
  refine ⟨J, fun g => (hJ g).trans ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, hx0, hgx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx0 (zero_smul k w₁)
    rw [map_smul, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0),
      Submodule.smul_mem_iff _ hc0] at hgx
    exact hgx
  · exact fun hg => ⟨w₁, Submodule.mem_span_singleton_self w₁, hw₁, hg⟩

theorem relIndex_ne_zero_of_isBorelOverAlgClosed_of_lineStabilizer {W : Type u} [AddCommGroup W]
    [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W} (hw₁ : w₁ ≠ 0)
    (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ TauCeti.Comodule.basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁)
    (B : TauCeti.HopfIdeal k H) (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B)
    (hBP : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) ≤ P)
    (hsol : Group.IsSolvable P) :
    (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k)).relIndex P ≠ 0 := by
  obtain ⟨J, hJ⟩ := exists_ideal_forall_iff_mem_span_self H hw₁
  exact relIndex_ne_zero_of_isBorelOverAlgClosed H B hB P hBP hsol
    (quotientPointsSubgroup_vanishingIdeal_le_of_forall_iff H P J fun g => (hP g).trans (hJ g).symm)


end CFSG.LieType.AlgebraicGroups.TorusConjugacy
