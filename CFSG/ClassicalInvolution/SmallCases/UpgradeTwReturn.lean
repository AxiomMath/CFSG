module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwDatum
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Datum
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Reduce
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Torus
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Main

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_of_isPComponent_twist_cross (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (reps : List (SignRep t.tag)) {r₀ : ℕ}
    (hB : ∀ i j, t.tag.symmetrizedCartan (t.perm i) (t.perm j) = t.tag.symmetrizedCartan i j)
    (hfix : ∀ r ∈ reps, permChar t.perm (signMaskChar t.tag r.mask) = signMaskChar t.tag r.mask)
    (hrep : ∀ χ, permChar t.perm χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar t.tag r.mask))
    (hunt : ∀ r ∈ reps, UntwistAt (frobTwistGL t.tag k p e (diagramMap t k))
      (signCharTuple (signMaskChar t.tag r.mask)))
    (hθ : ∀ r ∈ reps, ThetaProperties t.perm r₀ (signMaskChar t.tag r.mask) (wordElt t.tag []))
    (hpin : ∀ r ∈ reps, IsTwistPinningNormalization t.tag k p e (signMaskChar t.tag r.mask)
      (thetaMap (wordElt t.tag []) t.perm) (wordWeylMatrix t.tag k [] * diagramMap t k))
    {x : ModGL t.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)))
    (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL t.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)),
        fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p e (diagramMap t k)), fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p e (diagramMap t k))⁆ ⊓ Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hodd₂ : Odd (Nat.card F₂))
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ r ∈ reps, ∃ D : OrthogonalSemilinearFixedRootDatum t.tag p k,
      D.χ = signMaskChar t.tag r.mask ∧ D.q = p ^ e ∧
      (∀ β, D.θ (toReal β) = toReal (permLattice t.perm β)) ∧
      ∃ (J' : Set.range D.classOrbit) (O₀ : Set (Fin t.tag.rank → ℤ)),
        O₀ ∈ (D.withOrbit J').orbits ∧ (D.withOrbit J').orbits = {O₀} ∧
          Nat.card F₂ = D.q ^ orbitCard O₀ := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, hcomp⟩ :=
    exists_twisted_toral_reduction p t hp he reps hfix hrep hunt hx hx2
  set χ := signMaskChar t.tag r.mask with hχ
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots χ) with hM_def
  obtain ⟨hJle, hJc⟩ := (hcomp L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  have hD : (adjointGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom =
      adjointGroup t.tag k := map_conj_diagramMap t k (Or.inl rfl)
  have hRfin : Finite (fixedPointsIn (adjointGroup t.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by cases t <;> decide)
      (units_map_entrywiseHom_diagramMap (t := t) (iterateFrobenius k p e))
      (diagramMap_pow_order t k)
  have hMG : M ≤ adjointGroup t.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMFle : fixedPointsIn M F ≤ fixedPointsIn (adjointGroup t.tag k) F :=
    inf_le_inf_right _ hMG
  have hMFfin : Finite (fixedPointsIn M F) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMFle)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact not_isPComponent_of_kernelRoots_eq_empty hne (inf_le_left : fixedPointsIn M F ≤ M)
      _ hJc
  have hA := t.cartan_perm
  have hτ : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 := by cases t <;> simp [TwistTag.tag]
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ := exists_pinned_datum p hp hk he hτ (ρ := t.perm)
    hA hB (hθ r hr) (Q₀ := wordWeylMatrix t.tag k [] * diagramMap t k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX t [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer t))
    (map_conj_wordWeylMatrix_mul [] hD) (hpin r hr) hne
  have hQ₀ : wordWeylMatrix t.tag k [] * diagramMap t k = diagramMap t k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p t he a₀⁻¹
  set u := rootDiagUnit t.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL t.tag k p e (h * diagramMap t k) y = h * F y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff u hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  have hMhfin : Finite (fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k))) := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj u).subgroupMap (fixedPointsIn M F)).toEquiv
  set Mh := fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) with hMh_def
  set X := D.totalFixedGroup with hX_def
  set JD := J.map (MulAut.conj u).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup t.tag k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup t.tag k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro x hx
    have hx' : (x : ModGL t.tag k) ∈ JD := hx
    have hmem : (x : ModGL t.tag k) ∈ X.map (adjointGroup t.tag k).subtype := by
      rw [hX]
      exact hJDle hx'
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup t.tag k).subtype
      (adjointGroup t.tag k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ x : X, ((eX x : Mh) : ModGL t.tag k) = (((x : adjointGroup t.tag k)) :
      ModGL t.tag k) := fun x => rfl
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : (((eX.symm y : X) : adjointGroup t.tag k) : ModGL t.tag k) =
            (y : ModGL t.tag k) := by
          have := heX (eX.symm y)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm y : X) : adjointGroup t.tag k) : ModGL t.tag k) ∈ JD
        rw [this]
        exact hy
      · intro hx
        refine ⟨eX x, ?_, MulEquiv.symm_apply_apply eX x⟩
        change ((eX x : Mh) : ModGL t.tag k) ∈ JD
        rw [heX]
        exact hx
    rwa [h2] at h1
  let φ : Y ≃* J₀ := φ₀.trans ((L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
    ((J.equivMapOfInjective _ (MulAut.conj u).injective).trans
      (Subgroup.subgroupOfEquivOfLe hJDG).symm))
  have hqD : D.q = p ^ e := by
    change p ^ D.e = p ^ e
    rw [hDe]
  obtain ⟨J', O₀, hO₀, hA, hcard⟩ := exists_orbits_singleton_of_isPComponent_cross D hXfin hJ₀X
    hJ₀comp φ O hO hodd₂ eY
  refine ⟨r, hr, D, hDχ, hqD, fun β => ?_, J', O₀, hO₀, hA, hcard⟩
  rw [hDθ β]
  simp [thetaMap, wordElt_nil]

end Main

end CFSG.ClassicalInvolution.Upgrade
