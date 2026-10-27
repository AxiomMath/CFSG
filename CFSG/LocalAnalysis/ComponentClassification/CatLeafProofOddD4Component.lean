module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddDatum

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

theorem exists_SL2_surjective_of_d4_involution_component
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.D4.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ (F₂ : Type) (_ : Field F₂) (_ : Finite F₂) (d : ℕ), (d = 1 ∨ d = 3) ∧
      Nat.card F₂ = (p ^ e) ^ d ∧ ∃ f : SL(2, F₂) →* L, Function.Surjective f := by
  classical
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, hcomp⟩ := exists_twisted_toral_reduction p
    TwistTag.D4 hp he d4SignDiagramReps h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e) hx hx2
  have hrm : r.mask = 4 := by
    rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
      rfl | hr'
    · exfalso
      apply hx1
      have h0 : signMaskTuple TwistTag.D4.tag k 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : g₁ * x * g₁⁻¹ = 1 := by
        rw [hg₁x]
        change rootDiagUnit TwistTag.D4.tag
          (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
        rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
      exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
    · obtain rfl := List.mem_singleton.1 hr'
      rfl
  set χ := signMaskChar TwistTag.D4.tag r.mask with hχ
  set F := frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) with hF
  set M := torusGroup TwistTag.D4.tag k ⊔ rootSpan TwistTag.D4.tag k (kernelRoots χ) with hM_def
  obtain ⟨hJle, hJc⟩ := (hcomp L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  have hD : (adjointGroup TwistTag.D4.tag k).map
      (MulAut.conj (diagramMap TwistTag.D4 k)).toMonoidHom = adjointGroup TwistTag.D4.tag k :=
    map_conj_diagramMap TwistTag.D4 k (Or.inl rfl)
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.D4.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)
  have hMG : M ≤ adjointGroup TwistTag.D4.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMFle : fixedPointsIn M F ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F :=
    inf_le_inf_right _ hMG
  have hMFfin : Finite (fixedPointsIn M F) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMFle)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact not_isPComponent_of_kernelRoots_eq_empty hne (inf_le_left : fixedPointsIn M F ≤ M)
      _ hJc
  have hθ : ThetaProperties TwistTag.D4.perm 3 χ (wordElt TwistTag.D4.tag []) :=
    h4.theta r hr [] (nil_mem_omegaWords_d4 hr)
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ := exists_pinned_datum p hp hk he
    (τ := TwistTag.D4.tag) (Or.inl rfl) (ρ := TwistTag.D4.perm) (TwistTag.cartan_perm .D4)
    symmetrizedCartan_perm_D4 hθ
    (Q₀ := wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer TwistTag.D4))
    (map_conj_wordWeylMatrix_mul [] hD) (n4 r hr [] (nil_mem_omegaWords_d4 hr)) hne
  have hQ₀ : wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k =
      diagramMap TwistTag.D4 k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p TwistTag.D4 he a₀⁻¹
  set u := rootDiagUnit TwistTag.D4.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k) y =
      h * F y * h⁻¹ := fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff u hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  have hMhfin : Finite (fixedPointsIn M
      (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k))) := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj u).subgroupMap (fixedPointsIn M F)).toEquiv
  set Mh := fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k))
    with hMh_def
  set X := D.totalFixedGroup with hX_def
  set JD := J.map (MulAut.conj u).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup TwistTag.D4.tag k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup TwistTag.D4.tag k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro x hx
    have hx' : (x : ModGL TwistTag.D4.tag k) ∈ JD := hx
    have hmem : (x : ModGL TwistTag.D4.tag k) ∈ X.map (adjointGroup TwistTag.D4.tag k).subtype := by
      rw [hX]
      exact hJDle hx'
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup TwistTag.D4.tag k).subtype
      (adjointGroup TwistTag.D4.tag k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ x : X, ((eX x : Mh) : ModGL TwistTag.D4.tag k) =
      (((x : adjointGroup TwistTag.D4.tag k)) : ModGL TwistTag.D4.tag k) := fun x => rfl
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) : ModGL TwistTag.D4.tag k) =
            (y : ModGL TwistTag.D4.tag k) := by
          have := heX (eX.symm y)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) :
          ModGL TwistTag.D4.tag k) ∈ JD
        rw [this]
        exact hy
      · intro hx
        refine ⟨eX x, ?_, MulEquiv.symm_apply_apply eX x⟩
        change ((eX x : Mh) : ModGL TwistTag.D4.tag k) ∈ JD
        rw [heX]
        exact hx
    rwa [h2] at h1
  have hqD : D.q = p ^ e := by
    change p ^ D.e = p ^ e
    rw [hDe]
  have hθD : ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt TwistTag.D4.tag []) := by
    rw [hDχ]
    exact hθ
  obtain ⟨J', hJ', -⟩ := exists_eq_orbitGroupC_of_isPComponent D hXfin hJ₀X hJ₀comp
  obtain ⟨O₀, hA⟩ : ∃ O₀ : Set (Fin TwistTag.D4.tag.rank → ℤ),
      (D.withOrbit J').orbits = {O₀} := d4_orbits_eq_singleton D (by rw [hDχ, hχ, hrm]; rfl) J'
  have hO₀ : O₀ ∈ (D.withOrbit J').orbits := hA ▸ Set.mem_singleton O₀
  have hqD' : (D.withOrbit J').q = p ^ e := hqD
  have hsurj := (D.withOrbit J').orbitGroupHom_surjective hO₀ hA
  have hcardK := (D.withOrbit J').card_orbitField hO₀
  have hfinK := CFSG.ComponentClassification.ExcSelector.finite_orbitField' (D.withOrbit J') hO₀
  have hd := orbitCard_eq_of_thetaProperties (D.withOrbit J') hθD hDθ hO₀
  let eL : L ≃* J₀ := (L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
    ((J.equivMapOfInjective _ (MulAut.conj u).injective).trans
      (Subgroup.subgroupOfEquivOfLe hJDG).symm)
  let eC : (D.withOrbit J').orbitGroupC ≃* (D.withOrbit J').orbitGroup :=
    Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup
  let eJ : J₀ ≃* (D.withOrbit J').orbitGroup := (MulEquiv.subgroupCongr hJ').trans eC
  exact ⟨_, inferInstance, hfinK, orbitCard O₀, hd, by rw [hcardK, hqD'],
    (eL.trans eJ).symm.toMonoidHom.comp ((D.withOrbit J').orbitGroupHom hO₀),
    (eL.trans eJ).symm.surjective.comp hsurj⟩

end CFSG.ComponentClassification.CatLeafProof
