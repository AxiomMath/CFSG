module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeOrbitMap
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeCheck
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeDatum

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Orbits

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p k)

theorem thetaOrbit_eq_iterOrbit {ρ : Equiv.Perm (Fin τ.rank)} {ω : WeylGroup τ}
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap ω ρ γ)) (α : Fin τ.rank → ℤ) :
    thetaOrbit D.θ α = iterOrbit (thetaMap ω ρ) α := by
  have hpow : ∀ m : ℕ, ∀ α : Fin τ.rank → ℤ,
      (D.θ ^ m) (toReal α) = toReal ((thetaMap ω ρ)^[m] α) := by
    intro m
    induction m with
    | zero => intro α; simp
    | succ m ih =>
      intro α
      rw [pow_succ', Module.End.mul_apply, ih, hDθ, Function.iterate_succ_apply']
  ext β
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, toReal_injective ((hpow m α).symm.trans hm)⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, hpow m α⟩

theorem orbitCard_eq_of_thetaProperties {ρ : Equiv.Perm (Fin τ.rank)} {r : ℕ} {ω : WeylGroup τ}
    (hθ : ThetaProperties ρ r D.χ ω) (hDθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap ω ρ γ))
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) : orbitCard O = 1 ∨ orbitCard O = r := by
  have h := hθ.ncard_iterOrbit _ (D.orbitRoot_mem_kernelRoots hO)
  rw [← thetaOrbit_eq_iterOrbit D hDθ, ← D.eq_thetaOrbit_orbitRoot hO] at h
  exact h

end Orbits

section Classes

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem d4_orbits_eq_singleton (D : OrthogonalSemilinearFixedRootDatum Tag.D4 p k)
    (hχ : D.χ = signMaskChar Tag.D4 4) (J' : Set.range D.classOrbit) :
    ∃ O₀, (D.withOrbit J').orbits = {O₀} := by
  have key : ∀ χ' : Multiplicative (Fin Tag.D4.rank → ℤ) →* ℤˣ, χ' = signMaskChar Tag.D4 4 →
      ∀ a b : kernelRoots χ', (⟦a⟧ : KernelComponent χ') = ⟦b⟧ →
        (b : Fin Tag.D4.rank → ℤ) = a ∨ (b : Fin Tag.D4.rank → ℤ) = -a := by
    rintro χ' rfl
    exact d4_hclass_four
  exact orbits_eq_singleton_of_forall_class (D.withOrbit J') fun a b hab => key D.χ hχ a b hab

end Classes

section Main

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem d4_exists_conj_eq_fixedTriple (hp : p ≠ 2)
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
        Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal]
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = (p ^ e) ^ 3)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ g₁ ∈ adjointGroup TwistTag.D4.tag k,
      frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) g₁ = g₁ ∧
      ∃ β : Fin d4.rank → ℤ, IsRoot d4 β ∧ rho β ≠ β ∧
        L = (fixedPointsIn (tripleGroup k β)
            (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) ⊔
          fixedPointsIn (tripleGroup k (-β))
            (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))).map
              (MulAut.conj g₁⁻¹).toMonoidHom := by
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
  let φ : Y ≃* J₀ := φ₀.trans ((L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
    ((J.equivMapOfInjective _ (MulAut.conj u).injective).trans
      (Subgroup.subgroupOfEquivOfLe hJDG).symm))
  have hqD : D.q = p ^ e := by
    change p ^ D.e = p ^ e
    rw [hDe]
  have hθD : ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt TwistTag.D4.tag []) := by
    rw [hDχ]
    exact hθ
  have hsize : ∀ J' : Set.range D.classOrbit, ∀ O ∈ (D.withOrbit J').orbits, orbitCard O ≤ 3 := by
    intro J' O' hO'
    rcases orbitCard_eq_of_thetaProperties (D.withOrbit J') hθD hDθ hO' with h1 | h1 <;> omega
  obtain ⟨J', O₀, hO₀, hA, h3, hJ⟩ := exists_eq_range_orbitMapHom_of_isPComponent_cube D hXfin
    (d4_orbits_eq_singleton D (by rw [hDχ, hχ, hrm]; rfl)) hsize hJ₀X hJ₀comp φ O (F₂ := F₂)
    (by rw [hF₂, hqD]) eY
  have hθρ : ∀ γ, D.θ (toReal γ) = toReal (rho γ) := by
    intro γ
    have h1 := hDθ γ
    rwa [wordElt_nil, thetaMap_one] at h1
  have hJF : ∀ y ∈ J, F y = y := fun y hy => (mem_fixedPointsIn.1 (hJle hy)).2
  have hJiff : ∀ y, y ∈ J.map (MulAut.conj u).toMonoidHom ↔
      ∃ A, y = (D.withOrbit J').orbitMapHom hO₀ A := by
    intro y
    constructor
    · intro hy
      have hyG : y ∈ adjointGroup TwistTag.D4.tag k := hJDG hy
      have h1 : (⟨y, hyG⟩ : adjointGroup TwistTag.D4.tag k) ∈ J₀ := hy
      rw [hJ, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
      obtain ⟨A, hA'⟩ := h1
      exact ⟨A, hA'.symm⟩
    · rintro ⟨A, rfl⟩
      have hyG := (D.withOrbit J').orbitMap_mem_adjointGroup O₀ A
      have h1 : (⟨_, hyG⟩ : adjointGroup TwistTag.D4.tag k) ∈ J₀ := by
        rw [hJ, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
        exact ⟨A, rfl⟩
      exact h1
  obtain ⟨β, hβ, hne', hJS⟩ := eq_fixedPointsIn_tripleGroup_sup_of_orbit (D := D.withOrbit J') he
    hDe hθρ hO₀ h3 s hJF hJiff
  refine ⟨g₁, hg₁G, hFg₁, β, hβ, hne', ?_⟩
  rw [← hJS, hJ_def, Subgroup.map_map]
  have hid : (MulAut.conj g₁⁻¹).toMonoidHom.comp (MulAut.conj g₁).toMonoidHom =
      MonoidHom.id (ModGL TwistTag.D4.tag k) := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      MonoidHom.id_apply]
    group
  rw [hid, Subgroup.map_id]

end Main

end CFSG.ClassicalInvolution.ModelFacts
