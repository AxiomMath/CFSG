module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Datum
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_uniform_of_twistReduction
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    (L₀ : Subgroup (ModGL τ k))
    (hL₀ : L₀ ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})
    (hL₀c : CFSG.IsPComponent 2 (L₀.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
      (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ Dd : OrthogonalSemilinearFixedRootDatum τ p k,
      (∃ m ∈ reps, ∃ l ∈ m.omegaWords, Dd.χ = signMaskChar τ m.mask ∧
        ∀ γ, Dd.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt τ l) ρ γ)) ∧
      Dd.e = e ∧ Finite Dd.totalFixedGroup ∧
      ∀ L : Subgroup (ModGL τ k),
        L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
          fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x} →
        CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
          (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
            Subgroup.centralizer {x})) →
        ∃ J₀ : Subgroup (adjointGroup τ k), J₀ ≤ Dd.totalFixedGroup ∧
          CFSG.IsPComponent 2 (J₀.subgroupOf Dd.totalFixedGroup) ∧ Nonempty (L ≃* J₀) := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  set χ := signMaskChar τ r.mask with hχ
  set Q₀ := wordWeylMatrix τ k l * D with hQ₀_def
  set M := torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) with hM_def
  have hMG : M ≤ adjointGroup τ k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨-, hJc⟩ := ((hcomp 2 Nat.prime_two).1 L₀).1 ⟨hL₀, hL₀c⟩
    exact not_isPComponent_of_kernelRoots_eq_empty hne
      (inf_le_left : fixedPointsIn M (frobTwistGL τ k p e Q₀) ≤ M) _ hJc
  have hθ := htheta r hr l hl
  have hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) hDT
  obtain ⟨Dd, h, hhT, hDχ, hDe, hDθ, -, hX⟩ := exists_pinned_datum p hp hk he hτ hA hB hθ
    (hDX l) hQ₀T (map_conj_wordWeylMatrix_mul l hDG) (hpin r hr l hl) hne
  have hker := rootCharKernel_signCharTuple (k := k) hk2 χ
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk2
    (signCharTuple χ) (signCharTuple_sign χ)
  rw [toralRootPointSubgroup, toralRootGroup, hker] at hMc hMsm
  have hF₀M : ∀ g ∈ M, frobTwistGL τ k p e Q₀ g ∈ M := by
    intro g hg
    have hS : (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q₀) =
        rootSpan τ k (kernelRoots χ) := by
      rw [map_frobTwistGL_rootSpan_of_conj p e (hDX l) fun _ hα => hα.1, hθ.image_kernelRoots]
    have hM₀ : M.map (frobTwistGL τ k p e Q₀) = M := by
      rw [hM_def, Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQ₀T, hS]
    rw [← hM₀]
    exact ⟨g, hg, rfl⟩
  obtain ⟨z, hzM, hz⟩ := exists_eq_inv_mul_frobTwistGL p he Q₀ hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hFu : frobTwistGL τ k p e Q₀ z⁻¹ = h⁻¹ * z⁻¹ := by
    rw [map_inv, hz]
    group
  have hFh : ∀ y, frobTwistGL τ k p e (h * Q₀) y = h * frobTwistGL τ k p e Q₀ y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M (frobTwistGL τ k p e Q₀)).map (MulAut.conj z⁻¹).toMonoidHom =
      fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) :=
    map_conj_fixedPointsIn_eq M _ _ (inv_mem hzM) hFh hFu
  have hQfin' : Finite (fixedPointsIn M (frobTwistGL τ k p e Q₀)) := hQfin
  set Mh := fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) with hMh_def
  set X := Dd.totalFixedGroup with hX_def
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup τ k).subtype
      (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ y : X, ((eX y : Mh) : ModGL τ k) =
      (((y : adjointGroup τ k)) : ModGL τ k) := fun y => rfl
  have hMhfin : Finite Mh := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj z⁻¹).subgroupMap
      (fixedPointsIn M (frobTwistGL τ k p e Q₀))).toEquiv
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  refine ⟨Dd, ⟨r, hr, l, hl, hDχ, hDθ⟩, hDe, hXfin, fun L hL hLc => ?_⟩
  obtain ⟨hJle, hJc⟩ := ((hcomp 2 Nat.prime_two).1 L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff z⁻¹ hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  set JD := J.map (MulAut.conj z⁻¹).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup τ k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup τ k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro y hy
    have hy' : (y : ModGL τ k) ∈ JD := hy
    have hmem : (y : ModGL τ k) ∈ X.map (adjointGroup τ k).subtype := by
      rw [hX]
      exact hJDle hy'
    obtain ⟨w, hw, hwy⟩ := hmem
    have : w = y := Subtype.ext hwy
    exact this ▸ hw
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have : (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) = (w : ModGL τ k) := by
          have := heX (eX.symm w)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) ∈ JD
        rw [this]
        exact hw
      · intro hy
        refine ⟨eX y, ?_, MulEquiv.symm_apply_apply eX y⟩
        change ((eX y : Mh) : ModGL τ k) ∈ JD
        rw [heX]
        exact hy
    rwa [h2] at h1
  exact ⟨J₀, hJ₀X, hJ₀comp,
    ⟨(L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
      ((J.equivMapOfInjective _ (MulAut.conj z⁻¹).injective).trans
        (Subgroup.subgroupOfEquivOfLe hJDG).symm)⟩⟩

end CFSG.ComponentClassification.CatLeafProof
