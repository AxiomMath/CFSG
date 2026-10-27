module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_injective fieldAutT
  subfieldDerivedImage)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.Quasithin (perfectCore)

section Embed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

instance charP_fieldRange (ι : K →+* F) : CharP ι.fieldRange 2 :=
  RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2

@[expose] noncomputable def fieldRangeEquiv (ι : K →+* F) (n : ℕ) (hn : 1 ≤ n) :
    matrixProjectiveDerived (coordinateQuadPlus n K) ≃*
      matrixProjectiveDerived (coordinateQuadPlus n ι.fieldRange) :=
  (statedOmegaPlusEquiv K n hn).symm.trans
    ((statedOmegaPlusCongr ι.rangeRestrictFieldEquiv n).trans
      (statedOmegaPlusEquiv ι.fieldRange n hn))

@[expose] noncomputable def fieldEmbed (ι : K →+* F) (n : ℕ) (hn : 1 ≤ n) :
    matrixProjectiveDerived (coordinateQuadPlus n K) →*
      matrixProjectiveDerived (coordinateQuadPlus n F) :=
  (incl ι.fieldRange (E7Pilot.isExtension_coordinateQuadPlus n ι.fieldRange)).comp
    (fieldRangeEquiv ι n hn).toMonoidHom

theorem fieldEmbed_frameHom (ι : K →+* F) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → Kˣ) :
    fieldEmbed ι n hn ((isHypFrame_plus K n).frameHom t) =
      (isHypFrame_plus F n).frameHom (liftParam ι t) := by
  have h3 : (statedOmegaPlusEquiv K n hn).symm ((isHypFrame_plus K n).frameHom t) =
      ⟨diagOmega K n t, diagOmega_mem_statedOmega_of_one_le hn _⟩ :=
    Subtype.ext (statedOmegaPlusEquiv_symm_frameHom hn _)
  have h4 : statedOmegaPlusCongr ι.rangeRestrictFieldEquiv n
      ⟨diagOmega K n t, diagOmega_mem_statedOmega_of_one_le hn _⟩ =
      ⟨diagOmega ι.fieldRange n (liftParam ι.rangeRestrictFieldEquiv.toRingHom t),
        diagOmega_mem_statedOmega_of_one_le hn _⟩ :=
    Subtype.ext ((coe_statedOmegaPlusCongr _ _).trans (glCongr_diagOmega _ _))
  have h5 := statedOmegaPlusEquiv_diag (F := ι.fieldRange) hn
    (liftParam ι.rangeRestrictFieldEquiv.toRingHom t) (diagOmega_mem_statedOmega_of_one_le hn _)
  have hw : liftParam ι.fieldRange.subtype (liftParam ι.rangeRestrictFieldEquiv.toRingHom t) =
      liftParam ι t := by
    funext l
    apply Units.ext
    simp [liftParam]
  change incl _ _ (statedOmegaPlusEquiv ι.fieldRange n hn (statedOmegaPlusCongr _ n
    ((statedOmegaPlusEquiv K n hn).symm ((isHypFrame_plus K n).frameHom t)))) = _
  rw [h3, h4, h5, incl_frameHom, hw]

omit [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem liftParam_mem_signedLevelParam (ι : K →+* F) {n : ℕ} {J P : Finset (Fin n)}
    {t : Fin n → Kˣ} (ht : t ∈ signedLevelParam (K := K) J P) :
    liftParam ι t ∈ signedLevelParam (K := F) J P := by
  intro i hi j hj
  have h := ht i hi j hj
  simp only [flipParam_apply] at h ⊢
  split_ifs at h ⊢ with h1 h2 h2
  · simp only [liftParam, ← map_inv, h]
  · simp only [liftParam, ← map_inv, h]
  · simp only [liftParam, ← map_inv, h]
  · simp only [liftParam, h]

theorem map_fieldEmbed_plusSignedLevelTorus_le (ι : K →+* F) {n : ℕ} (hn : 1 ≤ n)
    (J P : Finset (Fin n)) :
    (plusSignedLevelTorus K J P).map (fieldEmbed ι n hn) ≤ plusSignedLevelTorus F J P := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ frameTorusOf (coordinateQuadPlus n K) (plusFrameLeft n) (plusFrameRight n)
      (signedLevelParam J P) := hx
  rw [(isHypFrame_plus K n).frameTorusOf_eq_map] at hx'
  obtain ⟨s, hs, rfl⟩ := hx'
  change _ ∈ frameTorusOf (coordinateQuadPlus n F) (plusFrameLeft n) (plusFrameRight n)
    (signedLevelParam J P)
  rw [(isHypFrame_plus F n).frameTorusOf_eq_map, fieldEmbed_frameHom]
  exact ⟨_, liftParam_mem_signedLevelParam ι hs, rfl⟩

end Embed

section Generation

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem range_le_iSup_plusNode_of_comp_fieldEmbed {n g : ℕ} (hn : 4 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (hFg : Nat.card F = 2 ^ g)
    (hF : 4 ≤ Nat.card F) (ι : K →+* F)
    {Φ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G}
    (hΦ : ∀ x, Φ (fieldEmbed ι n (by omega) x) = ((e.symm x : L) : G)) :
    Φ.range ≤ ⨆ j, plusNode e j := by
  rw [MonoidHom.range_eq_map, ← iSup_rationalNode (K := F) hn hFg hF, Subgroup.map_iSup]
  refine iSup_mono fun j => ?_
  refine F4Pilot.le_centralizerPerfectCore ?_ ?_
  · rw [← Subgroup.map_commutator, commutator_rationalNode (by omega) hF j]
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hy
    have hxF : fieldEmbed ι n (by omega) x ∈
        plusSignedLevelTorus F (plusNodeSet n j) (plusNodeFlip n j) :=
      map_fieldEmbed_plusSignedLevelTorus_le ι (by omega) _ _ ⟨x, hx, rfl⟩
    have hc : fieldEmbed ι n (by omega) x * a = a * fieldEmbed ι n (by omega) x :=
      mem_centralizer_iff.1 (rationalNode_le_centralizer _ j ha) _ hxF
    rw [← hΦ x, ← map_mul, ← map_mul, hc]

end Generation

section Renormalize

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_comp_fieldEmbed_eq (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Ψ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G} (hinj : Function.Injective Ψ)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x))
    {ψ' : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hψ' : ψ' * β * ψ'⁻¹ =
      fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)) :
    ∃ Φ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G, Φ.range = Ψ.range ∧
      ∀ x, Φ (fieldEmbed ι n (by omega) x) = ((e.symm x : L) : G) := by
  set σs := fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)
    with hσs
  set k := ι.fieldRange with hk
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => by
    rw [hfix, hk, RingHom.mem_fieldRange, Set.mem_range]
  have hext := E7Pilot.isExtension_coordinateQuadPlus n k
  set Ψ₁ := Ψ.comp ψ'.symm.toMonoidHom with hΨ₁
  have hinj₁ : Function.Injective Ψ₁ := hinj.comp ψ'.symm.injective
  have hrange₁ : Ψ₁.range = Ψ.range := by
    rw [hΨ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ'.symm.surjective,
      ← MonoidHom.range_eq_map]
  have hβ' : β = ψ'⁻¹ * σs * ψ' := by rw [← hψ']; group
  have hσΨ₁ : ∀ x, t * Ψ₁ x * t⁻¹ = Ψ₁ (σs x) := by
    intro x
    simp only [hΨ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hβ, hβ']
    congr 1
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hC : Ψ.range ⊓ centralizer ({t} : Set G) = (fixedSubgroup σs).map Ψ₁ := by
    rw [← hrange₁]
    exact SymplecticPilot.range_inf_centralizer_eq_map hinj₁ hσΨ₁
  obtain ⟨hQ, -⟩ := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    n F (by omega)
  have hQne : ∃ v, coordinateQuadPlus n F v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.exists_ne_zero_of_nondeg
      (by omega : 0 < 2 * n) hQ
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ (E7Pilot.commutator_top_coordinatePlus (by omega))
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT
    (E7Pilot.coordinateQuadPlus_fieldMap n σ) hσk hext hQne hJ
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  set ε : matrixProjectiveDerived (coordinateQuadPlus n k) →* G := Ψ₁.comp (incl k hext)
    with hε
  have hεinj : Function.Injective ε := hinj₁.comp hιinj
  have hperf : ⁅ε.range, ε.range⁆ = ε.range :=
    E7Pilot.commutator_range_of_commutator_top _ (E7Pilot.commutator_top_coordinatePlus (by omega))
  have hεC : ε.range ≤ centralizer ({t} : Set G) := by
    have h1 : ε.range ≤ (fixedSubgroup σs).map Ψ₁ := by
      rintro _ ⟨y, rfl⟩
      refine ⟨incl k hext y, ?_, rfl⟩
      have h2 : incl k hext y ∈ perfectCore (fixedSubgroup σs) := by
        rw [hcore]
        exact ⟨y, rfl⟩
      exact CFSG.Quasithin.perfectCore_le _ h2
    rw [← hC] at h1
    exact h1.trans inf_le_right
  have hle : ε.range ≤ L := std_perfect_le hset hOut htC ht hperf hεC
  have hcard : Nat.card L ≤ Nat.card ε.range := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv,
      Nat.card_congr (fieldRangeEquiv ι n (by omega)).toEquiv]
  have hεL : ε.range = L := Subgroup.eq_of_le_of_card_ge hle hcard
  set E : matrixProjectiveDerived (coordinateQuadPlus n k) ≃* L :=
    (MonoidHom.ofInjective hεinj).trans (MulEquiv.subgroupCongr hεL) with hE
  have hEval : ∀ y, ((E y : L) : G) = Ψ₁ (incl k hext y) := fun y => rfl
  set δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n k)) :=
    (fieldRangeEquiv ι n (by omega)).symm.trans (e.symm.trans E.symm) with hδ
  obtain ⟨δ', hδ'⟩ := E7Pilot.exists_mulAut_incl_comm (k := k) hn δ
  refine ⟨Ψ₁.comp δ'.toMonoidHom, ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 δ'.surjective, ← MonoidHom.range_eq_map,
      hrange₁]
  · change Ψ₁ (δ' (incl k hext (fieldRangeEquiv ι n (by omega) x))) = _
    rw [hδ', ← hEval]
    have h1 : E (δ (fieldRangeEquiv ι n (by omega) x)) = e.symm x := by
      change E (E.symm (e.symm ((fieldRangeEquiv ι n (by omega)).symm
        (fieldRangeEquiv ι n (by omega) x)))) = e.symm x
      rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    rw [h1]

end Renormalize

end CFSG.SeitzReduction.OmegaPilot
