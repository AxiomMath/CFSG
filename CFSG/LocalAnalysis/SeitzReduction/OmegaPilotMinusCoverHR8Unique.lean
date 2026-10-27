module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_injective fieldAutT
  subfieldDerivedImage)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam planeTorusParam)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed autExtensionComm_incl_minus)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Quasithin (perfectCore)

section Embed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def minusEqEquiv {n : ℕ} (hn : 1 ≤ n) {β β' γ γ' : F} (hβ : β = β')
    (hγ : γ = γ') :
    matrixProjectiveDerived (coordinateQuadMinus n F hn β γ) ≃*
      matrixProjectiveDerived (coordinateQuadMinus n F hn β' γ') := by
  subst hβ hγ
  exact MulEquiv.refl _

@[expose] noncomputable def minusFieldEmbed (ι : K →+* F) {n : ℕ} (hn : 1 ≤ n) (b c : K) :
    matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
      matrixProjectiveDerived (coordinateQuadMinus n F hn (ι b) (ι c)) :=
  (minusEqEquiv hn (RingHom.rangeRestrictFieldEquiv_apply_coe ι b)
      (RingHom.rangeRestrictFieldEquiv_apply_coe ι c)).toMonoidHom.comp
    ((incl ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange hn
      (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))).comp
      (minusCongr ι.rangeRestrictFieldEquiv hn b c).toMonoidHom)

end Embed

section Renormalize

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_comp_incl_minus_eq (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (hn : 5 ≤ n) {σ : F ≃+* F} {k : Subfield F}
    [CharP k 2] (hσk : ∀ x, x ∈ k ↔ σ x = x) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (j : L ≃* matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {Ψ : matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (b : F) (c : F)) →* G}
    (hinj : Function.Injective Ψ)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (b : F) (c : F)))}
    (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x))
    {ψ' : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (b : F) (c : F)))}
    (hψ' : ψ' * β * ψ'⁻¹ = fieldAutT (coordinateQuadMinus n F (by omega) (b : F) (c : F)) σ
      (coordinateQuadMinus_fieldMap_of_fixed (by omega) ((hσk b).1 b.2) ((hσk c).1 c.2))) :
    ∃ Φ : matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (b : F) (c : F)) →* G,
      Φ.range = Ψ.range ∧
        ∀ x : L, Φ (incl k (isExtension_coordinateQuadMinus k (by omega) b c) (j x)) = (x : G) := by
  have hn1 : 1 ≤ n := by omega
  have hQσ := coordinateQuadMinus_fieldMap_of_fixed (n := n) hn1 ((hσk b).1 b.2) ((hσk c).1 c.2)
  set σs := fieldAutT (coordinateQuadMinus n F hn1 (b : F) (c : F)) σ hQσ with hσs
  have hext := isExtension_coordinateQuadMinus k hn1 b c
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
  have hQne : ∃ v, coordinateQuadMinus n F hn1 (b : F) (c : F) v ≠ 0 :=
    ⟨minusAnisoVec hn1, by rw [coordinateQuadMinus_minusAnisoVec]; exact one_ne_zero⟩
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT hQσ hσk hext hQne hJ
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  set ε := Ψ₁.comp (incl k hext) with hε
  have hεinj : Function.Injective ε := hinj₁.comp hιinj
  have hperf : ⁅ε.range, ε.range⁆ = ε.range :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
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
    rw [Nat.card_congr j.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv]
  have hεL : ε.range = L := Subgroup.eq_of_le_of_card_ge hle hcard
  set E : matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c) ≃* L :=
    (MonoidHom.ofInjective hεinj).trans (MulEquiv.subgroupCongr hεL) with hE
  have hEval : ∀ y, ((E y : L) : G) = Ψ₁ (incl k hext y) := fun y => rfl
  set δ : MulAut (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c)) :=
    j.symm.trans E.symm with hδ
  obtain ⟨δ', hδ', -⟩ := autExtensionComm_incl_minus (n := n) (by omega) hσk b c hirr hQσ δ
  refine ⟨Ψ₁.comp δ'.toMonoidHom, ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 δ'.surjective, ← MonoidHom.range_eq_map,
      hrange₁]
  · change Ψ₁ (δ' (incl k hext (j x))) = _
    rw [hδ', ← hEval]
    have h1 : E (δ (j x)) = x := by
      change E (E.symm (j.symm (j x))) = x
      rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
    rw [h1]

end Renormalize

section NodeParam

variable {K : Type} [Field K] {F : Type} [Field F] {r : ℕ}

theorem snocOneParam_liftParam_mem_signedLevelParam_of_le (ι : K →+* F) {j : Fin (r + 2)}
    (hj : j.val + 1 ≤ r) {s : Fin (r + 1) → Kˣ}
    (hs : s ∈ levelParam (consecutiveBlock (r + 1) j.val 2)) :
    snocOneParam F (r + 1) (liftParam ι s) ∈
      signedLevelParam (plusNodeSet (r + 2) j) (plusNodeFlip (r + 2) j) := by
  change flipParam F (plusNodeFlip (r + 2) j) (snocOneParam F (r + 1) (liftParam ι s)) ∈
    levelParam (plusNodeSet (r + 2) j)
  have hflip : ∀ x : Fin (r + 2), x ∉ plusNodeFlip (r + 2) j := by
    intro x hx
    simp only [plusNodeFlip, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    omega
  have hcast : ∀ x ∈ plusNodeSet (r + 2) j, ∃ x' : Fin (r + 1),
      x'.castSucc = x ∧ x' ∈ consecutiveBlock (r + 1) j.val 2 := by
    intro x hx
    rw [mem_plusNodeSet] at hx
    have hxv : x.val = j.val ∨ x.val = j.val + 1 := by omega
    refine ⟨⟨x.val, by omega⟩, Fin.ext rfl, ?_⟩
    rw [mem_consecutiveBlock]
    simp only
    omega
  intro x hx y hy
  obtain ⟨x', rfl, hx'⟩ := hcast x hx
  obtain ⟨y', rfl, hy'⟩ := hcast y hy
  rw [flipParam_apply, flipParam_apply, ite_eq_right (hflip _), ite_eq_right (hflip _),
    snocOneParam_castSucc, snocOneParam_castSucc]
  simp only [liftParam]
  rw [hs x' hx' y' hy']

theorem snocOneParam_liftParam_mem_signedLevelParam_of_fork (ι : K →+* F) {j : Fin (r + 2)}
    (hj : ¬ j.val + 1 ≤ r) {s : Fin (r + 1) → Kˣ}
    (hs : s ∈ planeTorusParam K {Fin.last r}) :
    snocOneParam F (r + 1) (liftParam ι s) ∈
      signedLevelParam (plusNodeSet (r + 2) j) (plusNodeFlip (r + 2) j) := by
  change flipParam F (plusNodeFlip (r + 2) j) (snocOneParam F (r + 1) (liftParam ι s)) ∈
    levelParam (plusNodeSet (r + 2) j)
  have hone : ∀ x ∈ plusNodeSet (r + 2) j, snocOneParam F (r + 1) (liftParam ι s) x = 1 := by
    intro x hx
    rw [mem_plusNodeSet] at hx
    have hxv : x.val = r ∨ x.val = r + 1 := by omega
    rcases hxv with hxv | hxv
    · have hx' : x = (Fin.last r).castSucc := Fin.ext (by simp [hxv])
      rw [hx', snocOneParam_castSucc]
      have h1 : s (Fin.last r) = 1 := hs _ (Finset.mem_singleton_self _)
      simp only [liftParam, h1, map_one]
    · have hx' : x = Fin.last (r + 1) := Fin.ext (by simp [hxv])
      rw [hx', snocOneParam_last]
  intro x hx y hy
  rw [flipParam_apply, flipParam_apply, hone x hx, hone y hy]
  simp

end NodeParam

@[expose] def OmegaMinusInvolutionCentralizerInput (n : ℕ) : Prop :=
  ∀ (hn : 4 ≤ n) (K F : Type) [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F), orderOf σ = 2 → Nat.card F = Nat.card K ^ 2 →
    ∀ (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ (β γ : F) (hβ : σ β = β) (hγ : σ γ = γ), (∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) →
    ∀ B : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ)), B * B = 1 →
      (∀ ψ : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ)),
        ψ * B * ψ⁻¹ ≠ fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
          (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ)) →
      ¬ Nat.card (fixedSubgroup B) ∣
        2 * Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)))

end CFSG.SeitzReduction.OmegaPilot
