module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpTwist
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllConj

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Frames

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]

theorem ellFrame_one (f : ℕ) (hq : 2 ≤ p ^ f) :
    EllFrame (twistHom TwistTag.D4 L (iterateFrobenius L p f)) ((p ^ f : ℕ) : ℤ) := by
  have hFr : ∀ c, iterateFrobenius L p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  refine ⟨fun t ht => twistHom_mem_torusGroup_d4 _ ht, fun q hq' => twistHom_mem_rootSpan_d4LongA2 f hq',
    twistHom_diagramMap _, fun ν hν => ?_, by omega⟩
  rw [twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  have h1 : ν ((Equiv.symm TwistTag.D4.perm) i) = ν i := by
    have := hν ((Equiv.symm TwistTag.D4.perm) i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  rw [h1, CTTorus.map_units_eq_pow hFr, Pi.pow_apply, zpow_natCast]

def twistHomOppHom (Fr : L →+* L) : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (trialityOpposition L)).toMonoidHom.comp (twistHom TwistTag.D4 L Fr)

theorem twistHomOppHom_apply (Fr : L →+* L) (g : ModGL TwistTag.D4.tag L) :
    twistHomOppHom Fr g = twistHomOpp Fr g := by
  simp [twistHomOppHom, twistHomOpp, MulAut.conj_apply]

theorem ellFrame_two (f : ℕ) (hq : 2 ≤ p ^ f) :
    EllFrame (twistHomOppHom (iterateFrobenius L p f)) (-((p ^ f : ℕ) : ℤ)) := by
  have h1 := ellFrame_one (L := L) f hq
  refine ⟨fun t ht => ?_, fun q hq' => ?_, ?_, fun ν hν => ?_, by omega⟩
  · rw [twistHomOppHom_apply, twistHomOpp,
      trialityOpposition_twistHom_torus _ ht]
    exact inv_mem (twistHom_mem_torusGroup_d4 _ ht)
  · rw [twistHomOppHom_apply, twistHomOpp]
    exact mp_conj_z0_rootSpan (twistHom_mem_rootSpan_d4LongA2 f hq')
  · rw [twistHomOppHom_apply, twistHomOpp, twistHom_diagramMap]
    have h : diagramMap TwistTag.D4 L * trialityOpposition L =
        trialityOpposition L * diagramMap TwistTag.D4 L := diagramMap_comm_trialityOpposition
    rw [← h]
    group
  · rw [twistHomOppHom_apply, twistHomOpp, h1.torusPow ν hν,
      trialityOpposition_conj_torus (rootDiagUnit_mem_torusGroup _), rootDiagUnit_inv]
    congr 1
    funext i
    simp [zpow_neg]

end Frames

section LSide

variable {L : Type} [Field L] [IsAlgClosed L]

theorem zpow_eq_self_of_emod_three {b : Lˣ} (hb3 : b ^ 3 = 1) {e : ℤ} (he : e % 3 = 1) :
    b ^ e = b := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, e = 3 * k + 1 := ⟨e / 3, by omega⟩
  rw [hk, zpow_add, zpow_one, zpow_mul]
  have : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
  rw [this, one_zpow, one_mul]

theorem cube_of_cocycle {x : ModGL TwistTag.D4.tag L}
    (h : x * ((diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * x *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1) :
    (x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1 := by
  have h1 : x * ((diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * x *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) =
      (x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 * (diagramMap TwistTag.D4 L) ^ 3 := by
    rw [pow_three, pow_three]
    group
  rw [h1, diagramMap_pow_three, mul_one] at h
  exact h

theorem weyl_mem_rel_of {x : ModGL TwistTag.D4.tag L}
    (hx : x ∈ monomialSubgroup TwistTag.D4.tag L)
    (H : ∀ (k : ModGL TwistTag.D4.tag L) (w : WeylGroup TwistTag.D4.tag),
      k ∈ torusGroup TwistTag.D4.tag L →
      x = k * canonicalRep (coxeterSystem TwistTag.D4.tag) L w → w ∈ relWeylTwist TwistTag.D4) :
    weylQuotientHom TwistTag.D4.tag L ⟨x, hx⟩ ∈ relWeylTwist TwistTag.D4 := by
  obtain ⟨w, k, hk, hxe⟩ := monomialSubgroup_le_torusWeylCosets hx
  have hxw : weylQuotientHom TwistTag.D4.tag L ⟨x, hx⟩ = w := by
    refine weylQuotientHom_eq ?_
    show MapsRootLines x w
    rw [hxe]
    exact mapsRootLines_mul_canonicalRep hk w
  rw [hxw]
  exact H k w hk hxe

theorem ell_main_L {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : EllFrame F e) (he3 : e % 3 = 1) {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) (hnT : n ∉ torusGroup TwistTag.D4.tag L)
    (hw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ ∈ relWeylTwist TwistTag.D4)
    (hx3 : (n * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) (hFn : F n = n)
    (hA : ∃ A : Lˣ, A ^ 3 = 1 ∧ A ≠ 1)
    (hlang : ∀ b : Lˣ, b ^ 3 = 1 → b ≠ 1 →
      ∀ ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b),
      (∃ t ∈ torusGroup TwistTag.D4.tag L, ∃ q ∈ rootSpan TwistTag.D4.tag L d4LongA2,
        ζ = t * q) →
      (∃ hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L,
        (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeA *ᵥ x) ∨
          (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeB *ᵥ x)) →
      ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b), z⁻¹ * F z = ζ) :
    ∃ b : Lˣ, b ^ 3 = 1 ∧ b ≠ 1 ∧ ∃ y ∈ adjointGroup TwistTag.D4.tag L, F y = y ∧
      y * (n * (diagramMap TwistTag.D4 L)⁻¹) * y⁻¹ = rotElt b := by
  obtain ⟨A, hA3, hA1⟩ := hA
  obtain ⟨b, hb3, hb1, h, hh, hx⟩ := ell_geometric_conj hA3 hA1 hn hnT hw hx3
  obtain ⟨y, hyG, hyF, hy⟩ := ell_lang_descent hF hb3 hb1 (zpow_eq_self_of_emod_three hb3 he3)
    hh hx hFn (hlang b hb3 hb1)
  exact ⟨b, hb3, hb1, y, hyG, hyF, hy⟩

end LSide

end CFSG.HardMathSupport.Lang.E6Descent
