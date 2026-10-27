module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1


section Defs

variable {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}

@[expose] noncomputable def frameConj (F : D4PhiFrame K σ q (-1)) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      ModGL TwistTag.D4.tag (AlgebraicClosure K) :=
  (MulAut.conj F.g0⁻¹).toMonoidHom.comp (triEmb K σ (AlgebraicClosure K))

theorem frameConj_apply (F : D4PhiFrame K σ q (-1))
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    frameConj F x = F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) x * F.g0 := by
  change F.g0⁻¹ * _ * F.g0⁻¹⁻¹ = _
  rw [inv_inv]

theorem frameConj_injective (F : D4PhiFrame K σ q (-1)) : Function.Injective (frameConj F) :=
  (MulAut.conj F.g0⁻¹).injective.comp (triEmb_injective (K := K) (σ := σ) (L := AlgebraicClosure K))

@[expose] noncomputable def frameNorm (F : D4PhiFrame K σ q (-1)) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)).comap (frameConj F)

@[expose] noncomputable def frameTorus (F : D4PhiFrame K σ q (-1)) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr)).comap (frameConj F)

@[expose] noncomputable def frameWeyl (F : D4PhiFrame K σ q (-1)) :
    frameNorm F →* WeylGroup TwistTag.D4.tag :=
  (weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)).comp
    (((frameConj F).comp (frameNorm F).subtype).codRestrict
      (monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)) fun x => x.2)

theorem frameWeyl_apply (F : D4PhiFrame K σ q (-1)) (x : frameNorm F) :
    frameWeyl F x = weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
      ⟨frameConj F x, x.2⟩ := rfl

end Defs

section Lift

variable {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}

theorem exists_frameLift (hq1 : 1 ≤ q) (F : D4PhiFrame K σ q (-1))
    {u : WeylGroup TwistTag.D4.tag} (hu : F.w * weylTwist TwistTag.D4 u = u * F.w) :
    ∃ x : frameNorm F, frameWeyl F x = u := by
  classical
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := inferInstance
  set Fh := twistHom TwistTag.D4 L F.Fr with hFh
  set nu := canonicalRep (coxeterSystem TwistTag.D4.tag) L u with hnu
  have hnuM : nu ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L u
  have hnuG : nu ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnuM
  have hFnu : Fh nu = canonicalRep (coxeterSystem TwistTag.D4.tag) L (weylTwist TwistTag.D4 u) :=
    twistHom_canonicalRep TwistTag.D4 L F.Fr u
  have hFnuM : Fh nu ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [hFnu]
    exact canonicalRep_mem_monomialSubgroup L _
  set m := F.n * Fh nu * F.n⁻¹ * nu⁻¹ with hm
  have hmM : m ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (mul_mem F.hn hFnuM) (inv_mem F.hn)) (inv_mem hnuM)
  have hmT : m ∈ torusGroup TwistTag.D4.tag L := by
    refine mem_torusGroup_of_mapsRootLines_one hmM ?_
    have h1 : weylQuotientHom TwistTag.D4.tag L ⟨m, hmM⟩ = 1 := by
      have h3 : (⟨m, hmM⟩ : monomialSubgroup TwistTag.D4.tag L) =
          ⟨F.n, F.hn⟩ * ⟨Fh nu, hFnuM⟩ * (⟨F.n, F.hn⟩)⁻¹ * (⟨nu, hnuM⟩)⁻¹ := rfl
      have h2 : weylQuotientHom TwistTag.D4.tag L ⟨Fh nu, hFnuM⟩ = weylTwist TwistTag.D4 u := by
        refine weylQuotientHom_eq ?_
        change MapsRootLines (Fh nu) (weylTwist TwistTag.D4 u)
        rw [hFnu]
        exact mapsRootLines_canonicalRep _
      have h1' : weylQuotientHom TwistTag.D4.tag L ⟨nu, hnuM⟩ = u :=
        weylQuotientHom_eq (mapsRootLines_canonicalRep u)
      rw [h3]
      simp only [map_mul, map_inv]
      rw [F.hnw, h2, h1', hu]
      group
    have := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := L) ⟨m, hmM⟩
    rwa [h1] at this
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust F.Fr F.hFr F.hn (d4T36M (-1))
    (fun x => by rw [F.hnw]; exact F.hw x) (d4T36M_sub_det_ne_zero (Or.inr rfl) hq1)
    (inv_mem hmT)
  set y := s * nu with hy
  set x₀ := F.g0 * y * F.g0⁻¹ with hx₀
  have hsA : s ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hsT
  have hyA : y ∈ adjointGroup TwistTag.D4.tag L := mul_mem hsA hnuG
  have hx₀A : x₀ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem F.hg0C hyA) (inv_mem F.hg0C)
  have hFx₀ : Fh x₀ = x₀ := by
    rw [hx₀, hy]
    simp only [map_mul, map_inv]
    rw [F.hg0]
    have e1 : F.n * Fh s * F.n⁻¹ = s * m⁻¹ := hs
    have e2 : F.n * Fh nu * F.n⁻¹ = m * nu := by rw [hm]; group
    calc F.g0 * F.n * (Fh s * Fh nu) * (F.g0 * F.n)⁻¹
        = F.g0 * ((F.n * Fh s * F.n⁻¹) * (F.n * Fh nu * F.n⁻¹)) * F.g0⁻¹ := by group
      _ = F.g0 * ((s * m⁻¹) * (m * nu)) * F.g0⁻¹ := by rw [e1, e2]
      _ = F.g0 * (s * nu) * F.g0⁻¹ := by group
  have hrange := F.hperf (Subgroup.zpowers x₀) (by rw [Subgroup.zpowers_le]; exact hx₀A)
    (by
      rintro _ ⟨k, rfl⟩
      rw [map_zpow, hFx₀])
  obtain ⟨x, hx⟩ := hrange (Subgroup.mem_zpowers x₀)
  have hφ : frameConj F x = y := by
    rw [frameConj_apply, hx, hx₀]
    group
  have hyM : y ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (torusGroup_le_monomialSubgroup hsT) hnuM
  refine ⟨⟨x, by
    change frameConj F x ∈ monomialSubgroup TwistTag.D4.tag L
    rw [hφ]; exact hyM⟩, ?_⟩
  rw [frameWeyl_apply]
  have hW : weylQuotientHom TwistTag.D4.tag L ⟨y, hyM⟩ = u :=
    weylQuotientHom_eq (by
      simpa [hy] using (mapsRootLines_of_mem_torusGroup hsT).mul (mapsRootLines_canonicalRep u))
  exact (congrArg (weylQuotientHom TwistTag.D4.tag L) (Subtype.ext hφ)).trans hW

end Lift

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
