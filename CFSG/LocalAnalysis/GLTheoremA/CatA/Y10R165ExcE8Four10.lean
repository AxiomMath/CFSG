module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.Sporadic.Co2Schreier.ThirdChain

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.StandardType CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint CFSG.Open
  CFSG.ComponentClassification.CatLeafProof
open scoped Pointwise

theorem d6Vec_apply_one (p : ℕ) (lam : ZMod p) : d6Vec p lam 1 = 1 := by
  rw [d6Vec, TableBExc.redMod]
  have h1 : d4d4WBase 1 = 1 := by decide
  have h2 : d4d4WLambda 1 = 0 := by decide
  rw [show (d4d4WBase + (lam.val : ℤ) • d4d4WLambda) 1 = 1 from by
    show d4d4WBase 1 + (lam.val : ℤ) * d4d4WLambda 1 = 1
    rw [h1, h2, mul_zero, add_zero]]
  norm_num

section Certificates


theorem exists_e8FourPointData (F : Type) [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 4) :
    ∃ (lam : ZMod p) (_ : lam * lam = -1) (ζ : (AlgebraicClosure F)ˣ) (_ : orderOf ζ = p)
      (g : ModGL Tag.E8 (AlgebraicClosure F))
      (_ : g ∈ torusGroup .E8 (AlgebraicClosure F) ⊔
        rootSpan .E8 (AlgebraicClosure F) (kernelRoots d4d4Char))
      (_ : g ∈ Subgroup.normalizer
        (rootSpan .E8 (AlgebraicClosure F) e8D4PerpRoots :
          Set (ModGL .E8 (AlgebraicClosure F))))
      (A₀ : Subgroup (adjointGroup .E8 F)) (_ : IsElemAbelian p A₀)
      (_ : Nat.card A₀ = p ^ 4) (x z : adjointGroup .E8 F) (_ : x ∈ A₀) (_ : z ∈ A₀)
      (_ : x ≠ 1) (_ : z ∉ Subgroup.zpowers x) (_ : x ∈ e8D4Levi F)
      (_ : z ∈ e8D4Levi F),
      adjEmb .E8 F (AlgebraicClosure F) x =
          g * rootDiagUnit .E8 (d6TorsionChar p ζ lam) * g⁻¹ ∧
        adjEmb .E8 F (AlgebraicClosure F) z =
          g * rootDiagUnit .E8 (d6zTorsionChar p ζ lam) * g⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨lam, hqlam, hlam⟩ := exists_lam_of_rk2Ord_four hcard hp hrk
  have hp5 : 5 ≤ p := five_le_of_rk2Ord_four hp hp2 hrk
  have hp3 : 3 < p := by omega
  have hpL : ((p : ℕ) : AlgebraicClosure F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure F) 2 p] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed
    (k := AlgebraicClosure F) (n := p) hpL
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hFr : ∀ c : AlgebraicClosure F,
      iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ Nat.card F := by
    intro c
    rw [iterateFrobenius_def, hcard]
  obtain ⟨g, hgM, hg₀⟩ := exists_fourLang F (AlgebraicClosure F) 2 n hn hcard
  have hgC : g ∈ adjointGroup .E8 (AlgebraicClosure F) :=
    (sup_le torusGroup_le_adjointGroup
      (rootSpan_le_adjointGroup (AlgebraicClosure F) _)) hgM
  obtain ⟨ι, hιinj, hι⟩ := exists_langTorsionHom_of_weyl (K := F) (L := AlgebraicClosure F)
    hp2 hp3 d4d4W hFr hζo hζ hqlam hgC (by simpa using hg₀)
  set vx : NoOffRest.eigSp (NoOffRest.torusLin .E8 p d4d4W) lam :=
    ⟨d6Vec p lam, d6Vec_mem_eig hp2 hlam⟩ with hvx
  set vz : NoOffRest.eigSp (NoOffRest.torusLin .E8 p d4d4W) lam :=
    ⟨d6zVec p lam, d6zVec_mem_eig hp2 hlam⟩ with hvz
  have hvxc : (vx : Fin Tag.E8.rank → ZMod p) = d6Vec p lam := congrArg Subtype.val hvx
  have hvzc : (vz : Fin Tag.E8.rank → ZMod p) = d6zVec p lam := congrArg Subtype.val hvz
  set x : adjointGroup .E8 F := ι (Multiplicative.ofAdd vx) with hxdef
  set z : adjointGroup .E8 F := ι (Multiplicative.ofAdd vz) with hzdef
  have hAe : IsElemAbelian p ι.range :=
    CFSG.StandardType.NoOffE8Five.isElemAbelian_range_of_module ι
  have hxmem : x ∈ ι.range := MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd vx, rfl⟩
  have hzmem : z ∈ ι.range := MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd vz, rfl⟩
  have hxp : x ^ p = 1 := hAe.2 x hxmem
  have hzp : z ^ p = 1 := hAe.2 z hzmem
  have hxdiag : adjEmb .E8 F (AlgebraicClosure F) x =
      g * rootDiagUnit .E8 (d6TorsionChar p ζ lam) * g⁻¹ := by
    have h := hι vx
    rw [hvxc, frameDiag_d6Vec hζ lam] at h
    exact h
  have hzdiag : adjEmb .E8 F (AlgebraicClosure F) z =
      g * rootDiagUnit .E8 (d6zTorsionChar p ζ lam) * g⁻¹ := by
    have h := hι vz
    rw [hvzc, frameDiag_d6zVec hζ lam] at h
    exact h
  have hx1 : x ≠ 1 := by
    intro hx1
    have h1 : (Multiplicative.ofAdd vx : Multiplicative
        (NoOffRest.eigSp (NoOffRest.torusLin .E8 p d4d4W) lam)) = 1 :=
      hιinj (by rw [← hxdef, hx1, map_one])
    have h0 : vx = 0 := Multiplicative.ofAdd.injective (by simpa using h1)
    have hc : d6Vec p lam 1 = 0 := by
      rw [← hvxc]
      exact congrFun (congrArg Subtype.val h0) 1
    rw [d6Vec_apply_one] at hc
    exact one_ne_zero hc
  have hzx : z ∉ Subgroup.zpowers x := by
    rintro ⟨k, hk⟩
    have hk' : (Multiplicative.ofAdd (k • vx) : Multiplicative
        (NoOffRest.eigSp (NoOffRest.torusLin .E8 p d4d4W) lam)) =
        Multiplicative.ofAdd vz := by
      apply hιinj
      have h1 : ι (Multiplicative.ofAdd (k • vx)) =
          (ι (Multiplicative.ofAdd vx)) ^ k :=
        map_zpow ι (Multiplicative.ofAdd vx) k
      have h2 : ι (Multiplicative.ofAdd vz) = z := hzdef.symm
      rw [h1, h2]
      exact hk
    have hv : k • (vx : Fin Tag.E8.rank → ZMod p) =
        (vz : Fin Tag.E8.rank → ZMod p) := by
      have h2 : k • vx = vz := Multiplicative.ofAdd.injective hk'
      simpa using congrArg Subtype.val h2
    have hv4 := congrFun hv 4
    simp only [Pi.smul_apply, hvxc, hvzc, d6Vec_apply_four, d6zVec_apply_four,
      smul_zero] at hv4
    exact zero_ne_one hv4
  have hxL : x ∈ e8D4Levi F :=
    mem_e8D4Levi_of_adjEmb_eq (K := F) (L := AlgebraicClosure F) (n := p)
      (coprime_card_sub_one_of_rk2Ord_four hcard hp hrk) hgM
      (perpRoots_subset_rootCharKernel_d6 lam) hxdiag hxp
  have hzL : z ∈ e8D4Levi F :=
    mem_e8D4Levi_of_adjEmb_eq (K := F) (L := AlgebraicClosure F) (n := p)
      (coprime_card_sub_one_of_rk2Ord_four hcard hp hrk) hgM
      (perpRoots_subset_rootCharKernel_d6z lam) hzdiag hzp
  have hcardA : Nat.card (ι.range) = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv]
    exact card_eig_d4d4W hp2 hlam
  exact ⟨lam, hlam, ζ, hζo, g, hgM,
    torus_sup_rootSpan_d4d4_le_normalizer_perp (L := AlgebraicClosure F) hgM,
    ι.range, hAe, hcardA, x, z, hxmem, hzmem, hx1, hzx, hxL, hzL, hxdiag, hzdiag⟩

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
