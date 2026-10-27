module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six10
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwUnitary

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix MatrixGroups Pointwise

theorem tw6SixLayer_unitary {K' Ω k : Type} [Field K'] [Finite K'] [Field Ω] [Algebra K' Ω]
    [IsAlgClosure K' Ω] [CharP Ω 2] [Field k] [Algebra k Ω] {n : ℕ} (hn : 2 ≤ n)
    (hK' : Nat.card K' = 2 ^ n) (hU : UnitaryFieldData 2 n k) {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hW : ((tw6SixFrameWeyl • ·) '' torusRootKernel x) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2) (i : Fin 2) :
    Nonempty (↥(tw6SixLayer (L := Ω) (Fr := Fr) tw6SixFrameWeyl i) ≃*
        ↥(unitarySU 2 n k 3)) ∧
      Nat.card (Subgroup.center ↥(tw6SixLayer (L := Ω) (Fr := Fr) tw6SixFrameWeyl i)) ∣ 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K'
  obtain ⟨hstab0, hstab1⟩ := tw6SixLayerRoots_smul
    (tw6_torusRootKernel_smul_stable (Fr := Fr) (q := 2 ^ n) hFr hx) hW
  have hroots : ∀ j : Fin 2, ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl j, IsRoot Tag.E6 α := by
    intro j α hα
    obtain ⟨β, hβ, rfl⟩ := hα
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  have hw0 : ((tw6SixFrameWeyl • ·) '' tw6SixLayerRoots tw6SixFrameWeyl 0) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [tw6SixLayerRoots, Set.image_image]; simp
  have hw1 : (((eisTransported 0 * tw6SixFrameWeyl) • ·) ''
      tw6SixLayerRoots tw6SixFrameWeyl 1) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [tw6SixLayerRoots, Set.image_image]
    have hcomp : (fun α : Fin Tag.E6.rank → ℤ => (eisTransported 0 * tw6SixFrameWeyl) •
        (tw6SixFrameWeyl⁻¹ • α)) = fun α => eisTransported 0 • α := by
      funext α
      rw [← mul_smul, mul_assoc, mul_inv_cancel, mul_one]
    rw [hcomp]
    exact tw6SixSwap_support56
  have h2 : 2 < 2 ^ n := by
    have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num at h
    omega
  obtain ⟨w, hw, hstw⟩ : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' tw6SixLayerRoots tw6SixFrameWeyl i =
        parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 ∧
      (∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl i,
        e6T3W • α ∈ tw6SixLayerRoots tw6SixFrameWeyl i) := by
    fin_cases i
    · exact ⟨tw6SixFrameWeyl, hw0, hstab0⟩
    · exact ⟨eisTransported 0 * tw6SixFrameWeyl, hw1, hstab1⟩
  obtain ⟨Φ, ⟨e⟩, ⟨Hc, hfix⟩, -, hZ⟩ :=
    tw6_A2_layer_equiv (K := K') (Ω := Ω) (Fr := Fr) (ℓ := 2) (f := n)
      (S := tw6SixLayerRoots tw6SixFrameWeyl i) (w := w)
      (by omega) hK' hFr (hroots i) hstw hw
  have hP : tw6SixLayer (L := Ω) (Fr := Fr) tw6SixFrameWeyl i =
      rootSpan Tag.E6 Ω (tw6SixLayerRoots tw6SixFrameWeyl i) ⊓
        (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) := by
    rw [tw6SixLayer, twistedFixedPoints_tw6N]
  have hrange : fixSubgroup Φ = (twUnitaryFrame hU Hc).range :=
    Subgroup.ext fun X =>
      (mem_fixSubgroup_iff_exists_twUnitaryFrame (Ω := Ω) hU hfix X).trans
        MonoidHom.mem_range.symm
  let ε : ↥(tw6SixLayer (L := Ω) (Fr := Fr) tw6SixFrameWeyl i) ≃* ↥(fixSubgroup Φ) :=
    (MulEquiv.subgroupCongr hP).trans e
  refine ⟨⟨ε.trans ((MulEquiv.subgroupCongr hrange).trans
    (MonoidHom.ofInjective (twUnitaryFrame_injective hU Hc)).symm)⟩, ?_⟩
  have hcenter : Nat.card (Subgroup.center ↥(tw6SixLayer (L := Ω) (Fr := Fr)
        tw6SixFrameWeyl i)) = Nat.card (Subgroup.center ↥(fixSubgroup Φ)) :=
    Nat.card_congr (Subgroup.centerCongr ε).toEquiv
  rw [hcenter, (hZ h2).2.2.1]
  exact Nat.gcd_dvd_left 3 _

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
