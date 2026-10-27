module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six9
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six8
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6SixDvdCard

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise


theorem tw6SixSwap_support56 :
    ((eisTransported 0 • ·) '' parabolicRoots Tag.E6 CFSG.RankThree.E6.support56) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 :=
  (eisTransported_exchanges (k := 0) (by norm_num)).2

theorem tw6SixLayerRoots_smul {L : Type} [Field L] {x : ModGL Tag.E6 L}
    (hvS : ∀ α ∈ torusRootKernel x, e6T3W • α ∈ torusRootKernel x)
    (hW : ((tw6SixFrameWeyl • ·) '' torusRootKernel x) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2) :
    (∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0, e6T3W • α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0) ∧
    (∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1, e6T3W • α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1) := by
  have hT : ∀ β ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2,
      (tw6SixFrameWeyl * e6T3W * tw6SixFrameWeyl⁻¹) • β ∈
        parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2 := by
    intro β hβ
    rw [← hW] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨h13, h56⟩ := conj_e6T3W_preserves_blocks hT
  constructor
  · intro α hα
    rw [tw6SixLayerRoots] at hα ⊢
    obtain ⟨β, hβ, rfl⟩ := hα
    exact ⟨_, h13 β hβ, by simp [mul_smul]⟩
  · intro α hα
    rw [tw6SixLayerRoots] at hα ⊢
    obtain ⟨β, hβ, rfl⟩ := hα
    exact ⟨_, h56 β hβ, by simp [mul_smul]⟩

theorem tw6SixLayer_data {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [IsAlgClosure K L] {n p : ℕ} [CharP L 2] {Fr : L →+* L}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hq3 : 3 ≤ 2 ^ n)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hpq : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) {x : ModGL Tag.E6 L}
    (hx : x ∈ twistedTorusOf (tw6N L) (twistE6 L Fr))
    (hW : ((tw6SixFrameWeyl • ·) '' torusRootKernel x) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2) :
    Finite ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0) ∧
    Finite ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1) ∧
    CFSG.Open.IsQuasisimple ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0) ∧
    CFSG.Open.IsQuasisimple ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1) ∧
    p ∣ Nat.card ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0) ∧
    p ∣ Nat.card ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1) ∧
    (∀ a ∈ tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0,
      ∀ b ∈ tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1, a * b = b * a) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hvS := tw6_torusRootKernel_smul_stable (Fr := Fr) hFr hx
  obtain ⟨h0, h1⟩ := tw6SixLayerRoots_smul hvS hW
  have hw0 : ((tw6SixFrameWeyl • ·) '' tw6SixLayerRoots tw6SixFrameWeyl 0) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [tw6SixLayerRoots, Set.image_image]; simp
  have hw1 : ((tw6SixFrameWeyl • ·) '' tw6SixLayerRoots tw6SixFrameWeyl 1) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support56 := by
    rw [tw6SixLayerRoots, Set.image_image]; simp
  have hw1card : (((eisTransported 0 * tw6SixFrameWeyl) • ·) ''
      tw6SixLayerRoots tw6SixFrameWeyl 1) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 := by
    rw [tw6SixLayerRoots, Set.image_image]
    have hcomp : (fun α : Fin Tag.E6.rank → ℤ => (eisTransported 0 * tw6SixFrameWeyl) •
        (tw6SixFrameWeyl⁻¹ • α)) = fun α => eisTransported 0 • α := by
      funext α
      rw [← mul_smul, mul_assoc, mul_inv_cancel, mul_one]
    rw [hcomp]
    exact tw6SixSwap_support56
  have hSroots0 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  have hSroots1 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  obtain ⟨hQ0, hfin0, hq0, -, -⟩ :=
    tw6_A2_layer_gen (K := K) (Ω := L) (Fr := Fr) (ℓ := 2) (f := n)
      (S := tw6SixLayerRoots tw6SixFrameWeyl 0) (w := tw6SixFrameWeyl) hn hK hq3 hFr
      hSroots0 h0 hw0
  obtain ⟨hQ1, hfin1, hq1, -, -⟩ :=
    tw6_A2_layer_gen₂ (K := K) (Ω := L) (Fr := Fr) (ℓ := 2) (f := n)
      (S := tw6SixLayerRoots tw6SixFrameWeyl 1) (w := tw6SixFrameWeyl) hn hK hq3 hFr
      hSroots1 h1 hw1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard0 := CFSG.StandardType.TwE6Nonsplit.tw6_A2_layer_card (K := K) (Ω := L)
    (Fr := Fr) (ℓ := 2) (f := n) hn hK hFr hSroots0 h0 hw0
  have hcard1 := CFSG.StandardType.TwE6Nonsplit.tw6_A2_layer_card (K := K) (Ω := L)
    (Fr := Fr) (ℓ := 2) (f := n) hn hK hFr hSroots1 h1 hw1card
  have hp0 : p ∣ Nat.card ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0) := by
    rw [tw6SixLayer, hcard0]
    exact CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.dvd_card_SU3_of_dvd hpq
  have hp1 : p ∣ Nat.card ↥(tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1) := by
    rw [tw6SixLayer, hcard1]
    exact CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.dvd_card_SU3_of_dvd hpq
  have hsep : CFSG.RankThree.Lattice.IsSeparated CFSG.RankThree.E6.support13
      CFSG.RankThree.E6.support56 := by
    intro a ha b hb
    rw [CFSG.RankThree.E6.mem_support13] at ha
    rw [CFSG.RankThree.E6.mem_support56] at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hcomm : ∀ a ∈ tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 0,
      ∀ b ∈ tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl 1, a * b = b * a := by
    intro a ha b hb
    set nn := canonicalRep (coxeterSystem Tag.E6) L tw6SixFrameWeyl with hnn
    have ha' : nn * a * nn⁻¹ ∈
        subsystemGroup Tag.E6 L CFSG.RankThree.E6.support13 := by
      rw [← hQ0]; exact ⟨a, ha.1, rfl⟩
    have hb' : nn * b * nn⁻¹ ∈
        subsystemGroup Tag.E6 L CFSG.RankThree.E6.support56 := by
      rw [← hQ1]; exact ⟨b, hb.1, rfl⟩
    have hc : Commute (nn * a * nn⁻¹) (nn * b * nn⁻¹) :=
      commute_of_isSeparated hsep ha' hb'
    have h2 : (MulAut.conj nn) (a * b) = (MulAut.conj nn) (b * a) := by
      rw [map_mul, map_mul, MulAut.conj_apply, MulAut.conj_apply]
      exact hc.eq
    exact (MulAut.conj nn).injective h2
  exact ⟨hfin0, hfin1, CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq0,
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq1, hp0, hp1, hcomm⟩

theorem tw6SixLayer_torus {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [IsAlgClosure K L] {n q : ℕ} [CharP L 2] [Fact q.Prime]
    {Fr : L →+* L} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hqd : q ∣ 2 ^ n + 1)
    (hstab0 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0,
      e6T3W • α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0)
    (hstab1 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1,
      e6T3W • α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1)
    {ζ : L} (hζ : IsPrimitiveRoot ζ q) (i : Fin 2) :
    ∃ T : Subgroup (ModGL Tag.E6 L),
      T ≤ tw6SixLayer (L := L) (Fr := Fr) tw6SixFrameWeyl i ∧
        IsElemAbelian q T ∧ Nat.card T = q ^ 2 := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ n := by omega
  have hqd' : q ∣ Nat.card K + 1 := by rw [hK]; exact hqd
  have hSroots0 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 0, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 tw6SixFrameWeyl⁻¹
  have hSroots1 : ∀ α ∈ tw6SixLayerRoots tw6SixFrameWeyl 1, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
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
  fin_cases i
  · obtain ⟨Φ, T, hTle, hTel, hTcard⟩ :=
      exists_qTorus_in_A2_layer (K := K) (Ω := L) (Fr := Fr) (ℓ := 2) (f := n)
        hf hK hFr hζ hqd' hSroots0 hstab0 (w := tw6SixFrameWeyl) hw0
    exact ⟨T, by simpa [tw6SixLayer, twistedFixedPoints_tw6N] using hTle, hTel, hTcard⟩
  · obtain ⟨Φ, T, hTle, hTel, hTcard⟩ :=
      exists_qTorus_in_A2_layer (K := K) (Ω := L) (Fr := Fr) (ℓ := 2) (f := n)
        hf hK hFr hζ hqd' hSroots1 hstab1 (w := eisTransported 0 * tw6SixFrameWeyl) hw1
    exact ⟨T, by simpa [tw6SixLayer, twistedFixedPoints_tw6N] using hTle, hTel, hTcard⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
