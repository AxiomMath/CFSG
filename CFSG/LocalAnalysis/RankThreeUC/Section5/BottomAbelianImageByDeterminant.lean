module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PDimensionOdd
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddDimCentralInvolutionForcesAbelian.OddDimCentralInvolutionForcesAbelian
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BottomBinaryCenterOrderTwo

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BottomAbelianImageByDeterminant

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem abelian (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXbot : CentralBinaryBlocks.X hc = ⊥) :
    IsMulCommutative (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  set H : Subgroup (MulAut ↥P) := T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) with hH
  have hH2 : IsPGroup 2 H := hc.oddPrimeClassTwoAction.setting.twoGroup.map _
  have hodd := PDimensionOdd.odd hc hr
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'
    have hpodd : Odd p := hc.oddPrimeClassTwoAction.setting.odd
    subst this
    exact absurd hpodd (by decide)
  have hne := BottomBinaryCenterOrderTwo.Y_ne_bot hc hr
  obtain ⟨y0, hy01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hy0n : (y0 : MulAut ↥P) ≠ 1 := fun h => hy01 (Subtype.ext h)
  have hinv := BottomCentralInvolutionInverts.inverts hc hr hXbot
  have hy0H : (y0 : MulAut ↥P) ∈ H := CentralBinarySubgroup.Y_le hc y0.2
  have hy02 : (y0 : MulAut ↥P) ^ 2 = 1 :=
    (CentralBinarySubgroup.Y_elemAbelian hc).2 _ y0.2
  let z : H := ⟨y0, hy0H⟩
  have hzc : z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (CentralBinarySubgroup.Y_commute hc _ y0.2 _ w.2).eq.symm
  have hz2 : z ^ 2 = 1 := Subtype.ext hy02
  have hz1 : z ≠ 1 := fun h => hy0n (congrArg Subtype.val h)
  have huniq : ∀ y ∈ Subgroup.center H, y ^ 2 = 1 → y ≠ 1 → y = z := by
    intro y hyc hy2 hy1
    have hyY : (y : MulAut ↥P) ∈ CentralBinaryBlocks.Y hc := by
      unfold CentralBinaryBlocks.Y
      rw [JeTransport.mem_omegaOneZ_gen 2 _]
      refine Subgroup.subset_closure ⟨y.2, ?_, ?_⟩
      · intro w hw
        have := Subgroup.mem_center_iff.mp hyc ⟨w, hw⟩
        exact congrArg Subtype.val this
      · exact congrArg Subtype.val hy2
    have hy1' : (y : MulAut ↥P) ≠ 1 := fun h => hy1 (Subtype.ext h)
    apply Subtype.ext
    ext x
    rw [hinv _ hyY hy1' x]
    exact congrArg Subtype.val (hinv _ y0.2 hy0n x).symm
  let σ : Representation (ZMod p) H (Space hc) := (sigma hc).comp H.subtype
  have hzneg : σ z = -LinearMap.id := by
    ext v : 1
    apply Additive.toMul.injective
    show (sigma hc (y0 : MulAut ↥P) v).val = (-v).val
    rw [sigma_apply, hinv _ y0.2 hy0n]
    rfl
  haveI : Finite (Space hc) := inferInstanceAs (Finite (Additive ↥P))
  haveI : FiniteDimensional (ZMod p) (Space hc) := Module.Finite.of_finite
  exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddDimCentralInvolutionForcesAbelian.abelian hH2 h2 σ z hzc hz2 hz1 huniq hzneg hodd

end CFSG.LocalAnalysis.RankThreeUC.Section5.BottomAbelianImageByDeterminant
