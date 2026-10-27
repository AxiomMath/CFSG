module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.TwE6Step3.Lines
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

theorem exists_twE6Six_selection {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {g0 : ModGL Tag.E6 L} {c : twistedE6RootGroup K σ}
    {A : Subgroup (twistedE6RootGroup K σ)} (hAe : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3)
    (hT : ∀ a ∈ A, psiT g0 c a ∈ twistedTorusOf (tw6N L) (twistE6 L Fr)) :
    ∃ x, x ∈ A ∧ ∃ y, y ∈ A ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x ∧
      IsA2A2Kernel (torusRootKernel (psiT g0 c x)) ∧
      IsA2Kernel (parabolicRoots Tag.E6 tw6SixSupportA2) ∧
      parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ torusRootKernel (psiT g0 c x) ∧
      parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ torusRootKernel (psiT g0 c y) ∧
      psiT g0 c x = rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZx p (ℓ ^ f) i).val) ∧
      psiT g0 c y = rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZy p (ℓ ^ f) i).val) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq0 : (((ℓ ^ f : ℕ)) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero L ℓ]
    exact zero_pow (by omega)
  have hq : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 - ((ℓ ^ f : ℕ) : ZMod p) + 1 = 0 :=
    (tw6_prime_setup (L := L) hq0 (Fact.out : p.Prime) hpq).2.2
  set ψ : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 L :=
    { toFun := psiT g0 c
      map_one' := psiT_one g0 c
      map_mul' := psiT_mul g0 c } with hψdef
  have hBcard : Nat.card (A.map ψ) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (psiT_injective g0 c), hAcard]
  have hBe : IsElemAbelian p (A.map ψ) := CFSG.SectionRank.isElemAbelian_map hAe ψ
  have hBT : A.map ψ ≤ twistedTorusOf (tw6N L) (twistE6 L Fr) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hT a ha
  obtain ⟨hpx, hpy⟩ := tw6Six_eigen_points_mem (L := L) hζ hFr hq hp5 hBe hBcard hBT
  obtain ⟨x, hxA, hψx⟩ := Subgroup.mem_map.1 hpx
  obtain ⟨y, hyA, hψy⟩ := Subgroup.mem_map.1 hpy
  have hψx' : psiT g0 c x = rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZx p (ℓ ^ f) i).val) := hψx
  have hψy' : psiT g0 c y = rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZy p (ℓ ^ f) i).val) := hψy
  have hx1 : x ≠ 1 := by
    intro hx
    have h1 : ψ x = 1 := by rw [hx, map_one]
    change psiT g0 c x = 1 at h1
    rw [hψx'] at h1
    have h1' : rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZx p (ℓ ^ f) i).val) =
        rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Lˣ) := by
      rw [rootDiagUnit_one]
      exact h1
    have hb : (fun i => ζ ^ (tw6SixZx p (ℓ ^ f) i).val) = 1 :=
      rootDiagUnit_injective h1'
    have h4 := congrFun hb 4
    have hzx4 : tw6SixZx p (ℓ ^ f) 4 = 1 := by simp [tw6SixZx, e6Index]
    rw [hzx4] at h4
    rw [ZMod.val_one] at h4
    exact hζ.ne_one (by omega : 1 < p) (by simpa using h4)
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxpow : x ^ (p : ℤ) = 1 := by
      rw [zpow_natCast]
      exact hAe.2 x hxA
    have hmod : x ^ n = x ^ (n % (p : ℤ)) := zpow_eq_zpow_emod n hxpow
    set m : ℕ := (n % (p : ℤ)).toNat with hm
    have hmz : (m : ℤ) = n % (p : ℤ) := by
      rw [hm]
      exact Int.toNat_of_nonneg (Int.emod_nonneg n (by omega : (p : ℤ) ≠ 0))
    have hxm : x ^ n = x ^ m := by
      rw [hmod, ← hmz, zpow_natCast]
    have hψn : ψ x ^ m = ψ y := by
      rw [← map_pow, ← hxm, hn]
    have hψn' : psiT g0 c x ^ m = psiT g0 c y := hψn
    have hbm : (fun i => ζ ^ (tw6SixZx p (ℓ ^ f) i).val) ^ m =
        (fun i => ζ ^ (tw6SixZy p (ℓ ^ f) i).val) := by
      refine rootDiagUnit_injective ?_
      rw [← rootDiagUnit_pow, ← hψx', ← hψy']
      exact hψn'
    have hker : CFSG.RankThree.E6.rootKernel (tw6SixZx p (ℓ ^ f)) ⊆
        CFSG.RankThree.E6.rootKernel (tw6SixZy p (ℓ ^ f)) := by
      rw [← rootCharKernel_zetaPow hζ, ← rootCharKernel_zetaPow hζ]
      intro α hα
      simp only [rootCharKernel, Set.mem_ofPred_eq] at hα ⊢
      refine ⟨hα.1, ?_⟩
      rw [← hbm, rootChar_pow, hα.2, one_pow]
    have hα : (Pi.single (e6Index 5) 1 : Fin Tag.E6.rank → ℤ) ∈
        CFSG.RankThree.E6.rootKernel (tw6SixZx p (ℓ ^ f)) := by
      rw [CFSG.RankThree.E6.mem_rootKernel]
      refine ⟨IsRoot.basis _, ?_⟩
      rw [charVal]
      rw [Finset.sum_eq_single (e6Index 5)]
      · simp [tw6SixZx, e6Index]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hα' := hker hα
    rw [CFSG.RankThree.E6.mem_rootKernel] at hα'
    have hval : charVal (tw6SixZy p (ℓ ^ f)) (Pi.single (e6Index 5) 1) = 1 := by
      rw [charVal]
      rw [Finset.sum_eq_single (e6Index 5)]
      · rw [Pi.single_eq_same]
        norm_num [tw6SixZy, e6Index]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hval] at hα'
    exact one_ne_zero hα'.2
  have hJx : IsA2A2Kernel (torusRootKernel (psiT g0 c x)) := by
    rw [hψx', tw6SixZetaPow_torusRootKernel hζ]
    exact tw6SixZx_isA2A2Kernel hp5 hq
  have hsubx : parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ torusRootKernel (psiT g0 c x) := by
    rw [hψx', tw6SixZetaPow_torusRootKernel hζ]
    exact tw6SixSupportA2_subset_rootKernel_zx hp5 hq
  have hsuby : parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ torusRootKernel (psiT g0 c y) := by
    rw [hψy', tw6SixZetaPow_torusRootKernel hζ]
    exact tw6SixSupportA2_subset_rootKernel_zy hp5 hq
  exact ⟨x, hxA, y, hyA, hx1, hyx, hJx, tw6SixSupportA2_isA2Kernel, hsubx, hsuby, hψx',
    hψy'⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
