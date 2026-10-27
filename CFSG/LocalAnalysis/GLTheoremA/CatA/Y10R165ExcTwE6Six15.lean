module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Rk2Six
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six9
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.SectionRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise


theorem exists_psi_of_kernelLayer_of_torusPoint {C : Type} [Group C] {L : Type} [Field L]
    {ι' : Type} {ι : C →* ModGL Tag.E6 L} {Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L}
    {n g0 : ModGL Tag.E6 L} (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup Tag.E6 L) (hιΦ : ∀ y, Φ (ι y) = ι y)
    (hg0C : g0 ∈ adjointGroup Tag.E6 L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6))
    {h : ModGL Tag.E6 L} (hh : h ∈ twistedTorusOf n Φ)
    {x : C} (hx : orderOf x = p) (c : C)
    (hψx : h = g0⁻¹ * ι (c * x * c⁻¹) * g0)
    {K : Type} [Field K] [Algebra K L]
    (KL : KernelLayer n Φ (torusRootKernel h) K ι') :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL Tag.E6 L,
      Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * y * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel h)) ∧
      (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ i, KL.P i ≤ ψ.range) := by
  classical
  have hS : ∀ α ∈ torusRootKernel h, IsRoot Tag.E6 α := fun _ hα => hα.1
  have hSn : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := by
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
    intro α hα
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    exact ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ (torusRootKernel h)) := by
    rw [mem_subtorusImage_iff, ← hψx]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hle := rootSpan_torusRootKernel_le_centralizer (x := h) (mem_twistedTorusOf.1 hh).1
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, -⟩ :=
    sigma_embedding_data ι hι hιC Φ hιΦ n g0 hg0C hg0 hperf hp hordW hS hSn
      KL.P KL.fin KL.quasi KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup L _)) KL.norm
      (fun y hy hyR hc => by
        obtain ⟨hyH, hyC⟩ := KL.cent y hy hc
        exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩)
      hx c hcS (fun a ha => by rw [← torusRootKernel_rootDiagUnit, ha, ← hψx])
  exact ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩

theorem tw6_exists_psi_of_kernelLayer {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime]
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {x c : twistedE6RootGroup K σ} (hx : orderOf x = p)
    (hh : psiT g0 c x ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {K' ι' : Type} [Field K'] [Algebra K' L]
    (KL : KernelLayer (tw6N L) (twistE6 L (iterateFrobenius L ℓ f))
      (torusRootKernel (psiT g0 c x)) K' ι') :
    ∃ ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = psiT g0 c (y : twistedE6RootGroup K σ)) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔
        rootSpan Tag.E6 L (torusRootKernel (psiT g0 c x))) ∧
      (∀ y, tw6N L * twistE6 L (iterateFrobenius L ℓ f) (ψ y) * (tw6N L)⁻¹ = ψ y) ∧
      (∀ i, KL.P i ≤ ψ.range) := by
  have hcomm : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L ℓ f).comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = iterateFrobenius L ℓ f (algebraMap K L c)
      rw [hσ, map_pow, iterateFrobenius_def]
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩ :=
    exists_psi_of_kernelLayer_of_torusPoint (C := twistedE6RootGroup K σ) (L := L)
      (ι := twE6Emb K σ L) (Φ := twistE6 L (iterateFrobenius L ℓ f)) (n := tw6N L)
      (g0 := g0) (h := psiT g0 c x) twE6Emb_injective twE6Emb_mem (twE6Emb_fixed _ hcomm)
      hg0C hg0 hperf hp (not_dvd_card_weyl_E6 hp hp5) hh hx c rfl (K := K') KL
  refine ⟨ψ, hψinj, ?_, hψHQ, hψR, hPψ⟩
  intro y
  rw [hψ]
  rfl

theorem card_eq_pow_three_of_rk2Ord_six {k : Type} [Field k] {n p : ℕ}
    (hk : Nat.card k = (2 ^ n) ^ 2) (hn : 1 ≤ n) {σ : k ≃+* k}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 6) {H : Type} [Group H] [Finite H]
    {π : H →* ↥(twistedE6RootGroup k σ)} (hpker : ¬ p ∣ Nat.card π.ker)
    {Ã : Subgroup H} (hÃ : IsElemAbelian p Ã) (h3 : 3 ≤ CFSG.Open.pRank p Ã) :
    Nat.card Ã = p ^ 3 ∧ Nat.card (Ã.map π) = p ^ 3 := by
  have hA : Nat.card Ã = p ^ CFSG.Open.pRank p Ã :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hÃ
  have hpq := dvd_two_pow_sq_sub_of_rk2Ord_six hp hp2 hrk
  have hp7 := seven_le_of_rk2Ord_six hp hp2 hrk
  have hp5 : 5 < p := by omega
  have hnd : ¬ p ∣ 2 ^ n := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have he : orderOf (((2 ^ n : ℕ)) : ZMod p) = 6 := by
    rw [Nat.cast_pow]
    exact hrk
  have hSylow : CFSG.LieType.SeitzGeneration.SylowTorus
      (↥(twistedE6RootGroup k σ)) p 3 :=
    CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six Nat.prime_two hn k hk σ hσ
      hp hp7 hnd he
  have hdisj : Disjoint Ã π.ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hA]
    exact Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).2 hpker)
  have hmap : Nat.card (Ã.map π) = Nat.card Ã :=
    CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π hdisj
  have hAle : Nat.card Ã ≤ p ^ 3 := by
    rw [← hmap]
    exact hSylow.rank_le hp (CFSG.SectionRank.isElemAbelian_map hÃ π)
  have hAge : p ^ 3 ≤ Nat.card Ã := by
    rw [hA]
    exact Nat.pow_le_pow_right hp.pos h3
  refine ⟨le_antisymm hAle hAge, ?_⟩
  rw [hmap, le_antisymm hAle hAge]

theorem tw6SixLayerRoots_zero :
    tw6SixLayerRoots tw6SixFrameWeyl 0 = parabolicRoots Tag.E6 tw6SixSupportA2 := by
  rw [tw6SixLayerRoots, Matrix.cons_val_zero, ← tw6SixFrameWeyl_supportA2, Set.image_image]
  simp

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
