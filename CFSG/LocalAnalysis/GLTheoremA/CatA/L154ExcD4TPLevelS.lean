module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTwoPartDefs
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoF4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrder
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.SLnShape
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import Certificates.Certificate10050
import Certificates.Certificate13660
import Certificates.Certificate1953
import Certificates.Certificate1954
import Certificates.Certificate8117

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)
open CFSG.LocalAnalysis.GLTheoremA.FP (fixNum)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo

theorem l154d4tp_twoPart_two_pow_mul_odd {k u : ℕ} (hu : Odd u) : twoPart (2 ^ k * u) = 2 ^ k := by
  unfold twoPart
  have hu0 : u ≠ 0 := hu.pos.ne'
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hu0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by
      rintro ⟨c, hc⟩
      exact (Nat.not_even_iff_odd.2 hu) ⟨c, by omega⟩), add_zero]

theorem l154d4tp_twoPart_mul_odd {m n : ℕ} (hm : Odd m) (hn : n ≠ 0) :
    twoPart (m * n) = twoPart n := by
  unfold twoPart
  rw [Nat.factorization_mul hm.pos.ne' hn, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by
      rintro ⟨c, hc⟩
      exact (Nat.not_even_iff_odd.2 hm) ⟨c, by omega⟩), zero_add]

theorem l154d4tp_odd_card_of_forall_pow {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : Odd m)
    (h : ∀ x : G, x ^ m = 1) : Odd (Nat.card G) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hcon)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h3 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at h3
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)

theorem l154d4tp_ncard_eq_two_mul_ncard_posRoots
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hfin : Ψ.Finite) : Ψ.ncard = 2 * (posRoots Ψ).ncard := by
  classical
  have hu : Ψ = posRoots Ψ ∪ negRoots Ψ := by
    ext α
    exact ⟨fun hα => (mem_posRoots_or_mem_negRoots hΨ hα).elim Or.inl Or.inr,
      fun h => h.elim (fun h => h.1) fun h => ((mem_negRoots_iff hΨ).1 h).1⟩
  have hdisj : Disjoint (posRoots Ψ) (negRoots Ψ) :=
    Set.disjoint_left.2 fun α h1 h2 => not_mem_negRoots_of_mem_posRoots h1 h2
  have himg : negRoots Ψ = (fun α : Fin τ.rank → ℤ => -α) '' posRoots Ψ := by
    ext α
    refine ⟨fun h => ⟨-α, h, by simp⟩, ?_⟩
    rintro ⟨β, hβ, rfl⟩
    change -(-β) ∈ posRoots Ψ
    rw [neg_neg]
    exact hβ
  have hfp : (posRoots Ψ).Finite := hfin.subset fun α hα => hα.1
  have hfn : (negRoots Ψ).Finite := by rw [himg]; exact hfp.image _
  conv_lhs => rw [hu]
  rw [Set.ncard_union_eq hdisj hfp hfn, himg, Set.ncard_image_of_injective _ neg_injective]
  ring

theorem l154d4tp_odd_center_of_range {C G : Type*} [Group C] [Group G] [Finite C] (f : C →* G)
    {H : Subgroup G} (hH : f.range = H) (hcomm : commutator C = ⊤)
    (hker : f.ker ≤ Subgroup.center C) (hodd : Odd (Nat.card (Subgroup.center C))) :
    Odd (Nat.card (Subgroup.center ↥H)) := by
  subst hH
  have hmap := map_center_of_surjective hcomm f.rangeRestrict f.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict])
  have hd : Nat.card (Subgroup.center ↥f.range) ∣ Nat.card (Subgroup.center C) := by
    rw [← hmap]
    exact Subgroup.card_map_dvd _ _
  exact Odd.of_dvd_nat hodd hd

section Card

variable
  {τ : Tag} {K : Type} [Field K] [Finite K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem l154d4tp_odd_card_componentTorus (i : KernelComponent χ) {s : ℕ} (hs : 1 ≤ s)
    (hK : Nat.card K = 2 ^ s) : Odd (Nat.card (componentTorus K χ i)) := by
  have hQ2 : Even (2 ^ s) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  by_contra hT'
  have h2 : 2 ∣ Nat.card (componentTorus K χ i) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hT')
  have h2' := SmallCompOrder.prime_dvd_sub_one_of_dvd_card_componentTorus (K := K) i
    Nat.prime_two h2
  rw [hK] at h2'
  exact (Nat.not_even_iff_odd.mpr (Nat.Even.sub_odd Nat.one_le_two_pow hQ2 odd_one))
    (even_iff_two_dvd.mpr h2')

theorem l154d4tp_twoPart_card_componentRootSpan (i : KernelComponent χ) {s : ℕ} (hs : 1 ≤ s)
    (hK : Nat.card K = 2 ^ s) :
    twoPart (Nat.card (componentRootSpan K χ i)) =
      2 ^ (s * (posRoots (componentRoots χ i)).ncard) := by
  obtain ⟨d, c, -, hc0, -, -, hcard⟩ :=
    SmallCompOrder.exists_card_componentRootSpan_counts (K := K) i
  have hQ2 : Even (2 ^ s) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd := (l154d4tp_odd_card_componentTorus (K := K) (χ := χ) i hs hK).mul
    (odd_sum_mul_pow_of_even (hK ▸ hQ2) c hc0 (posRoots (componentRoots χ i)).ncard)
  have h : Nat.card (componentRootSpan K χ i) = 2 ^ (s * (posRoots (componentRoots χ i)).ncard) *
      (Nat.card (componentTorus K χ i) * ∑ k ∈ Finset.range
        ((posRoots (componentRoots χ i)).ncard + 1), c k * Nat.card K ^ k) := by
    rw [hcard, hK, ← pow_mul]
    ring
  rw [h]
  exact l154d4tp_twoPart_two_pow_mul_odd hodd

end Card

section LevelS

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154d4tp_levelS (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {s : ℕ}
    (hs : 1 ≤ s) (hq : S.D.q = 2 ^ s)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ s →
      Group.IsPerfect ↥(componentRootSpan K (rootCharHom a) i))
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _)) :
    Odd (Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) ∧
      twoPart (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) = 2 ^ (s * 12) ∧
      twoPart (Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 2 ^ (s * 12) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hΨr : IsRootComponent Ψ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun β hβ => hΨr.isRoot β hβ
  have horb : componentOrbitLength S.ρ Ψ = 1 :=
    componentOrbitLength_eq_one hfin hρ
  have hinner' : twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) := by
    rw [horb, Function.iterate_one]
    exact hinner
  obtain ⟨σ, hfinK, hcardK, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner'
  haveI := hfinK
  rw [horb, pow_one, hq] at hcardK
  have hperf' := hperf ↥(fixSubfield σ) hcardK
  have hN : (posRoots Ψ).ncard = 12 := by
    have := l154d4tp_ncard_eq_two_mul_ncard_posRoots hΨr hfin
    omega
  obtain ⟨u, hu, hCQ⟩ := exists_odd_ggCQ_componentRootSpan i hs hcardK
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperf')) hf1
  have hcomm : commutator ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) = ⊤ :=
    Group.isPerfect_def.1 hperf'
  have hZodd : Odd (Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :=
    l154d4tp_odd_center_of_range f hRf hcomm hker (Odd.of_dvd_nat
      (l154d4tp_odd_card_componentTorus (K := fixSubfield σ) i hs hcardK)
      (SmallCompOrder.card_center_dvd_card_componentTorus (K := fixSubfield σ)
        (χ := rootCharHom a) i))
  have h4 : ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i) = 2 ^ (s * 12) * u := by
    have h := ggCQ_map_of_perfect f hker (Group.IsPerfect.top_iff.mpr hperf')
    rw [← MonoidHom.range_eq_map, hRf, ggCQ_top_subgroup] at h
    rw [h, hCQ, hN]
  refine ⟨hZodd, ?_, ?_⟩
  · have h2 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 2 ^ (s * 12) * u := h4
    rw [h2]
    exact l154d4tp_twoPart_two_pow_mul_odd hu
  · rw [card_eq_ggCQ_mul (rationalComponent S.ρ S.Γ (rootCharHom a) i), h4, mul_assoc]
    exact l154d4tp_twoPart_two_pow_mul_odd (hu.mul hZodd)

end LevelS

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
