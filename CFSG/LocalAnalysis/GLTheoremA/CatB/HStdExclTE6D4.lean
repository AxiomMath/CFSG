module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6Kac
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoE6D4
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.StandardType.ExcThreeAtTwo
  CFSG.StandardType CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

section Arithmetic

private theorem not_smallOrd_of_two_pow_twelve_dvd {G : Type} [Group G] (I : Subgroup G)
    (h : 2 ^ 12 ∣ Nat.card (↥I ⧸ Subgroup.center ↥I)) : ¬ SmallOrd I := by
  rintro (h1 | h1) <;> rw [h1] at h <;> norm_num at h

end Arithmetic

section Inner


private theorem two_pow_twelve_dvd_of_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} [CharP L 2] {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := isPerfect_componentRootSpan_of_big hτ D (by omega)
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 12 := by omega
  have hdvd := pow_card_dvd_centerQuotient_of_uniEmbed uniEmbed_holds (rootCharHom a) i
    (fixSubfield D.σ) g hg hgk hperf
  rw [hN] at hdvd
  obtain ⟨k, hk1, hkcard⟩ := LayerExcThree.exists_card_eq_two_pow (fixSubfield D.σ)
  rw [hkcard] at hdvd
  rw [← pow_mul] at hdvd
  exact (Nat.pow_dvd_pow 2 (by omega : 12 ≤ k * 12)).trans hdvd

end Inner

section Kac

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

private theorem kc_single24 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 24 →
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 := by
  decide +kernel


private theorem kernelRoots_subset_of_ncard24 {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i := by
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
  have hcnt :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.ncard_kernelRoots_eq_cntB
      hζ w hchar
  have h24 := kc_single24 m0 m1 m2 m3 m4 m5 hsum x hx (hncard.symm.trans hc)
  have hk : (kernelRoots (rootCharHom a)).ncard = 24 := hcnt.trans h24
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  exact (Set.eq_of_subset_of_ncard_le hle (by rw [hk, hc]) hfin).ge

end Kac

section Main


theorem e6TwoD4NotSmall_holds : E6TwoD4NotSmall := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hrank hcard hqs
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact not_smallOrd_of_two_pow_twelve_dvd _
      (two_pow_twelve_dvd_of_inner (Or.inr (Or.inl rfl)) hT hinner hcard)
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  ·
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    exact not_smallOrd_of_ggNotExcThreeOrder _
      (d4Class_ggCQ_E6_two S ⟨Fr, hFr, hΦ'⟩ hq2 hT hap h1 i hrank hcard hqs)
  ·
    obtain ⟨v, hv, hρ'⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3L facts_E6
      kacCount_E6_four (by decide) (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT
      (rootDiagUnit_pow_eq_one_of_forall hap) i hrank hcard
    have hs := componentOrbitLength_eq_one hfin hρ'
    rw [hs, Function.iterate_one] at hinner
    have hsub := kernelRoots_subset_of_ncard24 h3L hap i hcard
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq21 : S.D.q = 2 ^ 1 := by rw [hq2, pow_one]
    obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv (ℓ := 2) (f := 1) S
      ⟨t, ht, Fr, hFr, hΦ⟩ (by norm_num) hq21 (by norm_num) hT hap i v hv hsub hρ' hinner
    haveI := finite_rationalComponent S a i
    have hcardR : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =
        CFSG.Open.orderTrialityD4 (2 ^ 1) := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds _ _ ⟨e⟩
      change _ = CFSG.Open.orderTrialityD4 (TauCeti.PrimePower.card _) at h
      rw [h, TauCeti.PrimePower.card_def]
    have hquot : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) =
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
    have hdvd : 2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      rw [hquot, hcardR]
      unfold CFSG.Open.orderTrialityD4
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _) _
    exact not_smallOrd_of_two_pow_twelve_dvd _ hdvd

end Main

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
