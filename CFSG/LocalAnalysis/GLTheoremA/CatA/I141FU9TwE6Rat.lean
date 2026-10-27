module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6D4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.LocalAnalysis.GLTheoremA.HStdExcl

theorem twE6_ne_u38_of_two_pow_dvd {n k : ℕ} (hk : 10 ≤ k) (h : 2 ^ k ∣ n) : n ≠ 5515776 := by
  rintro rfl
  have h10 : 2 ^ 10 ∣ 5515776 := (pow_dvd_pow 2 hk).trans h
  revert h10
  decide

theorem twE6_two_pow_dvd_div {n g m : ℕ} (hg : Odd g) (hgn : g ∣ n) (h : 2 ^ m ∣ n) :
    2 ^ m ∣ n / g := by
  have hcop : Nat.Coprime (2 ^ m) g := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hg)
  have hn : n = g * (n / g) := (Nat.mul_div_cancel' hgn).symm
  rw [hn] at h
  exact hcop.dvd_of_dvd_mul_left h

theorem twE6_psl_card_ne_u38 {k f : ℕ} (hk : 2 ≤ k) (hf : 1 ≤ f) :
    ((2 ^ f) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((2 ^ f) ^ i - 1)) /
      k.gcd (2 ^ f - 1) ≠ 5515776 := by
  have hodd : Odd (2 ^ f - 1) := by
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    rcases this with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  have hg : Odd (k.gcd (2 ^ f - 1)) := Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)
  have hgdvd : k.gcd (2 ^ f - 1) ∣ (2 ^ f) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, ((2 ^ f) ^ i - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have hmem : k ∈ Finset.Icc 2 k := Finset.mem_Icc.2 ⟨hk, le_rfl⟩
    refine ((Nat.gcd_dvd_right k (2 ^ f - 1)).trans ?_).trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ i - 1) hmem)
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ f) k
  have hdvd : 2 ^ (f * (k * (k - 1) / 2)) ∣ (2 ^ f) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, ((2 ^ f) ^ i - 1) := by
    rw [pow_mul]
    exact dvd_mul_right _ _
  have h2 := twE6_two_pow_dvd_div hg hgdvd hdvd
  by_cases h10 : 10 ≤ f * (k * (k - 1) / 2)
  · exact twE6_ne_u38_of_two_pow_dvd h10 h2
  · push Not at h10
    have hk5 : k ≤ 4 := by
      by_contra hk5
      push Not at hk5
      have : 10 ≤ k * (k - 1) / 2 := by
        have h1 : 5 * 4 ≤ k * (k - 1) := Nat.mul_le_mul hk5 (by omega)
        omega
      nlinarith
    interval_cases k
    · have hf9 : f ≤ 9 := by omega
      interval_cases f <;> decide +kernel
    · have hf3 : f ≤ 3 := by omega
      interval_cases f <;> decide +kernel
    · have hf1 : f ≤ 1 := by omega
      interval_cases f
      decide +kernel

theorem twE6_psu_card_eq_u38 {k f : ℕ} (hk : 3 ≤ k) (hf : 1 ≤ f)
    (h : ((2 ^ f) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
        k.gcd (2 ^ f + 1) = 5515776) : k = 3 ∧ f = 3 := by
  have hQ1 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hodd : Odd (k.gcd (2 ^ f + 1)) := by
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right k (2 ^ f + 1))
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hPcast : ((∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => Int.toNat_of_nonneg ?_
    have h1 : (1 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast (by omega))
    have h2 : ((-1 : ℤ)) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
    linarith
  have hgdvd : k.gcd (2 ^ f + 1) ∣ (2 ^ f) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hPcast]
    refine Dvd.dvd.mul_left ?_ _
    have hmem : k ∈ Finset.Icc 2 k := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    refine (?_ : ((k.gcd (2 ^ f + 1) : ℕ) : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ k - (-1) ^ k).trans
      (Finset.dvd_prod_of_mem (fun i => ((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) hmem)
    have h1 : ((k.gcd (2 ^ f + 1) : ℕ) : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) - (-1) := by
      rw [sub_neg_eq_add]
      exact_mod_cast Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right k (2 ^ f + 1))
    exact h1.trans (sub_dvd_pow_sub_pow _ _ k)
  have hdvd : 2 ^ (f * (k * (k - 1) / 2)) ∣ (2 ^ f) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    rw [pow_mul]
    exact dvd_mul_right _ _
  have h2 := twE6_two_pow_dvd_div hodd hgdvd hdvd
  by_cases h10 : 10 ≤ f * (k * (k - 1) / 2)
  · exact absurd h (twE6_ne_u38_of_two_pow_dvd h10 h2)
  · push Not at h10
    have hk5 : k ≤ 4 := by
      by_contra hk5
      push Not at hk5
      have : 10 ≤ k * (k - 1) / 2 := by
        have h1 : 5 * 4 ≤ k * (k - 1) := Nat.mul_le_mul hk5 (by omega)
        omega
      nlinarith
    interval_cases k
    · have hf3 : f ≤ 3 := by omega
      interval_cases f
      · exfalso; revert h; decide +kernel
      · exfalso; revert h; decide +kernel
      · exact ⟨rfl, rfl⟩
    · have hf1 : f ≤ 1 := by omega
      interval_cases f
      exfalso; revert h; decide +kernel

section Inner


theorem twE6_two_pow_dvd_of_inner {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
    {S : LangSetup Tag.E6 L p₀} {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hc : 14 ≤ (componentRoots (rootCharHom a) i).ncard) :
    2 ^ (posRoots (componentRoots (rootCharHom a) i)).ncard ∣
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := isPerfect_componentRootSpan_of_big (Or.inr (Or.inl rfl)) D hc
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  have hdvd := pow_card_dvd_centerQuotient_of_uniEmbed uniEmbed_holds (rootCharHom a) i
    (fixSubfield D.σ) g hg hgk hperf
  obtain ⟨k, hk1, hkcard⟩ := LayerExcThree.exists_card_eq_two_pow (fixSubfield D.σ)
  rw [hkcard, ← pow_mul] at hdvd
  exact (Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_left _ (by omega))).trans hdvd

end Inner

section Kac

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

private theorem twE6_kc_single24 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 24 →
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 := by
  decide +kernel


private theorem twE6_kernelRoots_subset_of_ncard24 {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i := by
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
  have hcnt :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.ncard_kernelRoots_eq_cntB
      hζ w hchar
  have h24 := twE6_kc_single24 m0 m1 m2 m3 m4 m5 hsum x hx (hncard.symm.trans hc)
  have hk : (kernelRoots (rootCharHom a)).ncard = 24 := hcnt.trans h24
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  exact (Set.eq_of_subset_of_ncard_le hle (by rw [hk, hc]) hfin).ge

end Kac

section D4


theorem twE6_d4_ne_u38 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 5515776 := by
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
  · have hdvd := twE6_two_pow_dvd_of_inner hT hinner (by omega)
    have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
    have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
    have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 12 := by omega
    rw [hN] at hdvd
    exact twE6_ne_u38_of_two_pow_dvd (by norm_num) hdvd
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  ·
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    have hfine := omegaMinus8Fine_d4Class_E6_two S ⟨Fr, hFr, hΦ'⟩ hq2 hT hap h1 i hrank hcard
    have hadm := CFSG.Blueprint.LieModel.admissible hfine
    obtain ⟨-, -, hfac⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ _ 4 2 1
      hadm hfine
    have hdvd : 2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      have := Nat.ordProj_dvd (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) 2
      rwa [hfac] at this
    exact twE6_ne_u38_of_two_pow_dvd (by norm_num) hdvd
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
    have hsub := twE6_kernelRoots_subset_of_ncard24 h3L hap i hcard
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
    exact twE6_ne_u38_of_two_pow_dvd (by norm_num) hdvd

end D4

section Orthogonal

theorem twE6_ne_u38_of_lieModel_pOmegaMinus {G : Type} [Group G] {n e : ℕ}
    (h : CFSG.Blueprint.LieModel G .POmegaMinus n 2 e) : Nat.card G ≠ 5515776 := by
  have hn4 : 4 ≤ n := h.admissible.2.2
  have he : 1 ≤ e := h.admissible.2.1
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
    (h.statedClassicalModel (by decide))]
  show CFSG.Open.ordTwistedD n (2 ^ e) ≠ 5515776
  refine twE6_ne_u38_of_two_pow_dvd (k := e * (n * (n - 1))) ?_ ?_
  · have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
    nlinarith
  · rw [pow_mul]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedD n (2 ^ e)

end Orthogonal

section Main


@[expose] def E6TwoRatU38Centre : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀), S.D.q = 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776 →
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141F
