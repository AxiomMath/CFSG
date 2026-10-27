module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResInnerTL
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthTwoD
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoElt
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoSL3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.HardMathSupport.Dickson.Sec6
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


private theorem excTLInnerAll_of_a2Facts {τ : Tag} (hfacts : ExcTLA2Facts τ) :
    ∀ (K : Type) [Field K] [Finite K], 4 ≤ Nat.card K →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
      (i : KernelComponent χ), HasA2Pair τ (componentRoots χ i) →
      Group.IsPerfect ↥(componentRootSpan K χ i) →
      ∀ q : ℕ, ¬ IsTypeL2 q ↥(componentRootSpan K χ i) := by
  intro K _ _ h4 M _ χ i hA2 _hperf q hL2
  obtain ⟨γ, hγ, δ, hδ, hsum, h1, h2, h3⟩ := hA2
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγr := hΨ.isRoot γ hγ
  have hδr := hΨ.isRoot δ hδ
  have hs : γ + δ ∈ componentRoots χ i := hΨ.add_mem γ hγ δ hδ hsum
  have hns : -(γ + δ) ∈ componentRoots χ i := hΨ.neg_mem _ hs
  obtain ⟨⟨e, he, hcomm⟩, hcom⟩ := hfacts K hγr hδr hsum h1 h2 h3
  have he0 : (e : K) ≠ 0 := by rcases he with rfl | rfl <;> simp
  obtain ⟨F, _, _, _, ⟨φ⟩⟩ := hL2
  refine excTL_false_of_heis φ (H := Multiplicative K) ?_ (excTLHom hγ) (excTLHom hδ)
    (excTLElt hs (1 : K)) ?_ ?_ ?_ ?_
  · rw [Nat.card_congr Multiplicative.toAdd]
    omega
  · exact excTL_elt_not_central hs hns one_ne_zero
  · intro s
    exact Subtype.ext (hcom (Multiplicative.toAdd s) 0 1).1.eq
  · intro t
    exact Subtype.ext (hcom 0 (Multiplicative.toAdd t) 1).2.eq
  · intro s t hs1 ht1
    have hs0 : Multiplicative.toAdd s ≠ 0 := fun h => hs1 (by simpa using h)
    have ht0 : Multiplicative.toAdd t ≠ 0 := fun h => ht1 (by simpa using h)
    have key : ⁅excTLHom hγ s, excTLHom hδ t⁆ =
        excTLElt hs ((e : K) * Multiplicative.toAdd s * Multiplicative.toAdd t) := by
      refine Subtype.ext ?_
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, excTLHom_coe, excTLElt_coe, pinnedX_neg]
      exact hcomm _ _
    rw [key]
    exact excTL_elt_not_central hs hns (mul_ne_zero (mul_ne_zero he0 hs0) ht0)

private theorem excTL_card_psl2_ge8 {F : Type} [Field F] [Finite F] (hq : 8 ≤ Nat.card F) :
    252 ≤ Nat.card (StatedProj (StatedSL 2 F)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
  have h2 := card_statedSL_two F
  have h3 := excTL_card_scalars_le (F := F)
  change Nat.card (StatedSL 2 F) = Nat.card (StatedProj (StatedSL 2 F)) * _ at h1
  have h4 : 504 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have : 64 ≤ Nat.card F ^ 2 := by nlinarith
    have : 63 ≤ Nat.card F ^ 2 - 1 := by omega
    nlinarith
  have h5 : Nat.card (StatedProj (StatedSL 2 F)) * 2 ≥ 504 := by
    calc 504 ≤ Nat.card (StatedSL 2 F) := by rw [h2]; exact h4
      _ = Nat.card (StatedProj (StatedSL 2 F)) *
            Nat.card ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) := h1
      _ ≤ Nat.card (StatedProj (StatedSL 2 F)) * 2 := Nat.mul_le_mul_left _ h3
  omega

private theorem excTL_false_of_card8 {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) (hq : 8 ≤ Nat.card F)
    (hG : Nat.card G ≤ 168) : False := by
  have h1 := excTL_card_psl2_ge8 hq
  have h2 : Nat.card (G ⧸ Subgroup.center G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center G))
  rw [Nat.card_congr φ.toEquiv] at h2
  omega

private theorem excTLInnerTwoAll_of_ne_G2 {τ : Tag} (hτ : τ ≠ .G2) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
      (i : KernelComponent χ), HasA2Pair τ (componentRoots χ i) →
      Group.IsPerfect ↥(componentRootSpan K χ i) →
      ∀ q : ℕ, 8 ≤ q → ¬ IsTypeL2 q ↥(componentRootSpan K χ i) := by
  intro K _ _ hK M _ χ i hA2 _hperf q hq hL2
  obtain ⟨γ, hγ, δ, hδ, hsum, h1, h2, h3⟩ := hA2
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγr := hΨ.isRoot γ hγ
  have hδr := hΨ.isRoot δ hδ
  obtain ⟨h, nγ, nδ, hform⟩ := excTL_a2_lengths hτ hγr hδr hsum h1 h2 h3
  obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := hL2
  rcases excTL_chain_or_subset hτ hΨ hγ hδ nγ nδ hform with hsub |
      ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, n1, n2, n3, p12, p23, p13⟩
  · obtain ⟨hfin, hcard⟩ := excTL_two_card_le hτ hK hγr hδr nγ nδ hform
      (S := componentRoots χ i) hsub
    haveI : Finite ↥(componentRootSpan K χ i) := hfin
    exact excTL_false_of_card8 φ (by rw [hF]; exact hq) hcard
  · exact excTL_two_false_of_chain hτ hK φ ha₁ ha₂ ha₃ n1 n2 n3 p12 p23 p13


private theorem not_isTypeL2_of_card_lt8 {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : 8 ≤ q)
    (hc : Nat.card Y < 252) : ¬ IsTypeL2 q Y := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card Y hT
  have hM : Nat.card (Y ⧸ Subgroup.center Y) ≤ Nat.card Y :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h3 : 64 * q ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul hq hq]
  rcases Nat.even_or_odd q with he | ho
  · have := (heven he).1
    omega
  · have := hodd ho
    omega

private theorem excres_inner_not_typeL2_all {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    (hL3 : (3 : L) ≠ 0) {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hA2 : HasA2Pair τ (componentRoots (rootCharHom a) i))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) {q : ℕ}
    (hq8 : 8 ≤ q) : ¬ IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hτG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  intro hq
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact hL3 (by simpa using CharP.cast_eq_zero L 3)
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq', ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hperfC : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    by_cases hQ4 : 4 ≤ r ^ (e * s)
    · obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
      exact isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := rootCharHom a) ht i
    · have h2 : r ^ (e * s) = 2 := by
        have h2le : 2 ≤ r ^ (e * s) := hr.two_le.trans (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
        have h3ne : r ^ (e * s) ≠ 3 := fun h3 => hr3 (by
          have := (Nat.prime_three.eq_one_or_self_of_dvd r (by
            rw [← h3]; exact dvd_pow_self r (Nat.mul_pos he hs0).ne')).resolve_left hr.one_lt.ne'
          exact this)
        omega
      exact excres_perfect_of_card_two hτ (K := fixSubfield σ) (by rw [hKcard, h2]) _ i hA2
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  have hqC : IsTypeL2 q ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    have hqR : IsTypeL2 q ↥f.range := p6_isTypeL2_of_equiv (MulEquiv.subgroupCongr hRf.symm) hq
    exact (excres_isTypeL2_of_central_surjection hperfC f.rangeRestrict
      f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)).1 hqR
  by_cases hQ4 : 4 ≤ r ^ (e * s)
  · exact excTLInnerAll_of_a2Facts (excTLA2Facts_of_ne_G2 hτG2) (fixSubfield σ)
      (by rw [hKcard]; exact hQ4) Lˣ (rootCharHom a) i hA2 hperfC q hqC
  · have h2 : r ^ (e * s) = 2 := by
      have h2le : 2 ≤ r ^ (e * s) := hr.two_le.trans (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
      have h3ne : r ^ (e * s) ≠ 3 := fun h3 => hr3 (by
        have := (Nat.prime_three.eq_one_or_self_of_dvd r (by
          rw [← h3]; exact dvd_pow_self r (Nat.mul_pos he hs0).ne')).resolve_left hr.one_lt.ne'
        exact this)
      omega
    exact excTLInnerTwoAll_of_ne_G2 hτG2 (fixSubfield σ) (by rw [hKcard, h2]) Lˣ (rootCharHom a) i
      hA2 hperfC q hq8 hqC


private theorem three_ne_zero_of_rootDiagUnit {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (ha3 : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) : (3 : L) ≠ 0 := by
  intro h3
  apply h1
  have ha1 : ∀ j, a j = 1 := by
    intro j
    have h' : ((a j : L)) ^ 3 = 1 := by
      have := congrArg Units.val (ha3 j)
      simpa using this
    have h0 : ((a j : L) - 1) ^ 3 = 0 := by
      linear_combination h' + (-(a j : L) ^ 2 + (a j : L)) * h3
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0))
  have : a = 1 := funext ha1
  rw [this, rootDiagUnit_one]

private theorem excres_outer_not_typeL2_all {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i ≠ .inner)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) {q : ℕ}
    (hq8 : 8 ≤ q) : ¬ IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  intro hq
  have hL3 : (3 : L) ≠ 0 := three_ne_zero_of_rootDiagUnit ha3 h1
  have hTp : rootDiagUnit τ a ^ 3 = 1 := excOth_rootDiagUnit_pow_eq_one ha3
  cases hk' : twistKind S.ρ (rootCharHom a) i with
  | inner => exact hk hk'
  | exc =>
    obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    obtain ⟨hnin, hA | ⟨hr4, hc24, -⟩⟩ := exc_kind hk'
    · have hNo := ssOth_e6class S Nat.prime_three hL3 hT hTp h1 i hA.1 hA.2 hnin hr
      obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
      exact (hNo F).false e'
    · have hNo := ssOth_d4class S Nat.prime_three hL3 hT hTp h1 i hr4 hc24 hnin hr
      obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
      exact (hNo F).false e'
  | twoD =>
    obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk'
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hτ5 : 5 ≤ τ.rank := h5.trans (compRank_le_rank _)
      have hNo := ssOth_twoD_high S (simplyLaced_of_five_le_rank hτ5) hT i hk' h5 hcard
      obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
      exact (hNo F).false e'
    · have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, h4']
      have hNo := ssOth_d4class S Nat.prime_three hL3 hT hTp h1 i h4' hc hnin hr
      obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
      exact (hNo F).false e'
  | suN =>
    obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    obtain ⟨h2', hn⟩ := suN_rank_ncard hk'
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three hL3 hTp i h2' hn
    obtain ⟨π, hπ⟩ := ssexc_suN_perm S hT i hk' hν hψ hκ hnorm hΨ
    obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
    obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
      ssexc_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq'
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    have hes : 0 < e * s := Nat.mul_pos he hs0
    obtain ⟨hfin, hqsC, hcard⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
    haveI := hfin
    haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Finite.of_injective (Subgroup.inclusion hf1) (Subgroup.inclusion_injective hf1)
    by_cases hne : (ν, r ^ (e * s)) = (3, 2)
    · have h216 := hcard hne
      have hle : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ 216 := by
        calc Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥f.range :=
              Subgroup.card_le_of_le hf1
          _ ≤ Nat.card ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
              Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
          _ = 216 := h216
      exact not_isTypeL2_of_card_lt8 hq8 (by omega) hq
    · have hCperf : Group.IsPerfect ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC hne).1
      have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
        le_antisymm (hf2 hCperf) hf1
      let g : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
          ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
        f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
      have hgsurj : Function.Surjective g := by
        rintro ⟨x, hx⟩
        obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
        exact ⟨c, Subtype.ext hc⟩
      have hgker : g.ker ≤ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
        intro c hc
        apply hfker
        rw [MonoidHom.mem_ker] at hc ⊢
        exact congrArg Subtype.val hc
      have hqC := (excres_isTypeL2_of_central_surjection hCperf g hgsurj hgker).1 hq
      obtain ⟨F, hFcard, ⟨e'⟩⟩ := ssexc_suN_exists_equiv hr hes σQ hσc hν
      have hqS := p6_isTypeL2_of_equiv e'.symm hqC
      haveI : Finite F := Nat.finite_of_card_ne_zero (by
        rw [hFcard]
        exact (pow_pos (pow_pos hr.pos _) 2).ne')
      haveI : CharP F r := charP_of_card_sq hFcard
      have hSU : CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution F r (e * s)) ν =
          StatedSU ν (r ^ (e * s)) F :=
        CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFcard ν
      have hqS' := p6_isTypeL2_of_equiv (MulEquiv.subgroupCongr hSU.symm) hqS
      obtain ⟨F', _, _, _, ⟨φ⟩⟩ := hqS'
      exact excOth_suid_no_psl2 hFcard hν hne φ


theorem excres_class_rankOne_of_typeL2 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hKac : ExcKac τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) {q : ℕ} (hq8 : 8 ≤ q)
    (hRi : IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (componentRoots (rootCharHom a) i).ncard = 2 := by
  by_contra hn
  have hL3 : (3 : L) ≠ 0 := three_ne_zero_of_rootDiagUnit ha3 h1
  obtain ⟨hK1, -, -⟩ := hKac L hL3 a ha3 h1
  rcases hK1 i with hn' | hA2
  · exact hn hn'
  · by_cases hk : twistKind S.ρ (rootCharHom a) i = .inner
    · exact excres_inner_not_typeL2_all hτ hL3 S hT i hk hA2 hQ hq8 hRi
    · exact excres_outer_not_typeL2_all hτ S hT ha3 h1 i hk hQ hq8 hRi

theorem exc_three_components_false {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hKac : ExcKac τ) {L : Type} [Field L] [IsAlgClosed L] (hL3 : (3 : L) ≠ 0) {p₀ : ℕ}
    (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) {q : ℕ} (hq8 : 8 ≤ q)
    {J₁ J₂ J₃ : Subgroup C} (hJ₁ : IsComponentOf J₁ (fixSubgroup β))
    (hJ₂ : IsComponentOf J₂ (fixSubgroup β)) (hJ₃ : IsComponentOf J₃ (fixSubgroup β))
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) (hL₁ : IsTypeL2 q ↥J₁)
    (hL₂ : IsTypeL2 q ↥J₂) (hL₃ : IsTypeL2 q ↥J₃) : False := by
  classical
  have hτG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hTame := langSetup_hTame_of_prime S Nat.prime_three (by exact_mod_cast hL3)
    (fun h => absurd h hτG2) hT ha3 h1
  have hcls : ∀ {J : Subgroup C}, IsComponentOf J (fixSubgroup β) → IsTypeL2 q ↥J →
      ∃ i : KernelComponent (rootCharHom a), J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        (componentRoots (rootCharHom a) i).ncard = 2 := by
    intro J hJ hLJ
    obtain ⟨i, hQi, hJi⟩ := excres_component_eq_rational S Nat.prime_three ι hι hrange β hβ hT ha3
      hTame hJ
    refine ⟨i, hJi, ?_⟩
    have hRi : IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      p6_isTypeL2_of_equiv ((Subgroup.equivMapOfInjective J ι hι).trans
        (MulEquiv.subgroupCongr hJi)) hLJ
    exact excres_class_rankOne_of_typeL2 hτ hKac S hT ha3 h1 i hQi hq8 hRi
  obtain ⟨i₁, hi₁, hn₁⟩ := hcls hJ₁ hL₁
  obtain ⟨i₂, hi₂, hn₂⟩ := hcls hJ₂ hL₂
  obtain ⟨hK1, hK2, hK3⟩ := hKac L hL3 a ha3 h1
  by_cases h48 : τ = .F4 ∨ τ = .E8
  · exact hK2 h48 i₁ hn₁
  · have hE67 : τ = .E6 ∨ τ = .E7 := by
      rcases hτ with h | h | h | h
      · exact absurd (Or.inl h) h48
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inr h) h48
    have hi : i₁ = i₂ := hK3 hE67 i₁ i₂ hn₁ hn₂
    subst hi
    exact h12 (Subgroup.map_injective hι (hi₁.trans hi₂.symm))

end CFSG.LocalAnalysis.GLTheoremA.T1428
