module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.LieType.SeitzGeneration.QuasiHigh3
public import CFSG.LieType.SeitzGeneration.UniPlaneCoverLift

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverPar

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.RootWeight CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.LieType.SeitzGeneration.QuasiHigh3

theorem invPairAt_of_normalized_pair {G : Type*} [Group G] {C D : Subgroup G}
    (ι : D →* MulAut C)
    (hι : ∀ (g : D) (s : C), ((ι g s : C) : G) = (g : G) * s * (g : G)⁻¹)
    {E : Subgroup (MulAut C)} (hE : E ≤ ι.range) {p : ℕ} {Q Q' : Subgroup G}
    (hQC : Q ≤ C) (hQ'C : Q' ≤ C) (hQ : ¬ p ∣ Nat.card Q) (hQ' : ¬ p ∣ Nat.card Q')
    (hgen : C ≤ Q ⊔ Q')
    (hAQ : (E.comap ι).map D.subtype ≤ Subgroup.normalizer (Q : Set G))
    (hAQ' : (E.comap ι).map D.subtype ≤ Subgroup.normalizer (Q' : Set G)) :
    QuasiHigh3.InvPairAt p E := by
  have hcardQ : Nat.card (Q.subgroupOf C) = Nat.card Q := by
    rw [← Subgroup.card_subtype C (Q.subgroupOf C),
      Subgroup.map_subgroupOf_eq_of_le hQC]
  have hcardQ' : Nat.card (Q'.subgroupOf C) = Nat.card Q' := by
    rw [← Subgroup.card_subtype C (Q'.subgroupOf C),
      Subgroup.map_subgroupOf_eq_of_le hQ'C]
  refine ⟨Q.subgroupOf C, Q'.subgroupOf C, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardQ]
    exact hQ
  · rw [hcardQ']
    exact hQ'
  · intro φ hφ s hs
    obtain ⟨d, rfl⟩ := hE hφ
    have hdE : d ∈ E.comap ι := by rwa [Subgroup.mem_comap]
    have ha : (d : G) ∈ (E.comap ι).map D.subtype :=
      Subgroup.mem_map_of_mem D.subtype hdE
    have haN : (d : G) ∈ Subgroup.normalizer (Q : Set G) := hAQ ha
    refine Subgroup.mem_subgroupOf.2 ?_
    show ((ι d s : C) : G) ∈ Q
    rw [hι d s]
    exact (Subgroup.mem_normalizer_iff.1 haN (s : G)).1
      (Subgroup.mem_subgroupOf.1 hs)
  · intro φ hφ s hs
    obtain ⟨d, rfl⟩ := hE hφ
    have hdE : d ∈ E.comap ι := by rwa [Subgroup.mem_comap]
    have ha : (d : G) ∈ (E.comap ι).map D.subtype :=
      Subgroup.mem_map_of_mem D.subtype hdE
    have haN : (d : G) ∈ Subgroup.normalizer (Q' : Set G) := hAQ' ha
    refine Subgroup.mem_subgroupOf.2 ?_
    show ((ι d s : C) : G) ∈ Q'
    rw [hι d s]
    exact (Subgroup.mem_normalizer_iff.1 haN (s : G)).1
      (Subgroup.mem_subgroupOf.1 hs)
  · have hmap : (Q.subgroupOf C ⊔ Q'.subgroupOf C).map C.subtype = Q ⊔ Q' := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQC,
        Subgroup.map_subgroupOf_eq_of_le hQ'C]
    rw [eq_top_iff]
    intro s _
    have hs : (s : G) ∈ Q ⊔ Q' := hgen s.2
    rw [← hmap] at hs
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    have hts' : t = s := Subtype.ext hts
    rwa [hts'] at ht

section ParCerts


theorem exists_normalized_radical_pair (τ : Tag) (k : Type) [Field k] [Finite k] (r p : ℕ)
    [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k))
    (hAC : A ≤ innDiagGL τ k) (hAp : IsPGroup p A) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    ∃ Q Q' : Subgroup (ModGL τ k), Q ≤ adjointGroup τ k ∧ Q' ≤ adjointGroup τ k ∧
      IsPGroup r Q ∧ IsPGroup r Q' ∧ adjointGroup τ k ≤ Q ⊔ Q' ∧
      A ≤ Subgroup.normalizer (Q : Set (ModGL τ k)) ∧
      A ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := by
  have := finite_modGL (τ := τ) (K := k)
  set T : Subgroup (ModGL τ k) := (rootDiagUnitHom τ k).range with hT
  have hTC : T ≤ Subgroup.normalizer (adjointGroup τ k : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact (root_diagonal_conjugation τ k b).2.2
  have hTD : T ≤ diagonalGroup := by
    rintro _ ⟨b, rfl⟩
    exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_diagonalGroup b
  obtain ⟨g, hg, l, hl, hJ, hAg⟩ := exists_conj_mem_parabolic_sup_of_normalizes
    (RootWeightDatum.ordinary τ : RootWeightDatum k) r (T := T) hTC hTD hRC hRr hR hAC hAR
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  have hJ' : J ≠ Set.univ := hJ
  set g' : ModGL τ k := g with hg'_def
  have hg' : g' ∈ adjointGroup τ k := hg
  have hAg' : ∀ a ∈ A, g'⁻¹ * a * g' ∈ parabolicSubgroup τ k J ⊔ T := hAg
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  have hnC : canonicalRep (coxeterSystem τ) k w₀ ∈ adjointGroup τ k :=
    canonicalRep_mem_adjointGroup _ k w₀
  set n := canonicalRep (coxeterSystem τ) k w₀
  set Q : Subgroup (ModGL τ k) := parabolicRadical τ k J
  set Q' : Subgroup (ModGL τ k) :=
    (parabolicRadical τ k (δ '' J)).map (MulAut.conj n⁻¹).toMonoidHom
  obtain ⟨-, -, -, hMP, -, hPQM, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ k J
  have hQp : IsPGroup r Q := (hfin r).2.1
  have hQC : Q ≤ adjointGroup τ k := rootSpan_le_adjointGroup k _
  have hMC : parabolicLevi τ k J ≤ adjointGroup τ k :=
    hMP.trans (parabolicSubgroup_le_adjointGroup τ k J)
  have hMQ : parabolicLevi τ k J ≤
      Subgroup.normalizer (Q : Set (ModGL τ k)) :=
    hMP.trans (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hTQ : T ≤ Subgroup.normalizer (Q : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact rootDiagUnit_mem_normalizer_parabolicRadical b J
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin'⟩ :=
    parabolic_root_radical_Levi_factors τ k (δ '' J)
  have hQ'p : IsPGroup r Q' := (hfin' r).2.1.map _
  have hQ'C : Q' ≤ adjointGroup τ k := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnC) (rootSpan_le_adjointGroup k _ hq)) (inv_inv n ▸ hnC)
  have hMQ' : parabolicLevi τ k J ≤
      Subgroup.normalizer (Q' : Set (ModGL τ k)) :=
    parabolicLevi_le_normalizer_opposite hδ J
  have hTQ' : T ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    refine mem_normalizer_map_conj_inv ?_
    change n * rootDiagUnit τ b * n⁻¹ ∈ _
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_normalizer_parabolicRadical _ _
  have hCQ : adjointGroup τ k ≤ Q ⊔ Q' :=
    adjointGroup_le_parabolicRadical_sup_opposite hδinj hδ hJ'
  have hAx : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤
      parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T) := by
    rintro _ ⟨a, ha, rfl⟩
    have h : g'⁻¹ * a * g' ∈ parabolicSubgroup τ k J ⊔ T := hAg' a ha
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine (sup_le (hPQM ▸ sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right) : parabolicSubgroup τ k J ⊔ T ≤
        parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T)) h
  by_cases hA1 : A = ⊥
  · refine ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, ?_, ?_⟩
    · rw [hA1]
      exact bot_le
    · rw [hA1]
      exact bot_le
  · have hPQ : Q ⊔ (parabolicLevi τ k J ⊔ T) ≤
        Subgroup.normalizer (Q : Set (ModGL τ k)) :=
      sup_le Subgroup.le_normalizer (sup_le hMQ hTQ)
    have hpQ : ¬ p ∣ Nat.card Q := not_dvd_card_of_isPGroup hrp hQp
    have hindex : ¬ p ∣ ((parabolicLevi τ k J ⊔ T).subgroupOf
        (Q ⊔ (parabolicLevi τ k J ⊔ T))).index := fun h =>
      hpQ (h.trans (index_subgroupOf_dvd_card_of_sup le_sup_left le_sup_right hPQ
        (sup_comm _ _)))
    have hAxp : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) :=
      IsPGroup.map hAp _
    obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hAx hAxp hindex
    set x : ModGL τ k := y * g'⁻¹
    have hmap : A.map (MulAut.conj x).toMonoidHom =
        (A.map (MulAut.conj g'⁻¹).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.map_map, map_mul]
      rfl
    have hA'' : A.map (MulAut.conj x).toMonoidHom ≤
        parabolicLevi τ k J ⊔ T := hmap ▸ hyA
    have hPC : Q ⊔ (parabolicLevi τ k J ⊔ T) ≤
        Subgroup.normalizer (adjointGroup τ k : Set (ModGL τ k)) :=
      sup_le (hQC.trans Subgroup.le_normalizer)
        (sup_le (hMC.trans Subgroup.le_normalizer) hTC)
    have hxC : x ∈ Subgroup.normalizer (adjointGroup τ k : Set (ModGL τ k)) :=
      Subgroup.mul_mem _ (hPC hy) (Subgroup.le_normalizer (inv_mem hg'))
    exact exists_radical_pair_of_map_conj (G := ModGL τ k) (r := r)
      (C := adjointGroup τ k) (A := A) (x := x) hxC
      ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ,
        hA''.trans (sup_le hMQ hTQ), hA''.trans (sup_le hMQ' hTQ')⟩

theorem invPairAt_of_inndiag {τ : Tag} {k : Type} [Field k] [Finite k] {r p : ℕ}
    [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] {D : Subgroup (ModGL τ k)} (hD : D ≤ innDiagGL τ k)
    (ι : D →* MulAut (adjointGroup τ k))
    (hι : ∀ (g : D) (s : adjointGroup τ k),
      ((ι g s : adjointGroup τ k) : ModGL τ k) =
        (g : ModGL τ k) * (s : ModGL τ k) * (g : ModGL τ k)⁻¹)
    (hinj : Function.Injective ι) {E : Subgroup (MulAut (adjointGroup τ k))}
    (hE : E ≤ ι.range) (hEab : IsElemAbelian p E)
    (hnorm : ∃ R : Subgroup (adjointGroup τ k), R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    QuasiHigh3.InvPairAt p E := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hnorm
  set A : Subgroup (ModGL τ k) := (E.comap ι).map D.subtype with hA
  have hAD : A ≤ D := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  haveI : IsElementaryAbelian p A := isElementaryAbelian_matrixPlane ι hinj hEab
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  set R' : Subgroup (ModGL τ k) := R.map (adjointGroup τ k).subtype with hR'
  have hR'C : R' ≤ adjointGroup τ k := Subgroup.map_subtype_le R
  have hR'p : IsPGroup r R' := IsPGroup.map hRp _
  have hR'1 : R' ≠ ⊥ := fun h => hR1
    ((Subgroup.map_eq_bot_iff_of_injective R (adjointGroup τ k).subtype_injective).1 h)
  have hAR' : A ≤ Subgroup.normalizer (R' : Set (ModGL τ k)) :=
    matrixPlane_le_normalizer ι hι hRn
  obtain ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hgen, hAQ, hAQ'⟩ :=
    exists_normalized_radical_pair τ k r p hrp A (hAD.trans hD) hAp R' hR'C hR'p hR'1 hAR'
  exact invPairAt_of_normalized_pair ι hι hE hQC hQ'C
    (not_dvd_card_of_isPGroup hrp hQp) (not_dvd_card_of_isPGroup hrp hQ'p) hgen hAQ hAQ'

theorem invPairAt_e6_of_normalizesR {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hEab : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag K) (hnorm : E6NormalizesR K E) :
    QuasiHigh3.InvPairAt 3 E := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (adjointGroup Tag.E6 K) :=
    CFSG.SeitzReduction.E6Pilot.isSimpleGroup_adjointGroup_E6
  by_cases hK4 : 4 ≤ Nat.card K
  · exact invPairAt_of_inndiag hK3 (D := e6InndiagGL K) le_rfl (e6InndiagConj K)
      (fun g s => e6InndiagConj_apply g s) (e6InndiagConj_injective K hK4)
      (by rw [range_e6InndiagConj]; exact hEd) hEab hnorm
  · have hinn := e6Inndiag_eq_innerAut_of_lt_four K hK3 hK4
    exact invPairAt_of_inndiag hK3 (D := adjointGroup Tag.E6 K) le_sup_left MulAut.conj
      (fun g s => rfl) (CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot)
      (hEd.trans hinn.le) hEab hnorm

theorem invP'Pair_of_e6Inndiag {K : Type*} [Group K] {k : Type} [Field k] [Finite k]
    (hk3 : ringChar k ≠ 3) (e : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hEd : coverImage e E ≤ e6Inndiag k) (hnorm : E6NormalizesR k (coverImage e E)) :
    QuasiHigh2.InvP'Pair 3 E := by
  refine QuasiHigh3.invP'Pair_of_invPairAt_model e ?_
  change QuasiHigh3.InvPairAt 3 (coverImage e E)
  exact invPairAt_e6_of_normalizesR hk3 (isElemAbelian_coverImage e hE) hEd hnorm

end ParCerts

section TwCerts


theorem invPairAt_twE6_of_normalizesR {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK3 : ringChar K ≠ 3) (hσq : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hEab : IsElemAbelian 3 E)
    (hEd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hnorm : TwE6NormalizesR K σ E) :
    QuasiHigh3.InvPairAt 3 E := by
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq : q ≤ 1 := by omega
    have h1 : Nat.card K ≤ 1 := by
      rw [hKq]
      nlinarith [Nat.zero_le q]
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨hp, f, hf, rfl⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hσ : σ ^ TwistTag.E6.order = 1 := by
    have hsq : σ ^ 2 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hσσ : σ (σ c) = c := by
        haveI := Fintype.ofFinite K
        rw [hσq (σ c), hσq c, ← pow_mul, ← sq, ← hKq, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using hσσ
    exact hsq
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  have hinj := twistedE6InndiagConj_injective hp hf hKq σ hσq
  have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hEd
  obtain ⟨R, hR1, hRp, hRn⟩ := hnorm
  set A : Subgroup (ModGL TwistTag.E6.tag K) :=
    (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype with hA
  have hAEA : IsElementaryAbelian 3 A :=
    isElementaryAbelian_matrixPlane (twistedE6InndiagConj K σ) hinj hEab
  have hAp : IsPGroup 3 A := IsElementaryAbelian.isPGroup 3 A
  have hAC : A ≤ twistedE6InndiagGL K σ := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  set R' : Subgroup (ModGL TwistTag.E6.tag K) :=
    R.map (twistedE6RootGroup K σ).subtype with hR'
  have hR'C : R' ≤ twistedE6RootGroup K σ := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hR'p : IsPGroup (ringChar K) R' := hRp.map _
  have hR'1 : R' ≠ ⊥ := fun h =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective R
      (twistedE6RootGroup K σ).subtype_injective).1 h)
  have hAR' : A ≤ Subgroup.normalizer (R' : Set (ModGL TwistTag.E6.tag K)) :=
    matrixPlane_le_normalizer (twistedE6InndiagConj K σ)
      (fun g s => twistedE6InndiagConj_apply g s) hRn
  obtain ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, hAQ, hAQ'⟩ :=
    exists_radical_pair_twE6Inndiag K σ hσ f hp hf hK3 hσq hKq A hAC hAp R' hR'C hR'p hR'1 hAR'
  refine invPairAt_of_normalized_pair (G := ModGL TwistTag.E6.tag K)
    (C := twistedE6RootGroup K σ) (D := twistedE6InndiagGL K σ)
    (twistedE6InndiagConj K σ) (fun g s => twistedE6InndiagConj_apply g s) hEr
    hQC hQ'C ?_ ?_ hCQ hAQ hAQ'
  · exact not_dvd_card_of_isPGroup hK3 hQp
  · exact not_dvd_card_of_isPGroup hK3 hQ'p

theorem invP'Pair_of_twE6Inndiag {K : Type*} [Group K] {k : Type} [Field k] [Finite k]
    (σ : k ≃+* k) {q : ℕ} (hk3 : ringChar k ≠ 3) (hσq : ∀ c, σ c = c ^ q)
    (hkq : Nat.card k = q ^ 2)
    (e : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hEd : coverImage e E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ)
    (hnorm : TwE6NormalizesR k σ (coverImage e E)) : QuasiHigh2.InvP'Pair 3 E := by
  refine QuasiHigh3.invP'Pair_of_invPairAt_model e ?_
  change QuasiHigh3.InvPairAt 3 (coverImage e E)
  exact invPairAt_twE6_of_normalizesR σ hk3 hσq hkq (isElemAbelian_coverImage e hE) hEd hnorm

end TwCerts

end CFSG.LieType.SeitzGeneration.CubeCoverPar

