module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverStep

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem IsCoverPair.intrinsic (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    {A R : Subgroup X} {m : ℕ} (hP : IsCoverPair A R m) {y : X} (hy : orderOf y = 2)
    (hyR : y ∈ R) (hyK : ∀ l ∈ R, l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 ↥R).map R.subtype) :
    IsTwoComponentIn (gsFixedLayer R y) (centralizer ((A ⊔ zpowers y : Subgroup X) : Set X)) ∧
      y ∈ gsFixedLayer R y ∧
      Nonempty (↥(gsFixedLayer R y) ⧸ Open.fusionZStar ↥(gsFixedLayer R y) ≃*
        alternatingGroup (Fin m)) ∧
      Nat.card (center (↥(gsFixedLayer R y) ⧸ pPrimeCore 2 ↥(gsFixedLayer R y))) ≤ 2 ∧
      ∀ q ∈ coreActionKernel R, q ∈ centralizer ({y} : Set X) →
        q ∈ coreActionKernel (gsFixedLayer R y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRq, hZ2⟩ := hP.coreQuotient hSchur
  obtain ⟨-, -, ⟨hRC, hR⟩, -, -, -, ⟨eR⟩⟩ := hP
  set C := centralizer (A : Set X) with hC
  set T := gsFixedLayer R y with hT
  have hRsub : (R.subgroupOf C).IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hR
    exact h
  have hyN : y ∈ normalizer (R : Set X) := le_normalizer hyR
  have hTpc := UnbalancedCorr.gsFixedLayer_isPComponent hRC hRsub (hRC hyR) hy hyN hRq hyK
  have hCy : centralizer ((A ⊔ zpowers y : Subgroup X) : Set X) = C ⊓ centralizer ({y} : Set X) :=
    centralizer_sup_zpowers A y
  have hTR : T ≤ R := (gsFixedLayer_le_inf R y).trans inf_le_left
  have hsup := gsFixedLayer_sup_map_pPrimeCore hy hRq hyN hyK
  obtain ⟨hcore, φ, -⟩ := restriction_quotient_mulEquiv hTR hsup
  have hmul : (T : Set X) * ((pPrimeCore 2 ↥R).map R.subtype : Set X) = R := by
    rw [← coe_sup_primeCore_eq_mul hTR, hsup]
  refine ⟨⟨?_, ?_⟩, Sol78.mem_gsFixedLayer_of_cover hy hyR hmul,
    ⟨(Sol78.fusionZStarQuotOfCore φ).trans eR⟩, ?_, fun q hq hqy => ?_⟩
  · rw [hCy]
    exact (gsFixedLayer_le_inf R y).trans (inf_le_inf_right _ hRC)
  · rw [hCy]
    exact hTpc
  · have h1 : Nat.card ((center (↥T ⧸ pPrimeCore 2 ↥T)).map φ.toMonoidHom) =
        Nat.card (center (↥T ⧸ pPrimeCore 2 ↥T)) :=
      Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
    rw [Sol78.map_center_eq_of_mulEquiv φ, hZ2] at h1
    omega
  · have hqN : q ∈ normalizer (R : Set X) := (mem_coreActionKernel.mp hq).1
    have hqT : q ∈ normalizer (T : Set X) :=
      TBLit.mem_normalizer_gsFixedLayer hqN (mem_centralizer_singleton_iff.mp hqy)
    refine mem_coreActionKernel.mpr ⟨hqT, fun t ht => ?_⟩
    rw [hcore]
    refine mem_inf.mpr ⟨?_, (mem_coreActionKernel.mp hq).2 t (hTR ht)⟩
    have h1 : q⁻¹ * t * q ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hqT) t).mp ht
      simpa using this
    have e : t⁻¹ * q⁻¹ * t * q = t⁻¹ * (q⁻¹ * t * q) := by group
    rw [e]
    exact mul_mem (inv_mem ht) h1

theorem exists_maximal_step {A S : Subgroup X} (hA2 : IsPGroup 2 A) (hSA : S ≤ A)
    (hne : S ≠ A) :
    ∃ A₀ : Subgroup X, S ≤ A₀ ∧ A₀ ≤ A ∧ ∃ x ∈ A, x ∈ normalizer (A₀ : Set X) ∧
      x ^ 2 ∈ A₀ ∧ x ∉ A₀ ∧ A₀ ⊔ zpowers x = A := by
  classical
  let 𝒮 := {B : Subgroup X // S ≤ B ∧ B ≤ A ∧ B ≠ A}
  have : Nonempty 𝒮 := ⟨⟨S, le_rfl, hSA, hne⟩⟩
  obtain ⟨⟨B, hSB, hBA, hBne⟩, hmax⟩ := Finite.exists_max (fun B : 𝒮 => Nat.card B.1)
  obtain ⟨s, hsA, hsN, hsB, hs2⟩ := Sol76.exists_sq_mem_of_ne hA2 hBA hBne
  refine ⟨B, hSB, hBA, s, hsA, hsN, hs2, hsB, ?_⟩
  by_contra hne'
  have hlt : B < B ⊔ zpowers s :=
    lt_of_le_of_ne le_sup_left fun h => hsB (h ▸ mem_sup_right (mem_zpowers s))
  have h1 : Nat.card ↥(B ⊔ zpowers s) ≤ Nat.card ↥B :=
    hmax ⟨B ⊔ zpowers s, hSB.trans le_sup_left, sup_le hBA (zpowers_le.mpr hsA), hne'⟩
  have h2 := Subgroup.card_lt_of_lt hlt
  omega

theorem measure_lt_of_card_lt {a a' n μ μ' : ℕ} (hμ : μ ≤ n) (ha : a' < a) :
    a' * (n + 1) - μ' < a * (n + 1) - μ := by
  have h1 : a' * (n + 1) + (n + 1) ≤ a * (n + 1) := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ ha
  generalize a' * (n + 1) = p' at *
  generalize a * (n + 1) = p at *
  omega

theorem measure_lt_of_card_le {a a' n μ μ' : ℕ} (hμ' : μ' ≤ n) (ha' : 1 ≤ a') (ha : a' ≤ a)
    (hlt : μ < μ') : a' * (n + 1) - μ' < a * (n + 1) - μ := by
  have h1 : a' * (n + 1) ≤ a * (n + 1) := Nat.mul_le_mul_right _ ha
  have h2 : n + 1 ≤ a' * (n + 1) := by simpa using Nat.mul_le_mul_right (n + 1) ha'
  generalize a' * (n + 1) = p' at *
  generalize a * (n + 1) = p at *
  omega

variable [IsSimpleGroup X]

theorem IsCoverPair.descend (hSig : GSThmB.SolomonSignalizerInput)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {A R : Subgroup X} {m : ℕ} (hP : IsCoverPair A R m) {y : X}
    (hy : orderOf y = 2) (hyA : y ∈ A) (hyR : y ∈ R) :
    ∃ (A₀ M : Subgroup X) (m' : ℕ), IsCoverPair A₀ M m' ∧ Nat.card A₀ < Nat.card A := by
  obtain ⟨hZq, hZ2⟩ := hP.coreQuotient hSchur
  obtain ⟨hA, hA2, hR, hm, hm9, hne, ⟨eR⟩⟩ := hP
  have hyle : zpowers y ≤ A := zpowers_le.mpr hyA
  by_cases hAy : zpowers y = A
  ·
    exfalso
    subst hAy
    have hC := centralizer_zpowers_eq' y
    rw [hC] at hR
    exact hne (hSig X hna hK hz hU y m R hy hm (by omega) hR.1 hR.2 ⟨eR⟩)
  obtain ⟨A₀, hyA₀, hA₀A, x, hxA, hxN, hx2, hxA₀, hsup⟩ := exists_maximal_step hA2 hyle hAy
  have hyA₀' : y ∈ A₀ := hyA₀ (mem_zpowers y)
  have hA₀ne : A₀ ≠ ⊥ := fun h => by
    rw [h, mem_bot] at hyA₀'
    rw [hyA₀', orderOf_one] at hy
    omega
  have hA₀2 : IsPGroup 2 A₀ := hA2.to_le hA₀A
  have hR' : IsTwoComponentIn R (centralizer ((A₀ ⊔ zpowers x : Subgroup X) : Set X)) := by
    rw [hsup]
    exact hR
  obtain ⟨M, hM, hMne, ⟨m', hm'o, hmm', eM⟩, -⟩ := pump_step hSchur hPump hA₀2
    (hA2.to_le (zpowers_le.mpr hxA)) hxN hx2 hxA₀
    (isKGroupCat_centralizer_sup hna hK hA₀ne hA₀2 hxN) hR' hm hm9 ⟨eR⟩ hZ2.le hy hyA₀' hyR
  refine ⟨A₀, M, m', ⟨hA₀ne, hA₀2, hM, hm'o, by omega, hMne, eM⟩, ?_⟩
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hA₀A fun h => hxA₀ (h ▸ hxA))

theorem not_isCoverPair (hSig : GSThmB.SolomonSignalizerInput)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (A R : Subgroup X) (m : ℕ) : ¬ IsCoverPair A R m := by
  classical
  suffices key : ∀ k : ℕ, ∀ (A R : Subgroup X) (m : ℕ), IsCoverPair A R m →
      Nat.card A * (Nat.card X + 1) - coverMeasure A R = k → False from
    fun hP => key _ A R m hP rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro A R m hP hk
    have hμ := coverMeasure_le_card A R
    have hsmall : ∀ (A' R' : Subgroup X) (m' : ℕ), IsCoverPair A' R' m' →
        Nat.card A' < Nat.card A → False := fun A' R' m' hP' hlt =>
      ih _ (hk ▸ measure_lt_of_card_lt hμ hlt) A' R' m' hP' rfl
    have hbig : ∀ (A' R' : Subgroup X) (m' : ℕ), IsCoverPair A' R' m' →
        Nat.card A' ≤ Nat.card A → coverMeasure A R < coverMeasure A' R' → False :=
      fun A' R' m' hP' hle hlt =>
        ih _ (hk ▸ measure_lt_of_card_le (coverMeasure_le_card A' R') Nat.card_pos hle hlt)
          A' R' m' hP' rfl
    by_cases hint : ∃ y : X, orderOf y = 2 ∧ y ∈ A ∧ y ∈ R
    ·
      obtain ⟨y, hy, hyA, hyR⟩ := hint
      obtain ⟨A₀, M, m', hP', hlt⟩ := hP.descend hSig hSchur hPump hna hK hz hU hy hyA hyR
      exact hsmall A₀ M m' hP' hlt
    push Not at hint
    obtain ⟨y, hy, hyR, hyK, Q, hQ, hQD, hQy, hQcard⟩ := hP.exists_sylow_centralizing hSchur
    have hyA : y ∉ A := fun h => hint y hy h hyR
    obtain ⟨hT, hyT, eT, hZT, hQT⟩ := hP.intrinsic hSchur hy hyR hyK
    obtain ⟨hA, hA2, hR, hm, hm9, -, -⟩ := hP
    have hy2 : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
    have hyc : ∀ a ∈ A, a * y = y * a := fun a ha => (mem_centralizer_iff.mp (hR.1 hyR)) a ha
    obtain ⟨A₀, -, hA₀A, x, hxA, hxN, hx2, hxA₀, hsup⟩ :=
      exists_maximal_step hA2 bot_le (Ne.symm hA)
    set B₀ := A₀ ⊔ zpowers y with hB₀
    have hyN : zpowers y ≤ normalizer (A₀ : Set X) :=
      zpowers_le.mpr (centralizer_le_normalizer' A₀ (mem_centralizer_iff.mpr fun a ha =>
        (hyc a (hA₀A ha))))
    have hy2g : IsPGroup 2 (zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
    have hB₀2 : IsPGroup 2 B₀ := by
      have := IsPGroup.to_sup_of_normal_right' hy2g (hA2.to_le hA₀A) hyN
      rwa [sup_comm] at this
    have hyB₀ : y ∈ B₀ := mem_sup_right (mem_zpowers y)
    have hB₀ne : B₀ ≠ ⊥ := fun h => by
      rw [h, mem_bot] at hyB₀
      rw [hyB₀, orderOf_one] at hy
      omega
    have hxy : x * y = y * x := hyc x hxA
    have hxB₀ : x ∈ normalizer (B₀ : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq, hB₀, Subgroup.map_sup,
        mem_normalizer_iff_map_conj_eq.mp hxN, MonoidHom.map_zpowers]
      congr 2
      show x * y * x⁻¹ = y
      rw [hxy, mul_inv_cancel_right]
    have hxnB₀ : x ∉ B₀ := by
      intro h
      obtain ⟨a, ha, w, hw, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hyN h
      rcases OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers hy2 hw with rfl | rfl
      · rw [mul_one] at hxA₀
        exact hxA₀ ha
      · apply hyA
        have h1 := mul_mem (inv_mem (hA₀A ha)) hxA
        rwa [inv_mul_cancel_left] at h1
    have hsupB : B₀ ⊔ zpowers x = A ⊔ zpowers y := by
      rw [hB₀, sup_right_comm, hsup]
    have hT' : IsTwoComponentIn (gsFixedLayer R y)
        (centralizer ((B₀ ⊔ zpowers x : Subgroup X) : Set X)) := by
      rw [hsupB]
      exact hT
    have hB₀A : Nat.card B₀ ≤ Nat.card A := by
      have h1 : Nat.card ↥B₀ * Nat.card ↥(zpowers y ⊓ A₀) = 2 * Nat.card A₀ := by
        have := Sol78.card_sup_mul_card_inf' hyN
        rwa [Nat.card_zpowers, hy, sup_comm] at this
      have h2 : 0 < Nat.card ↥(zpowers y ⊓ A₀) := Nat.card_pos
      have hlt : A₀ < A := lt_of_le_of_ne hA₀A fun h => hxA₀ (h ▸ hxA)
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hA₀A
      have h3 := Subgroup.card_lt_of_lt hlt
      have hApos : 0 < Nat.card A := Nat.card_pos
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · rw [mul_zero] at hc
            omega
          · rw [mul_one] at hc
            omega
        · exact h
      have h4 : 2 * Nat.card A₀ ≤ Nat.card A := by
        rw [hc, mul_comm 2]
        exact Nat.mul_le_mul_left _ hc2
      have h5 : Nat.card ↥B₀ ≤ Nat.card ↥B₀ * Nat.card ↥(zpowers y ⊓ A₀) :=
        Nat.le_mul_of_pos_right _ h2
      omega
    obtain ⟨M, hM, hMne, ⟨m', hm'o, hmm', eM⟩, hcase⟩ := pump_step hSchur hPump hB₀2
      (hA2.to_le (zpowers_le.mpr hxA)) hxB₀ (mem_sup_left hx2) hxnB₀
      (isKGroupCat_centralizer_sup hna hK hB₀ne hB₀2 hxB₀) hT' hm hm9 eT hZT hy hyB₀ hyT
    have hP' : IsCoverPair B₀ M m' := ⟨hB₀ne, hB₀2, hM, hm'o, by omega, hMne, eM⟩
    rcases hcase with hyM | hμ'
    ·
      obtain ⟨A', M', m'', hP'', hlt⟩ :=
        hP'.descend hSig hSchur hPump hna hK hz hU hy hyB₀ hyM
      exact hsmall A' M' m'' hP'' (lt_of_lt_of_le hlt hB₀A)
    ·
      have hyx : y ∉ zpowers (x ^ 2) := fun h =>
        hyA (hA₀A ((zpowers_le.mpr hx2) h))
      have hQB : Q ≤ centralizer ((B₀ ⊔ zpowers x : Subgroup X) : Set X) ⊓
          coreActionKernel (gsFixedLayer R y) := by
        intro q hq
        refine mem_inf.mpr ⟨?_, hQT q (mem_inf.mp (hQD hq)).2 (hQy hq)⟩
        rw [hsupB, centralizer_sup_zpowers]
        exact mem_inf.mpr ⟨(mem_inf.mp (hQD hq)).1, hQy hq⟩
      obtain ⟨P, hP2, hPD, hlt⟩ := hμ' hyx Q hQ hQB
      have h1 := card_le_coverMeasure hP2 hPD
      exact hbig B₀ M m' hP' hB₀A (by omega)

theorem twoGroupAltCoverExclusion_of_inputs (hSig : GSThmB.SolomonSignalizerInput)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput) :
    TwoGroupAltCoverExclusion := by
  intro X _ _ _ hna hK hz hU A m R hA hA2 hm hm9 hRA hR he
  by_contra hne
  exact not_isCoverPair hSig hSchur hPump hna hK hz hU A R m
    ⟨hA, hA2, ⟨hRA, hR⟩, hm, hm9, hne, he⟩

end CFSG.ComponentClassification.SolMax
