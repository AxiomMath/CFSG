module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuotTransfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuot
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem exists_orderOf_eq_two_quot_nsGlobal {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center (nsGlobal e)))) {P : Type*} [Group P]
    (ψ : nsGlobal e ⧸ center (nsGlobal e) ≃* P) : ∃ y : P, orderOf y = 2 := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2L : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    have hf := factorization_card_statedSp (by omega : 1 ≤ m + 1) hKc (by omega)
    refine Nat.dvd_of_factorization_pos ?_
    rw [hf]
    positivity
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2L
  have hinj := injective_mk_comp_inclusion hLS ht hKt hZ
  refine ⟨ψ ((QuotientGroup.mk' (center (nsGlobal e))).comp (Subgroup.inclusion hLS) x), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective _ hinj, hx]

end Basic

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_quot_unitaryOdd_two (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobalQuot e t .unitaryOdd) (htN : t ∈ normalizer (nsGlobal e : Set G))
    (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ γ : MulAut (nsGlobal e ⧸ center (nsGlobal e)),
      γ * centerQuotAction (nsGlobal e) ⟨t, htN⟩ =
        centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨⟨-, hZ, hty⟩, -⟩ := hglob
  have hty' : LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU (2 * (m + 1) + 1) 2 1 := hty
  have hadm : StatedLieAdmissible .PSU (2 * (m + 1) + 1) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have hq : ¬(2 * (m + 1) + 1 = 3 ∧ 2 ^ 1 = 2) := by omega
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * (m + 1) + 1)) K') :
      Matrix (Fin (2 * (m + 1) + 1)) (Fin (2 * (m + 1) + 1)) K'), orderOf y = 2 →
      1 * (m + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * (m + 1) + 1)) K') :
          Matrix (Fin (2 * (m + 1) + 1)) (Fin (2 * (m + 1) + 1)) K'))))).factorization 2 := by
    intro y hy
    have h1 := le_factorization_card_centralizer_primeFormP_one h y hy
    rw [show (2 * (m + 1) + 1) / 2 = m + 1 by omega,
      show (2 * (m + 1) + 1) % 2 = 1 by omega] at h1
    have h0 : (1 : ℕ).factorization 2 = 0 := by simp
    rw [h0]
    nlinarith
  have hy0 := exists_orderOf_eq_two_quot_nsGlobal hK hm e ht hKt hZ ψ
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  set θt := centerQuotAction (nsGlobal e) ⟨t, htN⟩ with hθt
  set θw := centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩ with hθw
  have hαt : MulAut.congr ψ θt * MulAut.congr ψ θt = 1 := by
    rw [← map_mul, hθt, centerQuotAction_mul_self ht htN, map_one]
  have hαw : MulAut.congr ψ θw * MulAut.congr ψ θw = 1 := by
    rw [← map_mul, hθw, centerQuotAction_mul_self hw2 hg, map_one]
  have hlet : (Nat.card (fixedSubgroup (MulAut.congr ψ θt))).factorization 2 ≤
      1 * (m + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) ht htN).trans
      (factorization_card_fixedSubgroup_le_of_mem hset (by omega) hKc e ht hKt htN)
  have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ θw))).factorization 2 ≤
      1 * (m + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
      (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
  obtain ⟨C₁, hC₁, hc₁, θ₁, he₁⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαt hlet
  obtain ⟨C₂, hC₂, hc₂, θ₂, he₂⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
  have h1 : C₁ = 1 := by
    rcases hc₁ with h1 | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  have h2 : C₂ = 1 := by
    rcases hc₂ with h2 | ⟨r, hr, -⟩
    · exact Units.ext h2
    · omega
  subst h1 h2
  refine exists_mulAut_mul_eq_of_congr ψ (γ := θ₁.symm.trans θ₂) ?_
  rw [he₁, he₂]
  exact symm_trans_mul_congr θ₁ θ₂ _

theorem unique_quot_unitaryOdd_two (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobalQuot e t .unitaryOdd) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) := by
  intro g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨γ, hγ⟩ := exists_conj_quot_unitaryOdd_two hset hK hm e ht hKt hglob htN g hg
  exact mem_normalizer_nsGlobal_of_conj_centerQuotAction hset hK hm e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

theorem exists_conj_quot_unitaryEven_two (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobalQuot e t .unitaryEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    (h2 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ¬ IsCharacteristicP 2
        (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩)))
    (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ γ : MulAut (nsGlobal e ⧸ center (nsGlobal e)),
      γ * centerQuotAction (nsGlobal e) ⟨t, htN⟩ =
        centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨⟨-, hZ, hty⟩, -⟩ := hglob
  have hty' : LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU (2 * (m + 1)) 2 1 := hty
  have hadm : StatedLieAdmissible .PSU (2 * (m + 1)) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have hq : ¬(2 * (m + 1) = 3 ∧ 2 ^ 1 = 2) := by omega
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * (m + 1))) K') :
      Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K'), orderOf y = 2 →
      1 * (m + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * (m + 1))) K') :
          Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K'))))).factorization 2 := by
    intro y hy
    set φ := CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h (2 * (m + 1))
    have h1 := unitaryEvenInnerTwoPart_holds 1 K' h (m + 1) (by omega) (φ y)
      (by rw [MulEquiv.orderOf_eq, hy])
    rw [card_centralizer_map_mulEquiv] at h1
    have h0 : (1 : ℕ).factorization 2 = 0 := by simp
    rw [h0]
    simp only [one_mul] at h1 ⊢
    omega
  have hy0 := exists_orderOf_eq_two_quot_nsGlobal hK hm e ht hKt hZ ψ
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ∃ (C₀ : GL (Fin (2 * (m + 1))) K') (hC₀ : IsPrimeFormGram C₀),
        (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K') =
          blockSwapJ (2 * (m + 1)) (m + 1) ∧
        ∃ θ : primeFormP h (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K') ≃*
            primeFormP h ((1 : GL (Fin (2 * (m + 1))) K') :
              Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K'),
          MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) =
            MulAut.congr θ (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h)) := by
    intro g hg
    have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    have hαw : MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
    have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ
        (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩)))).factorization 2 ≤
          1 * (m + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
        (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
    obtain ⟨C₀, hC₀, hc, θ, he⟩ :=
      exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
    rcases hc with h1 | ⟨r, hr, hJ⟩
    · exfalso
      have hC1 : C₀ = 1 := Units.ext h1
      subst hC1
      apply h2 g hg
      have hch := F4Pilot.isCharacteristicP_fixedSubgroup_fieldBar_one h (n := 2 * (m + 1))
        (by omega) (by omega) (even_two_mul _) (UnitaryPilot.barRingEquiv h)
        (fun x => UnitaryPilot.barRingEquiv_apply h x)
      have Φ := ((fixedSubgroupCongrEquiv ψ _).trans (MulEquiv.subgroupCongr
        (congrArg fixedSubgroup he))).trans (fixedSubgroupCongrEquiv θ _).symm
      exact isCharacteristicP_of_mulEquiv Φ.symm hch
    · obtain rfl : r = m + 1 := by omega
      exact ⟨C₀, hC₀, hJ, θ, he⟩
  obtain ⟨hg1, he1⟩ := centerQuotAction_one_conj htN
  obtain ⟨C₁, hC₁, hJ₁, θ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨C₂, hC₂, hJ₂, θ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ψ (γ := θ₁.symm.trans θ₂) ?_
  rw [h₁, h₂]
  exact symm_trans_mul_congr θ₁ θ₂ _

theorem unique_quot_unitaryEven_two (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobalQuot e t .unitaryEven)
    (h2 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ¬ IsCharacteristicP 2
        (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩))) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) := by
  intro g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨γ, hγ⟩ := exists_conj_quot_unitaryEven_two hset hK hm e ht hKt hglob htN h2 g hg
  exact mem_normalizer_nsGlobal_of_conj_centerQuotAction hset hK hm e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

end Unique

@[expose] def SpTwoUnitaryEvenSecondClassQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k .unitaryEven) → NsRowGlobalQuot e t .unitaryEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ¬ IsCharacteristicP 2
          (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩))

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_unitaryRow_of_quot_of_odd (hset : SeitzSetting G L) {M : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (M : Set G)) {r f : ℕ} (hfo : Odd f)
    (hty : LieModel (M ⧸ center M) .PSU r 2 f)
    (hout : centerQuotAction M ⟨t, htN⟩ ∉ (MulAut.conj : M ⧸ center M →* MulAut _).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (M : Set G) → g ∈ normalizer (M : Set G)) :
    False := by
  have hθθ : centerQuotAction M ⟨t, htN⟩ * centerQuotAction M ⟨t, htN⟩ = 1 :=
    centerQuotAction_mul_self ht htN
  obtain ⟨K', _, h, C₀, hC₀, hm, hq, φ, ε, -, -, hnf⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU hty hθθ hout
  have : Finite K' := h.finite
  have hcard : Nat.card (K' ≃+* K') = 2 * f :=
    (card_ringAut_and_isCyclic Nat.prime_two K' h.card).1
  have : Finite (K' ≃+* K') :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := h.one_le; omega)
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hout
    refine (FixedFourGroup.congr_mem_inner_iff ε _).1 ?_
    rw [hnf, map_one]
    exact one_mem _
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_quotMulAut_hom ε htN ht huniq
    (primeFormFieldFactor h hC₀ hm hq) ?_ (primeFormFieldFactor_conj h hC₀ hm hq) ?_
  · rw [hcard]
    rintro ⟨k, hk⟩
    obtain ⟨j, rfl⟩ := hfo
    omega
  · rw [normalizerQuotMulAut_eq_congr, hnf, primeFormFieldFactor_fieldHom]
    exact hφ1

end Endgame

section Rows

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_nsCoverType_unitaryOdd (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : NsCoverType e .unitaryOdd) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hglob := nsRowGlobalQuot_of_coverType hset hK hm e ht hKt
    (Or.inr (Or.inr (Or.inr rfl))) hcov
  obtain ⟨hout, -⟩ := hglob.2 htN
  exact false_of_unitaryRow_of_quot_of_odd hset ht htN odd_one hglob.1.2.2 hout
    (unique_quot_unitaryOdd_two hset hK hm e ht hKt hglob)

theorem false_of_nsCoverType_unitaryEven (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : NsCoverType e .unitaryEven)
    (h2 : NsRowGlobalQuot e t .unitaryEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ¬ IsCharacteristicP 2
          (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩))) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hglob := nsRowGlobalQuot_of_coverType hset hK hm e ht hKt
    (Or.inr (Or.inl rfl)) hcov
  obtain ⟨hout, -⟩ := hglob.2 htN
  exact false_of_unitaryRow_of_quot_of_odd hset ht htN odd_one hglob.1.2.2 hout
    (unique_quot_unitaryEven_two hset hK hm e ht hKt hglob (h2 hglob))

theorem spTwoRowInput_unitaryOdd_of_coverInput (hc : SpTwoUnitaryCoverInput .unitaryOdd 1) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .unitaryOdd) → False :=
  fun G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot =>
    false_of_nsCoverType_unitaryOdd hset hK (by omega) e ht hKt
      (nsCoverType_of_nsUnitaryCover (Or.inr ⟨rfl, rfl⟩) (by omega)
        (hc G L hset n K hK hn e t ht hKt hroot))

theorem spTwoRowInput_unitaryEven_of_coverInput (hc : SpTwoUnitaryCoverInput .unitaryEven 0)
    (h2 : SpTwoUnitaryEvenSecondClassQuotInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .unitaryEven) → False :=
  fun G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot =>
    false_of_nsCoverType_unitaryEven hset hK (by omega) e ht hKt
      (nsCoverType_of_nsUnitaryCover (Or.inl ⟨rfl, rfl⟩) (by omega)
        (hc G L hset n K hK hn e t ht hKt hroot))
      (fun hglob => h2 G L hset n K hK hn e t ht hKt hroot hglob)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
