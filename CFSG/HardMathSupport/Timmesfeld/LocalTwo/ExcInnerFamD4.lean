module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamE
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

set_option linter.unusedSectionVars false



theorem not_coprime_card_trialityFieldImage' {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) (hpf : p ∣ f)
    (hdq : p ∣ (ℓ ^ f) ^ 6 - 1 ∨ p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * (f / p))) :
    ¬ Nat.Coprime p (Nat.card (trialityFieldImage σ δ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hdp : f / p * p = f := Nat.div_mul_cancel hpf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  set d := f / p with hd
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hK' : Nat.card K = ℓ ^ (3 * d * p) := by rw [hK3, mul_assoc, hdp]
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp]; exact hσ c
  obtain ⟨-, -, hk0, hσ0, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd1 hp.two_le hm3 K hK' σ
      hσ' δ hδ
  have hK0 : Nat.card (fixSubfield δ) = (ℓ ^ d) ^ 3 := by rw [hk0, ← pow_mul, mul_comm]
  have hr : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hσ0' : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ).toRingHom c =
      c ^ ((ℓ ^ d) ^ (p % 3)) := by
    intro c
    apply Subtype.ext
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ0, SubmonoidClass.coe_pow,
      hσ' (c : K)]
    have h1 : (c : K) ^ ℓ ^ (3 * d) = c := SteinbergBT.pow_card_eq_self_of_mem hk0 c.2
    have h2 : ∀ m : ℕ, (c : K) ^ (ℓ ^ (3 * d)) ^ m = c := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_mul, ih, h1]
    have e : ℓ ^ (d * p) = (ℓ ^ (3 * d)) ^ (p / 3) * (ℓ ^ d) ^ (p % 3) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      calc d * p = d * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
        _ = 3 * d * (p / 3) + d * (p % 3) := by ring
    rw [e, pow_mul, h2]
  obtain ⟨hcard, -⟩ := triality_both_orientations_exact_finite_order ℓ d hℓ hd1 (fixSubfield δ)
    hK0 (p % 3) hr (fixSubfieldRestrict σ δ).toRingHom hσ0'
  have hJ : Nat.card (trialityFieldImage σ δ) = (ℓ ^ d) ^ 12 * ((ℓ ^ d) ^ 2 - 1) *
      ((ℓ ^ d) ^ 6 - 1) * ((ℓ ^ d) ^ 8 + (ℓ ^ d) ^ 4 + 1) := by
    rw [trialityFieldImage, Subgroup.card_map_of_injective (baseChangeGL_injective _), hcard]
  have hcast : ((ℓ ^ f : ℕ) : ZMod p) = ((ℓ ^ d : ℕ) : ZMod p) := by
    rw [← hdp, pow_mul, Nat.cast_pow (ℓ ^ d) p, ZMod.pow_card]
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hq01 : 1 ≤ ℓ ^ d := Nat.one_le_pow _ _ hℓ.pos
  rw [← Nat.Prime.dvd_iff_not_coprime hp, hJ]
  rcases hdq with hdq | hdq
  · have hd6 : p ∣ (ℓ ^ d) ^ 6 - 1 := dvd_pow_sub_one_of_cast_eq hq1 hq01 hcast hdq
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd6 _) _
  · have hd12 : p ∣ (ℓ ^ d) ^ 4 - (ℓ ^ d) ^ 2 + 1 := dvd_phi12_of_cast_eq hq1 hq01 hcast hdq
    have h24 : (ℓ ^ d) ^ 2 ≤ (ℓ ^ d) ^ 4 := Nat.pow_le_pow_right hq01 (by norm_num)
    have hfac : (ℓ ^ d) ^ 8 + (ℓ ^ d) ^ 4 + 1 =
        ((ℓ ^ d) ^ 4 - (ℓ ^ d) ^ 2 + 1) * ((ℓ ^ d) ^ 4 + (ℓ ^ d) ^ 2 + 1) := by
      zify [h24]
      ring
    exact Dvd.dvd.mul_left (by rw [hfac]; exact Dvd.dvd.mul_right hd12 _) _


theorem exists_hom_trialityD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨Θ, hΘ, hker⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ
    exact ⟨Θ, hΘ, hker⟩

theorem crossCharTwoFamCat_D4_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (p : ℕ),
      p.Prime → 7 ≤ p → p ≠ q.p → p ∣ q.card ^ 6 - 1 →
      InnerPlaneBalance p (CatT ⟨.trialityD4 q, hv⟩)) :
    CrossCharTwoFamCat .trialityD4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : Finite (CatT ⟨.trialityD4 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hinjCat := conj_injective_cat_trialityD4 q hv
  have hinj := conj_injective_of_mulEquiv e hinjCat
  have hin : InnerPlaneBalance p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    by_cases h2 : p ∣ q.card ^ 6 - 1
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · exact (innerPlaneBalance_of_rankLE1 hp hinjCat
        (rankLE1_cat_trialityD4 q hv hp (by omega) hpq h2)).of_mulEquiv e.symm
  have hout : OuterFields p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    obtain ⟨Θ, hΘ, hker⟩ := exists_hom_trialityD4 q.prime_p q.exponent_pos K hK σ hσ
    have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
    refine outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx) ?_
    by_cases hpc : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    · refine Or.inr fun x hxp hxo => ?_
      have hx1 : Θ x ≠ 1 := fun h1 => hxo (by
        have h2 : x ∈ Θ.ker := h1
        rw [hker] at h2
        exact h2)
      have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
      have hpf : p ∣ q.exponent := by
        have h3 := dvd_exponent_of_ringAut q.prime_p (by have := q.exponent_pos; omega) hK3 hp hx1
          (by rw [← map_pow, hxp, map_one])
        rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
        · exact h3
      have hdvd' : p ∣ Nat.card (CatT ⟨.trialityD4 q, hv⟩) := by
        rw [Nat.card_congr e.toEquiv]
        exact hpc
      obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
        (by omega) (Ne.symm hpq) (chevalleyModel_cat_trialityD4 hv)).1 hdvd').2.2.2.2 rfl
      have hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
          p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1 := by
        by_cases hd6 : p ∣ (q.p ^ q.exponent) ^ 6 - 1
        · exact Or.inl hd6
        · exact Or.inr (dvd_phi12_of_exhaustion (Nat.one_le_pow _ _ q.prime_p.pos) hd6 hm hd)
      exact fieldCoreAt_D4 q.prime_p q.exponent_pos K hK σ hσ Θ hΘ hp (by omega)
        (fun δ hδ => not_coprime_card_trialityFieldImage' q.prime_p q.exponent_pos K hK σ hσ hp
          (by omega) hpf hdq δ hδ)
        (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
    · exact Or.inl (elemAbelian_card_eq_one_of_not_dvd hp hpc)
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_D4_of_classes
    (h : ∀ e ∈ [1, 2, 3, 6], InnerPlaneBalanceAt .trialityD4 e) :
    CrossCharTwoFamCat .trialityD4 := by
  refine crossCharTwoFamCat_D4_of_planes fun q hv p hp hp7 hpq hd => ?_
  obtain ⟨e, he⟩ : ∃ e, orderOf ((q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hdiv : e ∣ 6 := (dvd_pow_sub_one_iff_orderOf hq1 he).1 hd
  have hmem : e ∈ [1, 2, 3, 6] := by
    have h1 : e ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hdiv, by norm_num⟩
    have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [h6] at h1
    simpa using h1
  exact h e hmem q hv p hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
