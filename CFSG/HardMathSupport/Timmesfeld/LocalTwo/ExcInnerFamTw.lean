module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamE
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldTwE6
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

set_option linter.unusedSectionVars false

theorem degCountTw_ge_two {e : ℕ} (h : 2 ≤ degCountTw e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h60 := le_sixty_of_degCountTw_pos (e := e) (by omega)
  have key : ∀ e ≤ 60, 2 ≤ degCountTw e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h60 h



theorem not_coprime_card_twistedE6_of_pos {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (k : Type)
    [Field k] [Finite k] (hk : Nat.card k = (ℓ ^ d) ^ 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c, σ₀ c = c ^ (ℓ ^ d)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ d)
    (hpos : 0 < degCountTw (orderOf (((ℓ ^ d : ℕ)) : ZMod p))) :
    ¬ Nat.Coprime p (Nat.card (twistedE6RootGroup k σ₀)) := by
  rw [← Nat.Prime.dvd_iff_not_coprime hp]
  by_contra hnd
  have hp3 : 3 < p := by omega
  have h1 := ordProj_card_twistedE6 hℓ hd k hk σ₀ hσ₀ hp hp3 hpq
  rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at h1
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ d : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hpos
  obtain ⟨dd, hdd, hed⟩ := exists_degree_of_degCount_pos (τ := Tag.E6) (e := ennola e) hpos
  have hQ := orderOf_neg_natCast_zmod hp (by omega) hpq he
  set Q : ℤ := -((ℓ ^ d : ℕ) : ℤ) with hQdef
  have hq2 : 2 ≤ ℓ ^ d := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hQa : Q.natAbs = ℓ ^ d := by simp [hQdef]
  have hdd0 : dd ≠ 0 := by
    have : ∀ x ∈ degreesW Tag.E6, x ≠ 0 := by decide
    exact this dd hdd
  have hne : (Q ^ dd - 1).natAbs ≠ 0 := by
    intro h0
    have h1 : Q ^ dd = 1 := by omega
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, hQa] at h2
    rcases Nat.pow_eq_one.1 h2 with h3 | h3
    · omega
    · exact hdd0 h3
  have hdvdZ : (p : ℤ) ∣ Q ^ dd - 1 := by
    have hpow : (Q : ZMod p) ^ dd = 1 := orderOf_dvd_iff_pow_eq_one.1 (hQ ▸ hed)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hpow]
    simp
  have hdvdN : p ∣ (Q ^ dd - 1).natAbs := Int.natCast_dvd.1 hdvdZ
  have hv := Nat.Prime.factorization_pos_of_dvd hp hne hdvdN
  have hmem : p ^ (((Q ^ dd - 1).natAbs).factorization p) ∈
      (degreesE Tag.E6).map fun d => p ^ (((Q ^ d - 1).natAbs).factorization p) :=
    List.mem_map.2 ⟨dd, hdd, rfl⟩
  have hdiv := List.dvd_prod hmem
  rw [← h1] at hdiv
  have hone := Nat.dvd_one.1 hdiv
  rw [Nat.pow_eq_one] at hone
  rcases hone with h | h
  · exact hp.one_lt.ne' h
  · omega

theorem exists_hom_twistedE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K,
      (∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor σ δ → Θ α = δ) ∧
      ∀ x ∈ Θ.ker, x ^ p = 1 →
        x ∈ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  refine ⟨Θ, hΘ, fun x hx hxp => ?_⟩
  rw [hker] at hx
  set J := twistedE6Inn K σ ⊔ twistedE6Diag K σ with hJ
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hxp' : (⟨x, hx⟩ : J) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have ha : (QuotientGroup.mk ⟨x, hx⟩ : J ⧸ (twistedE6Inn K σ).subgroupOf J) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1
      ⟨hcube _, by rw [← QuotientGroup.mk_pow, hxp', QuotientGroup.mk_one]⟩
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ha)

theorem crossCharTwoFamCat_twistedE6_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (p : ℕ),
      p.Prime → 7 ≤ p → p ≠ q.p → 2 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) →
      InnerPlaneBalance p (CatT ⟨.twistedE6 q, hv⟩)) :
    CrossCharTwoFamCat .twistedE6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hpq0 : ¬ p ∣ q.p ^ q.exponent := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  have hinjCat := conj_injective_cat_twistedE6 q hv
  have hinj := conj_injective_of_mulEquiv e hinjCat
  have hin : InnerPlaneBalance p (twistedE6RootGroup K σ) := by
    by_cases h2 : 2 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · exact (innerPlaneBalance_of_rankLE1 hp hinjCat
        (rankLE1_cat_twistedE6 q hv hp hpq (by omega))).of_mulEquiv e.symm
  have hout : OuterFields p (twistedE6RootGroup K σ) := by
    obtain ⟨Θ, hΘ, hker⟩ := exists_hom_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp
      (by omega)
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    refine outerFields_of_hom Θ hp hinj (fun x hx hxp => hker x hx hxp) ?_
    by_cases h0 : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 0
    · refine Or.inl fun F hF => ?_
      rw [hqc] at h0
      exact elemAbelian_card_eq_one_of_degCountTw_zero q.prime_p q.exponent_pos K hK σ hσ hp
        (by omega) hpq0 rfl h0 hF
    · refine Or.inr fun x hxp hxo => ?_
      have hxord := orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo
      have hx1 : Θ x ≠ 1 := fun h1 => hxo (hker x h1 hxp)
      have hpf : p ∣ q.exponent := by
        have h3 := dvd_exponent_of_ringAut q.prime_p (n := 2 * q.exponent)
          (by have := q.exponent_pos; omega) hK2 hp hx1 (by rw [← map_pow, hxp, map_one])
        rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
        · exact h3
      have hpos := Nat.pos_of_ne_zero h0
      refine fieldCoreAt_twistedE6 q.prime_p q.exponent_pos K hK2 σ hσ Θ hΘ hp (by omega) ?_
        hxord hxo
      intro κ hκ σ₀ hσ₀ hkcard
      have hdp : q.exponent / p * p = q.exponent := Nat.div_mul_cancel hpf
      have hd1 : 1 ≤ q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
      have : Finite (fixSubfield κ) := Subtype.finite
      have hk2 : Nat.card (fixSubfield κ) = (q.p ^ (q.exponent / p)) ^ 2 := by
        rw [hkcard, ← pow_mul, mul_comm]
      have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ (q.p ^ (q.exponent / p)) := fun c =>
        Subtype.ext (by rw [hσ₀ c, SubmonoidClass.coe_pow])
      have hcast : (((q.p ^ q.exponent : ℕ)) : ZMod p) =
          (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p) := by
        conv_lhs => rw [← hdp, pow_mul, Nat.cast_pow (q.p ^ (q.exponent / p)) p, ZMod.pow_card]
      have hcnt' : 0 < degCountTw (orderOf (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p)) := by
        rw [← hcast, ← hqc]
        exact hpos
      have hpq1 : ¬ p ∣ q.p ^ (q.exponent / p) := fun h =>
        hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
      have : Finite (ModGL TwistTag.E6.tag (fixSubfield κ)) := finite_modGL
      have : Finite (twistedE6RootGroup (fixSubfield κ) σ₀) := Subtype.finite
      have hcard : Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) =
          Nat.card (twistedE6RootGroup (fixSubfield κ) σ₀) :=
        Subgroup.card_map_of_injective (baseChangeGL_injective _)
      rw [hcard]
      exact not_coprime_card_twistedE6_of_pos q.prime_p hd1 (fixSubfield κ) hk2 σ₀ hσ₀' hp
        (by omega) hpq1 hcnt'
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_twistedE6_of_classes
    (h : ∀ e ∈ [1, 2, 3, 4, 6], InnerPlaneBalanceAt .twistedE6 e) :
    CrossCharTwoFamCat .twistedE6 := by
  refine crossCharTwoFamCat_twistedE6_of_planes fun q hv p hp hp7 hpq h2 => ?_
  have := degCountTw_ge_two h2
  rcases this with he | he | he | he | he <;>
    exact h _ (by simp) q hv p hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
