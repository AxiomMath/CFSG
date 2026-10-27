module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley

theorem dvd_card_of_not_rankLE2 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ¬ RankLE2 p G) : p ∣ Nat.card G := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [RankLE2, not_forall, not_le] at h
  obtain ⟨F, hF, hcard⟩ := h
  have hFp : IsPGroup p F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at hcard
    exact absurd hcard (not_lt.2 (Nat.one_le_pow _ _ hp.pos))
  exact (dvd_pow_self p hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card F)

section TwE6


theorem crossCharFamAt_twistedE6_ge_three_of_inner
    (h : CrossCharInnerAt .twistedE6 fun idx p => ∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) :
    CrossCharFamAt .twistedE6 fun idx p => ∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt, hp5⟩
  have hin := h ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt, hp5⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hqc] at hcnt
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hin' : IsInnerLocallyBalanced p (twistedE6RootGroup K σ) := hin.of_mulEquiv e.symm
  refine IsLocallyBalancedAbs.of_mulEquiv e ?_
  by_cases hpf : p ∣ q.exponent
  · obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK
        σ hσ
    refine isLocallyBalancedAbs_of_inner_of_fieldCore hp hinj hin' fun x hxp hxo => ?_
    have : Fact p.Prime := ⟨hp⟩
    refine fieldCoreAt_twistedE6 q.prime_p q.exponent_pos K hK2 σ hσ Θ hΘ hp (by omega) ?_
      (orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)) hxo
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
    have hcnt' : 3 ≤ degCountTw (orderOf (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p)) := by
      rw [← hcast]
      exact hcnt
    have hpq0 : ¬ p ∣ q.p ^ (q.exponent / p) := fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
    have : Finite (ModGL TwistTag.E6.tag (fixSubfield κ)) := finite_modGL
    have : Finite (twistedE6RootGroup (fixSubfield κ) σ₀) := Subtype.finite
    have hcard : Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) =
        Nat.card (twistedE6RootGroup (fixSubfield κ) σ₀) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [hcard, ← Nat.Prime.dvd_iff_not_coprime hp]
    exact dvd_card_of_not_rankLE2 hp (not_rankLE2_twistedE6 q.prime_p hd1 (fixSubfield κ) hk2 σ₀
      hσ₀' hp (by omega) hpq0 hcnt')
  · obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp
      (by omega)
    have hK2' : Nat.card K = q.p ^ (q.exponent * 2) := by rw [hK, ← pow_mul]
    obtain ⟨-, -, -, -, hcardA, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        q.prime_p (by have := q.exponent_pos; omega) hK2'
    have hcop : Nat.Coprime p (Nat.card (RingAut K)) := by
      rw [hcardA]
      exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpf)
        (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
    intro D hD hcardD H hH hDH
    exact hin' D hD hcardD (le_innerAut_of_hom (MulEquiv.refl _) Θ hcop hΘ hD.2) H hH hDH

end TwE6

section Open


theorem crossCharFamAt_twistedE6_open_of_inner
    (h5 : CrossCharInnerAt .twistedE6 fun idx p => ∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p)
    (h3 : CrossCharFamAt .twistedE6 fun _ p => p = 3) :
    CrossCharFamAt .twistedE6 fun idx p =>
      ¬ regimeExcVac TauCeti.LieTypeIndex.twistedE6 degCountTw idx p := by
  refine crossCharFamAt_twistedE6_open_of_ge_three fun idx hk p hp hp2 hc ⟨q, hq, hcnt⟩ => ?_
  rcases eq_three_or_five_le hp hp2 with rfl | hp5
  · exact h3 idx hk 3 hp hp2 hc rfl
  · exact crossCharFamAt_twistedE6_ge_three_of_inner h5 idx hk p hp hp2 hc ⟨q, hq, hcnt, hp5⟩

end Open

end CFSG.HardMathSupport.Timmesfeld.CrossChar
