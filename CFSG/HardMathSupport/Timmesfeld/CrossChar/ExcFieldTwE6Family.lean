module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTwistedE6

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Chevalley

section TwE6Order


theorem not_coprime_card_twistedE6 {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (k : Type) [Field k]
    (hk : Nat.card k = (ℓ ^ d) ^ 2) (σ₀ : k ≃+* k) (hσ₀ : ∀ c, σ₀ c = c ^ (ℓ ^ d))
    (hp : p.Prime) (hcnt : degCountTw (orderOf (((ℓ ^ d : ℕ)) : ZMod p)) = 2) :
    ¬ Nat.Coprime p (Nat.card (twistedE6RootGroup k σ₀)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero 2 (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  have : Finite (twistedE6RootGroup k σ₀) := Subtype.finite
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ d : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCountTw_eq_two hcnt with rfl | rfl
  · exact not_coprime_card_of_sylowTorus (sylowTorus_twistedE6_three hℓ hd k hk σ₀ hσ₀ hp he) hp
      (by norm_num)
  · exact not_coprime_card_of_sylowTorus (sylowTorus_twistedE6_four hℓ hd k hk σ₀ hσ₀ hp he) hp
      (by norm_num)

end TwE6Order

section TwE6Family


theorem crossCharFamAt_twistedE6_field :
    CrossCharFamAt .twistedE6 (regimeExcField TauCeti.LieTypeIndex.twistedE6 degCountTw) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (a := degCountTw) (by decide) hp hp2
    (not_dvd_card_of_ne hp hpq) hcnt.le
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hqc] at hcnt
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hr : RankLE2 p (twistedE6RootGroup K σ) :=
    RankLE2.of_mulEquiv e (rankLE2_cat_twistedE6 q hv hp (by rw [hqc]; exact hcnt))
  refine IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_of_fieldCore hp hinj
    (fun D hD hcard hin => false_of_inner_cube_of_rankLE2 hp hinj hr hD hcard hin) ?_)
  intro x hxp hxo
  have : Fact p.Prime := ⟨hp⟩
  refine fieldCoreAt_twistedE6 q.prime_p q.exponent_pos K hK2 σ hσ Θ hΘ hp (by omega) ?_
    (orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)) hxo
  intro κ hκ σ₀ hσ₀ hkcard
  have hdvdf : p ∣ q.exponent := hpf
  have hdp : q.exponent / p * p = q.exponent := Nat.div_mul_cancel hdvdf
  have hd1 : 1 ≤ q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hdvdf) hp.pos
  have : Finite (fixSubfield κ) := Subtype.finite
  have hk2 : Nat.card (fixSubfield κ) = (q.p ^ (q.exponent / p)) ^ 2 := by
    rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ (q.p ^ (q.exponent / p)) := fun c =>
    Subtype.ext (by rw [hσ₀ c, SubmonoidClass.coe_pow])
  have hcast : (((q.p ^ q.exponent : ℕ)) : ZMod p) =
      (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p) := by
    conv_lhs => rw [← hdp, pow_mul, Nat.cast_pow (q.p ^ (q.exponent / p)) p, ZMod.pow_card]
  have hcnt' : degCountTw (orderOf (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p)) = 2 := by
    rw [← hcast]
    exact hcnt
  have hcard : Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) =
      Nat.card (twistedE6RootGroup (fixSubfield κ) σ₀) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective _)
  rw [hcard]
  exact not_coprime_card_twistedE6 q.prime_p hd1 (fixSubfield κ) hk2 σ₀ hσ₀' hp hcnt'

end TwE6Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
