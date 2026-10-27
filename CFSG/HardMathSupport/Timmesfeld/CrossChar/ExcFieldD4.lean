module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial

section D4


theorem fieldCoreAt_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (hdvd : ∀ δ : K ≃+* K, (∀ c, δ c = c ^ ℓ ^ (3 * (f / p))) →
      ¬ Nat.Coprime p (Nat.card (trialityFieldImage σ δ)))
    {x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    FieldCoreAt p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hηp, hpf, ⟨h₀, hconj⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp hp3
      ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp
  obtain ⟨φ, hφ, hφord, hφgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 3 * f) hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφgen⟩
  have hdp : f / p * p = f := Nat.div_mul_cancel hpf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  set d := f / p with hd
  set δc := φ ^ (3 * d) with hδcdef
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * d) := fun c => ringAut_pow_apply_of_frobenius hφ _ c
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * d * p) := by rw [hK3, mul_assoc, hdp]
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp]; exact hσ c
  obtain ⟨hδord, -, -, -, -, hJC, -, hsimple, hnc, ⟨ι', -⟩, -, hNδ, hnormal, hcent, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd1 hp.two_le hm3 K hK' σ
      hσ' δc hδc
  have hδcp : δc ^ p = 1 := by
    rw [hδcdef, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hφord, mul_assoc, hdp]
  set η := Θ x with hηdef
  have hηp' : orderOf η = p := hηp
  have hδcord : orderOf δc = p := by
    refine orderOf_eq_prime hδcp fun h => ?_
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact hp.one_lt.ne hδord
  have hz : Subgroup.zpowers η = Subgroup.zpowers δc := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' hp.pos hδcord
        (by rw [← hηp']; exact pow_orderOf_eq_one η)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' hp.pos hηp' hδcp
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ δc) =
      Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ η) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.D4) σ) η
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.D4) σ) δc
    rw [hz] at h1
    exact h2.symm.trans h1
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have e1 : ((trialityFieldImage σ δc).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃* trialityFieldImage σ δc :=
    Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (trialityFieldImage σ δc) := hsimple
  have hq : CFSG.IsQuasisimple ((trialityFieldImage σ δc).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm (isQuasisimple_of_simple_nonabelian hnc)
  have hcore : FieldCoreAt p (fieldActor (t := TwistTag.D4) σ δc) := by
    refine fieldCoreAt_of_canonical_quasisimple hinj hδord hq hNδ hnormal hcent ?_
    rw [Nat.card_congr e1.toEquiv]
    exact hdvd δc hδc
  exact fieldCoreAt_of_conj (FieldCoreAt.of_zpowers_eq hzA hcore) (MulAut.conj h₀) hconj

theorem not_coprime_card_trialityFieldImage {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) (hpf : p ∣ f)
    (hdq : p ∣ (ℓ ^ f) ^ 6 - 1) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * (f / p))) :
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
  have hd6 : p ∣ (ℓ ^ d) ^ 6 - 1 := by
    have h1 := (ZMod.natCast_eq_zero_iff ((ℓ ^ f) ^ 6 - 1) p).2 hdq
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one, hcast] at h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq01), Nat.cast_pow,
      Nat.cast_one]
    exact h1
  rw [← Nat.Prime.dvd_iff_not_coprime hp, hJ]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd6 _) _

end D4

end CFSG.HardMathSupport.Timmesfeld.CrossChar
