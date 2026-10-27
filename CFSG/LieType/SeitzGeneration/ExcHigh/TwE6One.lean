module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E6Low

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.Timmesfeld.ExceptionalOrders

section TorusIndex


theorem index_graphFixedRootTorus_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (σ : K →+* K) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).index =
      (ℓ ^ f) ^ 36 * (geomSum 2 2 (ℓ ^ f) * geomSum 3 2 (ℓ ^ f) *
        (geomSum 2 5 (ℓ ^ f) * geomSum 2 3 (ℓ ^ f) * geomSum 2 1 (ℓ ^ f)) *
          (geomSum 2 9 (ℓ ^ f) * geomSum 2 6 (ℓ ^ f) * geomSum 2 4 (ℓ ^ f) *
            geomSum 3 1 (ℓ ^ f))) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField (t := TwistTag.E6) hℓ hf hK hσ
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6,
    ← graphFixedRootTorus_eq_compatTorus hsurj] at hC
  have hcard := Subgroup.card_mul_index ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (graphFixedRootTorus_le TwistTag.E6 K σ)).toEquiv, hC, mul_assoc] at hcard
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard

theorem not_dvd_index_graphFixedRootTorus_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (σ : K →+* K) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f - 1) :
    ¬ p ∣ ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).index := by
  rw [index_graphFixedRootTorus_twistedE6 hℓ hf σ hK hσ]
  have : Fact p.Prime := ⟨hp⟩
  set Q := ℓ ^ f with hQ
  intro hd
  have h1 : 1 ≤ Q := Nat.one_le_pow _ _ hℓ.pos
  have hq1 : ((Q : ℕ) : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at this
    exact this
  have key : ((Q ^ 36 * (geomSum 2 2 Q * geomSum 3 2 Q *
      (geomSum 2 5 Q * geomSum 2 3 Q * geomSum 2 1 Q) *
        (geomSum 2 9 Q * geomSum 2 6 Q * geomSum 2 4 Q * geomSum 3 1 Q)) : ℕ) : ZMod p) =
        ((1152 : ℕ) : ZMod p) := by
    simp only [Nat.cast_mul, Nat.cast_pow, geomSum_cast_of_cast_eq_one _ _ _ hq1, hq1, one_pow,
      one_mul]
    norm_num
  have h1152 : p ∣ 1152 := by
    refine (ZMod.natCast_eq_zero_iff 1152 p).1 ?_
    rw [← key]
    exact (ZMod.natCast_eq_zero_iff _ p).2 hd
  have h2 : p ∣ 2 ^ 7 * 3 ^ 2 := by norm_num; exact h1152
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    omega

end TorusIndex

section Normalizer


theorem graphFixedRootTorus_conj_mem_posUnipotent (K : Type) [Field K] (σ : K →+* K)
    {x u : ModGL TwistTag.E6.tag K} (hx : x ∈ graphFixedRootTorus TwistTag.E6 K σ)
    (hu : u ∈ graphFixedPosUnipotent TwistTag.E6 K σ) :
    x * u * x⁻¹ ∈ graphFixedPosUnipotent TwistTag.E6 K σ := by
  have hN := graphFixedPosUnipotent_subgroupOf_normal (t := TwistTag.E6) (K := K) (σ := σ)
  have hxB : x ∈ graphFixedBorel TwistTag.E6 K σ :=
    graphFixedTorus_le_graphFixedBorel (Subgroup.mem_inf.1 hx).1
  have huB : u ∈ graphFixedBorel TwistTag.E6 K σ := graphFixedPosUnipotent_le_graphFixedBorel hu
  have h := hN.conj_mem ⟨u, huB⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨x, hxB⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem normalizer_graphFixedRootTorus_le (K : Type) [Field K] (σ : K →+* K) :
    (graphFixedRootTorus TwistTag.E6 K σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.E6 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hx' : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ :=
    Subgroup.mem_subgroupOf.1 hx
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro hn
    exact graphFixedRootTorus_conj_mem_posUnipotent K σ hx' hn
  · intro hn
    have h := graphFixedRootTorus_conj_mem_posUnipotent K σ (inv_mem hx') hn
    have e : ∀ a b : ModGL TwistTag.E6.tag K, a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := fun a b => by
      group
    rwa [e] at h

end Normalizer

section Vacuity


theorem normalizesRSubgroup_twistedE6_of_dvd_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (Cat ⟨.twistedE6 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.twistedE6 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.twistedE6 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hσ' : ∀ c, σ.toRingHom c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hdiv : p ∣ q.p ^ q.exponent - 1 := by
    rw [← PrimePower.card_def]
    exact hpq
  have hidx := not_dvd_index_graphFixedRootTorus_twistedE6 q.prime_p q.exponent_pos σ.toRingHom
    hK hσ' hp hp5 hdiv
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hfin : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hq := card_orbitField (t := TwistTag.E6) q.prime_p q.exponent_pos hK hσ'
  have hcardU : Nat.card (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom) =
      (q.p ^ q.exponent) ^ 36 := by
    rw [card_graphFixedPosUnipotent (t := TwistTag.E6) hsurj hq, ncard_posRoots_twistedE6]
  have hcardQ : Nat.card ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) = (q.p ^ q.exponent) ^ 36 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).toEquiv, hcardU]
  have hQ0 : (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQ
    have : 1 < (q.p ^ q.exponent) ^ 36 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
    omega
  have hQr : IsPGroup q.p ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    IsPGroup.of_card (n := q.exponent * 36) (by rw [hcardQ, ← pow_mul])
  obtain ⟨R, hR0, hRr, hR⟩ := exists_normalized_of_inner e hidx
    (normalizer_graphFixedRootTorus_le K σ.toRingHom) hQ0 hQr hinj hEp hin
  refine ⟨R, hR0, ?_, hR⟩
  simpa [TauCeti.LieTypeIndex.characteristic_twistedE6] using hRr

theorem seitzExcHighTwE6One : SeitzExcHighTwE6One := by
  rintro ⟨d, hv⟩ p hp _ _ _ E _ hc ⟨hin, _, ⟨hp5, q, hdq, -, hord⟩, _, hn⟩
  obtain rfl : d = .twistedE6 q := hdq
  have hq : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact absurd (normalizesRSubgroup_twistedE6_of_dvd_sub_one q hv hp hp5
    (dvd_sub_one_of_orderOf_eq_one hq hord) (IsPGroup.of_card hc) hin) hn

end Vacuity

end CFSG.LieType.SeitzGeneration.ExcHigh
