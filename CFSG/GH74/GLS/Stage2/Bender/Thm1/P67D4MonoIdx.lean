module

public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem not_dvd_of_card_mul_eq (q i : ℕ) (hq : q % 3 = 1) (hq1 : 1 < q)
    (h : (q ^ 3 - 1) * (q - 1) * 12 * i =
      q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) : ¬ 3 ∣ i := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m := ⟨a / 3, by omega⟩
  have hm : 0 < m := by omega
  have e3 : (3 * m + 1) ^ 3 - 1 = 3 * m * ((3 * m) ^ 2 + 3 * (3 * m) + 3) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e2 : (3 * m + 1) ^ 2 - 1 = 3 * m * (3 * m + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e6 : (3 * m + 1) ^ 6 - 1 =
      3 * m * ((3 * m) ^ 2 + 3 * (3 * m) + 3) * ((3 * m + 1) ^ 3 + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e8 : (3 * m + 1) ^ 8 + (3 * m + 1) ^ 4 + 1 =
      ((3 * m) ^ 2 + 3 * (3 * m) + 3) * ((3 * m) ^ 2 + 3 * m + 1) *
        ((3 * m) ^ 4 + 4 * (3 * m) ^ 3 + 5 * (3 * m) ^ 2 + 2 * (3 * m) + 1) := by
    ring
  rw [e3, e2, e6, e8, Nat.add_sub_cancel] at h
  set s := 3 * m * m + 3 * m + 1 with hs
  have hu : (3 * m) ^ 2 + 3 * (3 * m) + 3 = 3 * s := by
    rw [hs]
    ring
  rw [hu] at h
  have hpos : 0 < 3 * m * (3 * m) * (3 * s) := by positivity
  have h2 : 3 * m * (3 * m) * (3 * s) * (12 * i) =
      3 * m * (3 * m) * (3 * s) *
        ((3 * m + 1) ^ 12 * (3 * m + 2) * ((3 * m + 1) ^ 3 + 1) * (3 * s) *
          ((3 * m) ^ 2 + 3 * m + 1) *
          ((3 * m) ^ 4 + 4 * (3 * m) ^ 3 + 5 * (3 * m) ^ 2 + 2 * (3 * m) + 1)) := by
    calc 3 * m * (3 * m) * (3 * s) * (12 * i)
        = 3 * m * (3 * s) * (3 * m) * 12 * i := by ring
      _ = _ := h
      _ = _ := by ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  intro hdvd
  obtain ⟨j, rfl⟩ := hdvd
  set Y : ℕ := (3 * m + 1) ^ 12 * (3 * m + 2) * ((3 * m + 1) ^ 3 + 1) * s *
      ((3 * m) ^ 2 + 3 * m + 1) *
      ((3 * m) ^ 4 + 4 * (3 * m) ^ 3 + 5 * (3 * m) ^ 2 + 2 * (3 * m) + 1) with hY
  have h4 : 12 * j = Y := by
    have : 3 * (12 * j) = 3 * Y := by
      calc 3 * (12 * j) = 12 * (3 * j) := by ring
        _ = _ := h3
        _ = 3 * Y := by
          rw [hY]
          ring
    omega
  have h5 : Y % 3 = 1 := by
    have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [hY, hs]
    rcases hmod with h | h | h <;>
      simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, h]
  omega

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

theorem card_relWeylTwist_D4 : Nat.card (relWeylTwist TwistTag.D4) = 12 := by
  classical
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have h := sum_length_relWeylTwist_D4 1
  simp only [one_pow, Finset.sum_const, smul_eq_mul, mul_one, geomSum, Finset.card_range] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert h using 1

theorem d4_monomial_le_root {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    graphFixedMonomial TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  rw [← twistedFixedGroup_eq_graphFixedRootGroup_triality σ (ringEquiv_cube_apply_eq hK hσ)
    (Or.inr ⟨p ^ f, hodd, hσ⟩)]
  exact graphFixedMonomial_le _ _ _

theorem d4_monomial_card {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card ↥(graphFixedMonomial TwistTag.D4 K σ.toRingHom) =
      ((p ^ f) ^ 3 - 1) * (p ^ f - 1) * 12 := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  obtain ⟨-, hT, -⟩ := triality_both_orientations_exact_finite_order p f hp hf K hK 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  obtain ⟨-, -, -, ⟨e, -⟩, -⟩ := fixed_monomial_quotient TwistTag.D4 K σ.toRingHom
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((graphFixedTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedMonomial TwistTag.D4 K σ.toRingHom)),
    Nat.card_congr e.toEquiv, card_relWeylTwist_D4,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedTorus_le_graphFixedMonomial TwistTag.D4 K σ.toRingHom)).toEquiv,
    graphFixedTorus_eq_graphFixedRootTorus_D4 hσ3, hT]
  ring

theorem d4_monomial_index_not_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) :
    ¬ 3 ∣ ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
  have hle := d4_monomial_le_root hp hp2 K hK σ hσ
  obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order p f hp hf K hK 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  have h := Subgroup.card_mul_index ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    d4_monomial_card hp hf K hK σ hσ, hC] at h
  exact not_dvd_of_card_mul_eq (p ^ f) _ hq (Nat.one_lt_pow (by omega) hp.one_lt) h

theorem d4_monomial_stable (K : Type) [Field K] [Finite K] (σ : K ≃+* K) :
    ∀ n ∈ (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      fieldActor (t := TwistTag.D4) σ σ n ∈
        (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnN, hnΓ⟩ := Subgroup.mem_inf.1 hn
  rw [coe_fieldActor]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact baseChangeGL_mem_monomialSubgroup σ.toRingHom hnN
  · exact units_map_entrywiseHom_mem_twistedFixedGroup (fun c => rfl) hnΓ

end CFSG.GH74.GLS.Stage2.Bender.Thm1
