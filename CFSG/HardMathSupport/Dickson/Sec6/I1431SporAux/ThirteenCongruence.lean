module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.HeisCount
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ConjActionLemmas
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.OrbitCongruence
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Planes

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Dickson.I271.M13

section Fixed

variable {G : Type*} [Group G]

theorem exists_pow_pow_eq_thirteen {y : G} (hy : orderOf y = 13) {j : ℕ} (hj : j % 13 ≠ 0) :
    ∃ m : ℕ, (y ^ j) ^ m = y := by
  have hcop : Nat.Coprime j 13 := by
    have h13 : ¬ 13 ∣ j := fun h => hj (Nat.mod_eq_zero_of_dvd h)
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).2 h13).symm
  exact exists_pow_eq_self_of_coprime (by rw [hy]; exact hcop)

theorem commute_of_commute_pow_thirteen {y t : G} (hy : orderOf y = 13) {j : ℕ} (hj : j % 13 ≠ 0)
    (h : t * y ^ j = y ^ j * t) : t * y = y * t := by
  obtain ⟨m, hm⟩ := exists_pow_pow_eq_thirteen hy hj
  have hc : Commute t (y ^ j) := h
  have := (hc.pow_right m).eq
  rwa [hm] at this

theorem ncard_commute_conj (D : Set G) (hD : ∀ w t : G, t ∈ D → w * t * w⁻¹ ∈ D) (w s : G) :
    {t | t ∈ D ∧ (w * s * w⁻¹) * t = t * (w * s * w⁻¹)}.ncard =
      {t | t ∈ D ∧ s * t = t * s}.ncard := by
  have hset : {t | t ∈ D ∧ (w * s * w⁻¹) * t = t * (w * s * w⁻¹)} =
      (fun t => w * t * w⁻¹) '' {t | t ∈ D ∧ s * t = t * s} := by
    ext t
    constructor
    · rintro ⟨htD, htc⟩
      refine ⟨w⁻¹ * t * w, ⟨?_, ?_⟩, by group⟩
      · simpa using hD w⁻¹ t htD
      · have : s * (w⁻¹ * t * w) = (w⁻¹ * t * w) * s := by
          calc s * (w⁻¹ * t * w) = w⁻¹ * ((w * s * w⁻¹) * t) * w := by group
            _ = w⁻¹ * (t * (w * s * w⁻¹)) * w := by rw [htc]
            _ = (w⁻¹ * t * w) * s := by group
        exact this
    · rintro ⟨t', ⟨ht'D, ht'c⟩, rfl⟩
      refine ⟨hD w t' ht'D, ?_⟩
      calc (w * s * w⁻¹) * (w * t' * w⁻¹) = w * (s * t') * w⁻¹ := by group
        _ = w * (t' * s) * w⁻¹ := by rw [ht'c]
        _ = (w * t' * w⁻¹) * (w * s * w⁻¹) := by group
  rw [hset, Set.ncard_image_of_injective]
  intro a b hab
  have := hab
  simpa using this

end Fixed

section Congruence

variable {G : Type*} [Group G] [Finite G] {g d c x : G}

theorem congruence_of_heis (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1)
    (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hx : orderOf x = 13)
    (hlines : ∀ e ∈ censusLines, ∃ W : G,
      W * (g ^ e.a * d ^ e.b) * W⁻¹ = (if e.toC then c else x) ^ e.lam)
    {D : Set G} (hD : ∀ w t : G, t ∈ D → w * t * w⁻¹ ∈ D)
    (hDstab : ∀ t ∈ D, ¬ 13 ^ 2 ∣ Nat.card (centralizer ({t} : Set G)))
    (hFc : ∀ t ∈ D, t * c ≠ c * t) :
    ∃ K : ℕ, 12 * D.ncard = 1248 * {t | t ∈ D ∧ t * x = x * t}.ncard + 13 ^ 3 * K := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  obtain ⟨S, hgS, hdS, hcS, hScard, hSform, -⟩ := heis_sylow hg13 hd13 hc13 hc1 hcg hcd hdg
  haveI : Fintype S := Fintype.ofFinite S
  have hSp : IsPGroup 13 S := IsPGroup.of_card hScard
  letI : MulAction S D := conjSMulOn S D (fun g _ s hs => hD g s hs)
  have hsmul : ∀ (g : S) (s : D), ((g • s : D) : G) = g * s * g⁻¹ := fun g s => rfl
  have hstab : ∀ ω : D, Nat.card (MulAction.stabilizer S ω) ≤ 13 := by
    intro ω
    rw [card_stabilizer_eq hsmul ω]
    exact card_inf_centralizer_le (by norm_num) hSp (hDstab ω.1 ω.2)
  have hP : Fintype.card S = 13 ^ 3 := by rw [← Nat.card_eq_fintype_card]; exact hScard
  obtain ⟨K, hK⟩ := exists_mul_eq_sum_card_fixedBy (Ω := D) (by norm_num) hP hstab
  refine ⟨K, ?_⟩
  let f : G → ℕ := fun s => {t | t ∈ D ∧ s * t = t * s}.ncard
  have hsum : ∑ s : S, Nat.card (MulAction.fixedBy D s) = ∑ s : S, f s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    exact card_fixedBy_eq_ncard hsmul s
  have hf : ∀ w s : G, f (w * s * w⁻¹) = f s := fun w s => ncard_commute_conj D hD w s
  have hfc : ∀ j : ℕ, j % 13 ≠ 0 → f (c ^ j) = 0 := by
    intro j hj
    show {t | t ∈ D ∧ c ^ j * t = t * c ^ j}.ncard = 0
    have : {t | t ∈ D ∧ c ^ j * t = t * c ^ j} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro htD hct
      exact hFc t htD (commute_of_commute_pow_thirteen hco hj hct.symm)
    rw [this, Set.ncard_empty]
  have hfx : ∀ j : ℕ, j % 13 ≠ 0 → f (x ^ j) = {t | t ∈ D ∧ t * x = x * t}.ncard := by
    intro j hj
    show {t | t ∈ D ∧ x ^ j * t = t * x ^ j}.ncard = _
    congr 1
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨htD, hct⟩
      exact ⟨htD, commute_of_commute_pow_thirteen hx hj hct.symm⟩
    · rintro ⟨htD, hct⟩
      exact ⟨htD, (((show Commute t x from hct).pow_right j).eq).symm⟩
  have hsyl := sum_over_sylow (f := f) hg13 hd13 hc13 hc1 hcg hcd hdg hlines hgS hdS hcS hScard
    hSform hf hfc hfx
  have hf1 : f 1 = D.ncard := by
    show {t | t ∈ D ∧ 1 * t = t * 1}.ncard = D.ncard
    congr 1
    ext t
    simp
  rw [Nat.card_coe_set_eq] at hK
  rw [hsum, hsyl, hf1] at hK
  omega

end Congruence

end CFSG.HardMathSupport.Dickson.Sec6.I1431
