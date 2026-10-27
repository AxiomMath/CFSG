module

public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem card_monomialSubgroup
    (τ : Tag) (K : Type) [Field K] :
    Nat.card (monomialSubgroup τ K) = Nat.card (torusGroup τ K) * Nat.card (WeylGroup τ) := by
  obtain ⟨-, ⟨ρ, hρs, -, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ K
  have hle : torusGroup τ K ≤ monomialSubgroup τ K := le_sup_left
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, mul_comm]

theorem exceptional_Lang_finite_normalizer_odd_index_involutions
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hq : Odd (Nat.card K)) {M : ℕ} (_hM : 1 ≤ M)
    (hqM : Nat.card K ≡ 1 [MOD 2 ^ M]) (hW : ¬ 2 ^ M ∣ Nat.card (WeylGroup τ)) :
    Odd ((monomialSubgroup τ K).relIndex (adjointGroup τ K)) ∧
    ∀ x ∈ adjointGroup τ K, x ^ 2 = 1 →
      ∃ u ∈ adjointGroup τ K, u * x * u⁻¹ ∈ monomialSubgroup τ K := by
  classical
  have := finite_modGL (τ := τ) (K := K)
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  set q := Nat.card K with hqdef
  set W := Nat.card (WeylGroup τ) with hWdef
  set P := ∑ᶠ w : WeylGroup τ, q ^ (coxeterSystem τ).length w with hP
  set I := (monomialSubgroup τ K).relIndex (adjointGroup τ K) with hI
  have hNC : monomialSubgroup τ K ≤ adjointGroup τ K := monomialSubgroup_le_adjointGroup'
  have hH : 0 < Nat.card (torusGroup τ K) := Nat.card_pos
  have hIdef : I = ((monomialSubgroup τ K).subgroupOf (adjointGroup τ K)).index := rfl
  have hrel : W * I = q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * P := by
    have h1 := Subgroup.card_mul_index ((monomialSubgroup τ K).subgroupOf (adjointGroup τ K))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, card_monomialSubgroup,
      card_adjointGroup, ← hIdef] at h1
    apply Nat.eq_of_mul_eq_mul_left hH
    rw [← mul_assoc, h1, mul_assoc]
  have hPW : P ≡ W [MOD 2 ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (2 ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWdef, Nat.card_eq_fintype_card]
  have hW0 : W ≠ 0 := Nat.card_pos.ne'
  set e := W.factorization 2 with he
  have he1 : ¬ 2 ^ (e + 1) ∣ W := Nat.pow_succ_factorization_not_dvd hW0 Nat.prime_two
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hW ((Nat.pow_dvd_pow 2 (by omega)).trans (Nat.ordProj_dvd W 2))
  have hIodd : Odd I := by
    by_contra hIe
    rw [Nat.not_odd_iff_even] at hIe
    obtain ⟨m, hm⟩ := hIe
    have hdvd : 2 ^ (e + 1) ∣ q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * P := by
      rw [← hrel, hm, pow_succ]
      exact mul_dvd_mul (Nat.ordProj_dvd W 2) (Dvd.intro m (by ring))
    have hcop : Nat.Coprime (2 ^ (e + 1))
        (q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) :=
      Nat.Coprime.pow _ _ (Nat.coprime_two_left.2 hq)
    have hP2 : 2 ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
    exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow 2 heM)).1 hP2)
  refine ⟨hIodd, fun x hx hx2 => ?_⟩
  set C := adjointGroup τ K
  set N := (monomialSubgroup τ K).subgroupOf C
  set x' : C := ⟨x, hx⟩
  have hx'2 : x' ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hpg : IsPGroup 2 (Subgroup.zpowers x') := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (x' ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'2, one_zpow]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : ¬ 2 ∣ Nat.card (C ⧸ N) := by
    have hQI : Nat.card (C ⧸ N) = I := rfl
    rw [hQI]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hIodd)
  obtain ⟨Q, hQ⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ N) hcardQ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  have hfix := hQ ⟨x', Subgroup.mem_zpowers x'⟩
  change ((x' * z : C) : C ⧸ N) = (z : C ⧸ N) at hfix
  rw [QuotientGroup.eq] at hfix
  refine ⟨(z : ModGL τ K)⁻¹, inv_mem z.2, ?_⟩
  have h1 : (x' * z)⁻¹ * z ∈ N := hfix
  have h2 : z⁻¹ * x' * z ∈ N := by
    have := inv_mem h1
    simpa [mul_assoc] using this
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa [mul_assoc] using h3

end CFSG.LieType.Chevalley
