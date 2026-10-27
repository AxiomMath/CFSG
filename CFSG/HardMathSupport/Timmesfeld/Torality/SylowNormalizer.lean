module

public import CFSG.LieType.Chevalley.LangFiniteNormalizerOddIndex

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section


theorem not_dvd_relIndex_monomial (τ : Tag) (K : Type) [Field K] [Finite K] {r : ℕ}
    [hr : Fact r.Prime] (hqr : ¬ r ∣ Nat.card K) {M : ℕ}
    (hqM : Nat.card K ≡ 1 [MOD r ^ M]) (hW : ¬ r ^ M ∣ Nat.card (WeylGroup τ)) :
    ¬ r ∣ (monomialSubgroup τ K).relIndex (adjointGroup τ K) := by
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
  have hPW : P ≡ W [MOD r ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (r ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWdef, Nat.card_eq_fintype_card]
  have hW0 : W ≠ 0 := Nat.card_pos.ne'
  set e := W.factorization r with he
  have he1 : ¬ r ^ (e + 1) ∣ W := Nat.pow_succ_factorization_not_dvd hW0 hr.out
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hW ((Nat.pow_dvd_pow r (by omega)).trans (Nat.ordProj_dvd W r))
  intro hrI
  obtain ⟨m, hm⟩ := hrI
  have hdvd : r ^ (e + 1) ∣ q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * P := by
    rw [← hrel, hm, pow_succ]
    exact mul_dvd_mul (Nat.ordProj_dvd W r) (Dvd.intro m rfl)
  have hcop : Nat.Coprime (r ^ (e + 1))
      (q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hqr)
  have hPr : r ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
  exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow r heM)).1 hPr)

theorem exists_conj_le_monomial_of_isPGroup (τ : Tag) (K : Type) [Field K] [Finite K] {r : ℕ}
    [hr : Fact r.Prime] (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup τ)) {A : Subgroup (ModGL τ K)}
    (hA : A ≤ adjointGroup τ K) (hAp : IsPGroup r A) :
    ∃ u ∈ adjointGroup τ K, ∀ x ∈ A, u * x * u⁻¹ ∈ monomialSubgroup τ K := by
  classical
  have := finite_modGL (τ := τ) (K := K)
  have hI := not_dvd_relIndex_monomial τ K hqr hqM hW
  set C := adjointGroup τ K
  set N := (monomialSubgroup τ K).subgroupOf C
  set A' : Subgroup C := A.subgroupOf C
  have hA'p : IsPGroup r A' := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := hAp ⟨(g : ModGL τ K), hg⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : A => (y : ModGL τ K)) hk
    simpa using this
  have hcardQ : ¬ r ∣ Nat.card (C ⧸ N) := hI
  obtain ⟨Q, hQ⟩ := hA'p.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ N) hcardQ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  refine ⟨(z : ModGL τ K)⁻¹, inv_mem z.2, fun x hx => ?_⟩
  have hxC : x ∈ C := hA hx
  set x' : C := ⟨x, hxC⟩
  have hx' : x' ∈ A' := hx
  have hfix := hQ ⟨x', hx'⟩
  change ((x' * z : C) : C ⧸ N) = (z : C ⧸ N) at hfix
  rw [QuotientGroup.eq] at hfix
  have h1 : (x' * z)⁻¹ * z ∈ N := hfix
  have h2 : z⁻¹ * x' * z ∈ N := by
    have := inv_mem h1
    simpa [mul_assoc] using this
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa [mul_assoc] using h3

end

end CFSG.HardMathSupport.Timmesfeld.Torality
