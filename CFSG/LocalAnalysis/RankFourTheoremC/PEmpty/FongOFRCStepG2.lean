module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.RankThree.PartOne.KLC.G2
import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors)


theorem sl2_eq_one_of_central_of_pow_prime_odd {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {b : Matrix.SpecialLinearGroup (Fin 2) K}
    (hb : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, b * A = A * b) (hbp : b ^ p = 1) :
    b = 1 := by
  have hcent : b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.mem_center_iff.2 fun g => (hb g).symm
  obtain ⟨r, hr, hrb⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcent
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hscal : Matrix.scalar (Fin 2) r ^ 2 = 1 := by
    rw [← map_pow, hr2, map_one]
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, ← hrb, hscal, Matrix.SpecialLinearGroup.coe_one]
  have hcop : Nat.gcd p 2 = 1 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have h1 : b ^ Nat.gcd p 2 = 1 := pow_gcd_eq_one.2 ⟨hbp, hb2⟩
  rwa [hcop, pow_one] at h1

section


theorem card_adjointGroup_G2_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup Tag.G2 K) ∣
      Nat.card K ^ 6 * ([6, 2].map fun d => Nat.card K ^ d - 1).prod := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, CFSG.Open.ordG2]
  generalize Nat.card K = q
  have hnum : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 6 * ([6, 2].map fun d => q ^ d - 1).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [← hnum]

theorem two_le_pRank_of_orth_roots_odd {τ : Tag} {K : Type} [Field K] [Finite K]
    {β γ : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) K,
      Commute (CFSG.LieType.Chevalley.rootSL2 τ K β A) (CFSG.LieType.Chevalley.rootSL2 τ K γ B))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K ^ 2 - 1) {G : Type*} [Group G]
    [Finite G] (e : G ≃* adjointGroup τ K) : 2 ≤ CFSG.pRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [CFSG.RankThree.SubgroupLists.card_sl2_field]
    exact Dvd.dvd.mul_left hdvd _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hadj : ∀ (r : Fin τ.rank → ℤ) (A : Matrix.SpecialLinearGroup (Fin 2) K),
      CFSG.LieType.Chevalley.rootSL2 τ K r A ∈ adjointGroup τ K := fun r A =>
    (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_data τ K r).2.2.2.2.1 A
  have hinjβ := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := τ) (K := K) β
  have hinjγ := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := τ) (K := K) γ
  set u₁ : adjointGroup τ K := ⟨CFSG.LieType.Chevalley.rootSL2 τ K β a, hadj β a⟩ with hu₁
  set u₂ : adjointGroup τ K := ⟨CFSG.LieType.Chevalley.rootSL2 τ K γ a, hadj γ a⟩ with hu₂
  have hu₁p : u₁ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hu₁, ← map_pow, hap, map_one]
    rfl)
  have hu₂p : u₂ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hu₂, ← map_pow, hap, map_one]
    rfl)
  have hu₁₂ : Commute u₁ u₂ := Subtype.ext (hcomm a a).eq
  refine CFSG.RankThree.PartOne.KLC.two_le_pRank_of_two_commuting hp (e₁ := e.symm u₁)
    (e₂ := e.symm u₂) (hu₁₂.map e.symm.toMonoidHom)
    (by rw [← map_pow, hu₁p, map_one]) (by rw [← map_pow, hu₂p, map_one]) ?_
  intro i j hij
  have h1 : u₁ ^ i * u₂ ^ j = 1 := by
    apply e.symm.injective
    rw [map_mul, map_zpow, map_zpow, hij, map_one]
  have h2 : CFSG.LieType.Chevalley.rootSL2 τ K β (a ^ i) *
      CFSG.LieType.Chevalley.rootSL2 τ K γ (a ^ j) = 1 := by
    have := congrArg Subtype.val h1
    simpa [hu₁, hu₂, map_zpow] using this
  have hβγ : CFSG.LieType.Chevalley.rootSL2 τ K β (a ^ i) =
      (CFSG.LieType.Chevalley.rootSL2 τ K γ (a ^ j))⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hγβ : CFSG.LieType.Chevalley.rootSL2 τ K γ (a ^ j) =
      (CFSG.LieType.Chevalley.rootSL2 τ K β (a ^ i))⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hai : a ^ i = 1 := by
    have hbp : (a ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    refine sl2_eq_one_of_central_of_pow_prime_odd hp hp2 (fun A => hinjβ ?_) hbp
    rw [map_mul, map_mul, hβγ]
    exact ((hcomm A (a ^ j)).inv_right).symm.eq
  have haj : a ^ j = 1 := by
    have hbp : (a ^ j) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    refine sl2_eq_one_of_central_of_pow_prime_odd hp hp2 (fun B => hinjγ ?_) hbp
    rw [map_mul, map_mul, hγβ]
    exact ((hcomm (a ^ i) B).inv_left).eq
  rw [← ha]
  exact ⟨(orderOf_dvd_iff_zpow_eq_one).2 hai, (orderOf_dvd_iff_zpow_eq_one).2 haj⟩

theorem untwCrossRankStep_G2 : UntwCrossRankStep Tag.G2 := by
  refine untwCrossRankStep_of_row (D := [6, 2]) (N := 6) (by decide)
    (fun K _ _ => card_adjointGroup_G2_dvd K) ?_
  intro ℓ f₀ p hℓ hf₀ hp hp5 hne K k _ _ _ _ hK hk m hm hpm hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hcong := natCast_card_eq_of_pow (p := p) hK hk
  have hp2 : p ≠ 2 := by omega
  have hlow : ∀ e : ℕ, (e = 1 ∨ e = 2) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
        2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.G2 k)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    have hdvd : p ∣ Nat.card k ^ 2 - 1 := by
      have hcast : ((Nat.card k ^ 2 - 1 : ℕ) : ℤ) =
          ((Nat.card k : ℤ) - 1) * ((Nat.card k : ℤ) + 1) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hk1)]
        push_cast
        ring
      have hZ : (p : ℤ) ∣ ((Nat.card k ^ 2 - 1 : ℕ) : ℤ) := by
        rw [hcast]
        rcases he with rfl | rfl
        · simp only [exhaustionPhi, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_one] at h'
          exact Dvd.dvd.mul_right h' _
        · simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_X,
            Polynomial.eval_one] at h'
          exact Dvd.dvd.mul_left h' _
      exact Int.natCast_dvd_natCast.1 hZ
    have h2 := two_le_pRank_of_orth_roots_odd (τ := Tag.G2) (K := k)
      (β := CFSG.RankThree.PartOne.KLC.g2OrthBeta) (γ := CFSG.RankThree.PartOne.KLC.g2OrthGamma)
      (fun A B => CFSG.RankThree.PartOne.KLC.g2Orth_commute A B) hp hp2 hdvd
      (MulEquiv.refl (adjointGroup Tag.G2 k))
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at h2
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      exhaustionMinusFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  ·
    exfalso
    have hd3 : (p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
      have e3 : (exhaustionPhi 3).eval (Nat.card K : ℤ) =
          ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [← e3]
      exact hpm
    have hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := Int.natCast_dvd_natCast.1 hd3
    have hdd : ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + 1 * (Nat.card K : ℤ) + 1 := by
      push_cast <;> ring
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      haveI : Fintype K := Fintype.ofFinite K
      haveI : CharP K 2 :=
        charP_of_card_eq_prime_pow (f := p * f₀) (by rw [← Nat.card_eq_fintype_card]; exact hK)
      have h := CFSG.RankThree.Chevalley.even_G2_cyclotomic_three_six_tori_and_prime_centralizers
        K (1 : ℤ) (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) hdd hp (by omega) hpd
      obtain ⟨-, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
    · have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact Odd.pow (hℓ.odd_of_ne_two hℓ2)
      have h := CFSG.RankThree.Chevalley.odd_G2_cyclotomic_three_six_tori_and_prime_centralizers
        K hodd (1 : ℤ) (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) hdd hp (by omega) hpd
      obtain ⟨-, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
  ·
    exfalso
    have hN : Nat.card K ≤ Nat.card K ^ 2 + 1 :=
      (le_self_pow Nat.card_pos two_ne_zero).trans (Nat.le_add_right _ _)
    have hd6 : ((Nat.card K ^ 2 + 1 - Nat.card K : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1 := by
      rw [Nat.cast_sub hN]
      push_cast <;> ring
    have hpd : (p : ℤ) ∣ ((Nat.card K ^ 2 + 1 - Nat.card K : ℕ) : ℤ) := by
      rw [hd6]
      have e6 : (exhaustionPhi 6).eval (Nat.card K : ℤ) =
          (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1 := by
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one]
        ring
      rw [← e6]
      exact hpm
    have hpd' : p ∣ Nat.card K ^ 2 + 1 - Nat.card K := Int.natCast_dvd_natCast.1 hpd
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      haveI : Fintype K := Fintype.ofFinite K
      haveI : CharP K 2 :=
        charP_of_card_eq_prime_pow (f := p * f₀) (by rw [← Nat.card_eq_fintype_card]; exact hK)
      have h := CFSG.RankThree.Chevalley.even_G2_cyclotomic_three_six_tori_and_prime_centralizers
        K (-1 : ℤ) (Or.inl rfl) (Nat.card K ^ 2 + 1 - Nat.card K) hd6 hp (by omega) hpd'
      obtain ⟨-, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
    · have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact Odd.pow (hℓ.odd_of_ne_two hℓ2)
      have h := CFSG.RankThree.Chevalley.odd_G2_cyclotomic_three_six_tori_and_prime_centralizers
        K hodd (-1 : ℤ) (Or.inl rfl) (Nat.card K ^ 2 + 1 - Nat.card K) hd6 hp (by omega) hpd'
      obtain ⟨-, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
