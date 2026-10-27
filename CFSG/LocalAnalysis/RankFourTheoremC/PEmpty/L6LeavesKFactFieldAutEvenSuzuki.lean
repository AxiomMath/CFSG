module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel SuzukiModel suzukiGroup)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator
  (card_fixedSubgroup_eq_of_intertwine card_fixedSubgroup_congr congr_mem_inner_iff)

theorem suzukiModel_of_lieModel {J : Type} [Group J] {n ℓ f : ℕ}
    (h : LieModel J .twistedB2 n ℓ f) : SuzukiModel J ℓ f := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · simp [CFSG.Blueprint.classicalTags] at ht
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · exact h

theorem five_dvd_sq_two_pow_add_one (c : ℕ) : 5 ∣ (2 ^ (2 * c + 1)) ^ 2 + 1 := by
  have key : ∀ n : ℕ, (2 ^ (2 * n + 1)) ^ 2 % 5 = 4 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have e16 : (2 ^ (2 * (n + 1) + 1)) ^ 2 = 16 * (2 ^ (2 * n + 1)) ^ 2 := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add (2 : ℕ) (2 * n + 1) 2]
        ring
      rw [e16, Nat.mul_mod, ih]
  have h := key c
  generalize (2 ^ (2 * c + 1)) ^ 2 = X at h ⊢
  omega

theorem card_fixed_suzuki {J : Type} [Group J] [Finite J]
    {ℓ f f₀ p : ℕ} (hSz : SuzukiModel J ℓ f) (hp : p.Prime) (hp2 : p ≠ 2) (hf : f = p * f₀)
    (α : MulAut J) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner J) :
    Nat.card (fixedSubgroup α) = (2 ^ f₀) ^ 2 * (2 ^ f₀ - 1) * ((2 ^ f₀) ^ 2 + 1) := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hf', hcard, ⟨e⟩⟩ := hSz
  haveI : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := fun h1 =>
    hαin (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner J).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  set α' : MulAut (suzukiGroup a K) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := by rw [hα', MulEquiv.orderOf_eq]; exact hαord
  have hα'in : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hαin ((congr_mem_inner_iff e α).mp h)
  have hcard' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hf']
  obtain ⟨σ, h, b, k, _, hkfin, -, hb, hk, hconj, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hcard' p hp hp2 α' hα'ord hα'in
  have hf₀ : f₀ = 2 * b + 1 := by
    have h1 : p * f₀ = (2 * b + 1) * p := by rw [← hf, hf', hb]
    rw [mul_comm (2 * b + 1) p] at h1
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have h1 : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup α') :=
    (card_fixedSubgroup_congr e α).symm
  have h2 : Nat.card (fixedSubgroup α') =
      Nat.card (fixedSubgroup (MulAut.conj h * α' * (MulAut.conj h)⁻¹)) := by
    refine card_fixedSubgroup_eq_of_intertwine (MulAut.conj h) α' _ fun x => ?_
    have hx : (MulAut.conj h)⁻¹ (MulAut.conj h x) = x := by
      rw [MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [MulAut.mul_apply, MulAut.mul_apply, hx]
  have h3 : Nat.card (fixedSubgroup (MulAut.conj h * α' * (MulAut.conj h)⁻¹)) =
      Nat.card (suzukiGroup b k) := by
    rw [hconj]
    exact Nat.card_congr φ.toEquiv
  rw [h1, h2, h3, CFSG.LieType.Ree.suzuki_order hk, hf₀]

theorem fixedLowerBoundAt_twistedB2 :
    FixedLowerBoundAt .twistedB2 := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hSz := suzukiModel_of_lieModel hmodel
  have hℓ : ℓ = 2 := hSz.1
  have hc := card_fixed_suzuki hSz hp (by omega) hf α hαp hαin
  subst hℓ
  simp only [lieOrderNumerator, lieOrderDivisor, one_mul]
  rw [hc]
  exact dvd_of_eq (mul_right_comm _ _ _)

theorem overgroupLocalAt_twistedB2 :
    OvergroupLocalAt .twistedB2 := by
  intro K _ _ hs hab n f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf
  haveI : IsSimpleGroup K := hs
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := suzukiModel_of_lieModel hmodel
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨5, Nat.prime_five, fun T Y hT hTY hY => ?_⟩
  have hTidx : ¬ 2 ∣ T.index := by
    have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h2
  let S : Sylow 2 K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1.toSylow hTidx
  have hST : (S : Subgroup K) = T := rfl
  have hle := CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.le_normalizer_of_suzuki hSz S
    (hST ▸ hTY) hY
  have h5 : ¬ 5 ∣ Nat.card Y := fun h =>
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.not_five_dvd_normalizer hSz S
      (h.trans (Subgroup.card_dvd_of_le hle))
  obtain ⟨-, hf1, -, -, hodd, -⟩ := hadm
  have hf₀odd : Odd f₀ := (Nat.odd_mul.mp (hf ▸ hodd)).2
  obtain ⟨c, hc⟩ := hf₀odd
  have h5num : 5 ∣ lieOrderNumerator .twistedB2 n (2 ^ f₀) := by
    simp only [lieOrderNumerator]
    rw [hc]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (five_dvd_sq_two_pow_add_one c) _) _
  have hq2 : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) (by rw [hc]; omega)
  have hnum0 : lieOrderNumerator .twistedB2 n (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    have h1 : 2 ^ f₀ - 1 ≠ 0 := by omega
    positivity
  rw [padicValNat.eq_zero_of_not_dvd h5]
  simp only [lieOrderDivisor, padicValNat.one, add_zero]
  exact one_le_padicValNat_of_dvd hnum0 h5num

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
