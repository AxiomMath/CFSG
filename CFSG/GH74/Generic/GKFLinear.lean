module

public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.S1.SymSchur

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Blueprint
  CFSG.Blueprint.Multiplier
open scoped MatrixGroups

@[expose] noncomputable def pLin (n : ℕ) (F : Type) [Field F] :
    SL(n, F) →* StatedProj (StatedSL n F) :=
  (QuotientGroup.mk' _).comp (specialLinearGroupEquivStatedSL n F).toMonoidHom

theorem pLin_apply (n : ℕ) (F : Type) [Field F] (x : SL(n, F)) :
    pLin n F x = QuotientGroup.mk (specialLinearGroupEquivStatedSL n F x) := rfl

theorem pLin_surjective (n : ℕ) (F : Type) [Field F] : Function.Surjective (pLin n F) :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

theorem pLin_ker (n : ℕ) (F : Type) [Field F] : (pLin n F).ker = center SL(n, F) := by
  ext x
  have h1 : x ∈ (pLin n F).ker ↔ specialLinearGroupEquivStatedSL n F x ∈
      (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) := by
    rw [MonoidHom.mem_ker, pLin_apply]
    exact QuotientGroup.eq_one_iff _
  rw [h1, ← map_center_eq_statedScalars]
  exact ⟨fun ⟨y, hy, hxy⟩ => ((specialLinearGroupEquivStatedSL n F).injective hxy) ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

theorem classical_psl_of_lieModel {G : Type} [Group G] {n p f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Models.LieModel G .PSL n p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSL n F)) := by
  rcases h with ⟨-, ⟨-, hc⟩ | ⟨h0, -⟩⟩
  · exact hc
  · exact absurd h0 hn

theorem prime_ne_two_of_odd_card_pow {p n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    (hodd : Odd (Nat.card F)) (hcard : Nat.card F = p ^ n) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ Nat.card F := by rw [hcard]; exact dvd_pow_self 2 (by omega)
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

open CFSG.ComponentClassification.TBLit in
theorem psl4_cover_of_griess (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K)) (F : Type) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : K ⧸ center K ≃* StatedProj (StatedSL 4 F)) :
    ∃ π : StatedSL 4 F →* K, Function.Surjective π ∧
      ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g := by
  obtain ⟨p, n, hp, hn, hcard⟩ := exists_prime_pow_card F
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card_pow hn hodd hcard
  have hm : CFSG.Models.LieModel (StatedProj (StatedSL 4 F)) .PSL 4 p n :=
    S1.lieModel_psl_four hp hn hcard (MulEquiv.refl _)
  have hcardM := S1.card_hopfMultiplier_psl_four hGA hp2 hm
  have hS₀ : Group.IsPerfect SL(4, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨α, hαs, hαc⟩ := exists_lift_of_odd_index hS₀ hK.1 (pLin 4 F) (pLin_surjective 4 F)
    (pLin_ker 4 F).le (centralQuotientMap e) (centralQuotientMap_surjective e)
    (centralQuotientMap_ker e).le (by rw [centralQuotientMap_ker e]; exact h2) 1 odd_one (by
      rw [hcardM, pLin_ker, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 4
        (by norm_num), hcard, mul_one])
  let φ := specialLinearGroupEquivStatedSL 4 F
  refine ⟨α.comp φ.symm.toMonoidHom, hαs.comp φ.symm.surjective, fun g => ?_⟩
  have h1 := congrArg (fun f => f (φ.symm g)) hαc
  simp only [MonoidHom.comp_apply, pLin_apply] at h1
  change e (QuotientGroup.mk (α (φ.symm g))) = _ at h1
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1

open CFSG.ComponentClassification.TBLit in
theorem psl2_cover_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hm : CFSG.Models.LieModel (K ⧸ center K) .PSL 2 p f) :
    center K = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (K ≃* StatedSL 2 F) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := classical_psl_of_lieModel (by norm_num) hm
  have hoddp : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := hcard ▸ hoddp
  have hmJ : CFSG.Models.LieModel (StatedProj (StatedSL 2 F)) .PSL 2 p f :=
    ⟨hm.1, Or.inl ⟨hm.1, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩⟩
  have hexc : Odd (exceptionalOrders .PSL 2 p f).1 ∧ Odd (exceptionalOrders .PSL 2 p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  have hgen : (genericOrders .PSL 2 p f) = (2, 1) := by
    have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
      obtain ⟨k, hk⟩ := hoddp
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    exact Prod.ext h1 rfl
  have hcardM : Nat.card (hopfMultiplier (StatedProj (StatedSL 2 F))) =
      2 * ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
    rw [card_hopfMultiplier_of_griess hGA hmJ, hgen]
    simp
  have hmodd : Odd ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) :=
    hexc.1.mul hexc.2
  have hdvd := card_center_dvd_hopfMultiplier hK e
  rw [hcardM] at hdvd
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (center K))
      ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hmodd)
  have hdvd2 : Nat.card (center K) ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2'
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · refine Or.inr ⟨F, inferInstance, inferInstance, hcard, ?_⟩
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have := Fintype.ofFinite F
      have h4le : 4 ≤ Nat.card F := by
        obtain ⟨-, -, -, hne2, hne3⟩ := hm.1
        have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by
          obtain ⟨-, hf, -⟩ := hm.1
          omega) p)
        have h2' : p ^ f ≠ 2 := fun h => hne2 (by rw [h])
        have h3' : p ^ f ≠ 3 := fun h => hne3 (by rw [h])
        rw [hcard]
        omega
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4le)
      exact ⟨s, hs⟩
    have hS₀ : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    obtain ⟨α, hαs, hαc⟩ := exists_lift_of_odd_index hS₀ hK.1 (pLin 2 F) (pLin_surjective 2 F)
      (pLin_ker 2 F).le (centralQuotientMap e) (centralQuotientMap_surjective e)
      (centralQuotientMap_ker e).le (by rw [centralQuotientMap_ker e]; exact h2) _ hmodd (by
        rw [hcardM, pLin_ker, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2
          (by norm_num), hcard]
        have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
          obtain ⟨k, hk⟩ := hoddp
          exact Nat.gcd_eq_left ⟨k, by omega⟩
        rw [h1])
    have hcardSL : Nat.card SL(2, F) = Nat.card (StatedProj (StatedSL 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (pLin 2 F) (pLin_surjective 2 F), pLin_ker,
        CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num), hcard]
      have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
        obtain ⟨k, hk⟩ := hoddp
        exact Nat.gcd_eq_left ⟨k, by omega⟩
      rw [h1]
    have hcardK : Nat.card K = Nat.card (StatedProj (StatedSL 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (centralQuotientMap e) (centralQuotientMap_surjective e),
        centralQuotientMap_ker e, h2']
    have hb : Function.Bijective α :=
      hαs.bijective_of_nat_card_le (by rw [hcardSL, hcardK])
    exact ⟨((MulEquiv.ofBijective α hb).symm).trans (specialLinearGroupEquivStatedSL 2 F)⟩

end CFSG.GH74.Generic
