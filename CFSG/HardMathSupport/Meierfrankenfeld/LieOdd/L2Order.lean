module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG CFSG.GorensteinWalter CFSG.Quasithin CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family
  CFSG.LocalAnalysis.ComponentInitial

theorem card_pGammaL2 {K : Type} [Field K] [Finite K] {p e : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ e) :
    Nat.card (PGammaL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) * e := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, pgl2_card_formula,
    (card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK).1]

theorem center_eq_bot_of_equiv_psl2 {K : Type} [Field K] [Finite K] {S : Type} [Group S]
    (θ : S ≃* PSL2 K) : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : θ z ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    have := congrArg θ (hz (θ.symm w))
    simpa using this
  rw [psl2_center_eq_bot K, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg θ.symm h1

theorem card_sup_le_of_psl2 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hq : 3 < p ^ e) {L E : Subgroup (MulAut W)}
    (hirr : X1.IsIrrOn L) (θ : ↥L ≃* PSL2 K)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E) :
    Nat.card ↥(L ⊔ E) ≤ p ^ e * (p ^ (2 * e) - 1) * e := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h] at hq; simp at hq
    · exact h
  have hoddpp : IsOddPrimePower (Nat.card K) := ⟨p, e, Fact.out, hodd, he1, hK⟩
  have hcard3 : 3 < Nat.card K := hK ▸ hq
  have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv_psl2 θ
  have hHn : L ⊔ E ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hE
  have hNnormal : (L.subgroupOf (L ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (L.subgroupOf (L ⊔ E)) ≃* PSL2 K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ E)).trans θ
  have hC := centralizer_trivial hW hirr.2 hcenter hE hEel
  have hCbot : Subgroup.centralizer
      ((L.subgroupOf (L ⊔ E) : Subgroup ↥(L ⊔ E)) : Set ↥(L ⊔ E)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hC z
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 hz n hn).symm
  have hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hoddpp hcard3) :=
    pGammaL2ToMulAutPSL2_surjective K hK hoddpp hcard3
  have hj : Function.Injective
      (normalPSL2ToPGammaL2 (L.subgroupOf (L ⊔ E)) K hoddpp hcard3 θ' hsurj) :=
    normalPSL2ToPGammaL2_injective _ K hoddpp hcard3 θ' hCbot hsurj
  have hfin : Finite (PGammaL2 K) := by
    have : 0 < Nat.card (PGammaL2 K) := by
      rw [card_pGammaL2 hK]
      exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by nlinarith))) he1
    exact Nat.finite_of_card_ne_zero this.ne'
  calc Nat.card ↥(L ⊔ E) ≤ Nat.card (PGammaL2 K) := Nat.card_le_card_of_injective _ hj
    _ = Nat.card K * (Nat.card K ^ 2 - 1) * e := card_pGammaL2 hK
    _ = p ^ e * (p ^ (2 * e) - 1) * e := by
      rw [hK, pow_mul', ← pow_mul]

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
