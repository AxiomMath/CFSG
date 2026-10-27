module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsOrder
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossL3

public section

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem card_projectiveSL_three {F : Type} [Field F] [Finite F] :
    Nat.card (projectiveSL 3 F) = psl3Order (Nat.card F) := by
  have hSL := card_specialLinear_three (F := F)
  have hPS : Nat.card SL(3, F) = Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    (scalars 3 F).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)
  unfold psl3Order
  rw [← hSL, hPS, hZ, Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by norm_num))]

theorem card_sl_two_of_card_three {F : Type} [Field F] [Finite F] (h : Nat.card F = 3) :
    Nat.card SL(2, F) = 24 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact h
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  norm_num

theorem card_projectiveSL_three_of_card_three {F : Type} [Field F] [Finite F] (h : Nat.card F = 3) :
    Nat.card (projectiveSL 3 F) = 5616 := by
  rw [card_projectiveSL_three, h]
  norm_num [psl3Order]

theorem isSimpleGroup_projectiveSL_three (F : Type) [Field F] : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega) (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

theorem prime_eq_thirteen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : ¬ p ∣ 3) (h : p ∣ 5616) : p = 13 := by
  have h5616 : (5616 : ℕ) = 2 * 2 * 2 * 2 * 3 * 3 * 3 * 13 := by norm_num
  rw [h5616] at h
  repeat rw [hp.dvd_mul] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  all_goals first
    | exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    | exact absurd h hp3
    | exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h

theorem factorization_5616_thirteen : Nat.factorization 5616 13 = 1 := by
  have h : (5616 : ℕ) = 13 * 432 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  have h13 : Nat.factorization 13 13 = 1 := by
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 13)]
  have h432 : Nat.factorization 432 13 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h13, h432]

theorem fl3_cross_three {A : Type} [Group A] [Finite A] {K : Subgroup A} {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) (e : ↥K ≃* projectiveSL 3 F) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpF : ¬ p ∣ Nat.card F) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K)
    (hJ : ∀ j : ↥K, e j * tInv = tInv * e j → (j : A) ∈ normalizer (X : Set A)) : False := by
  classical
  have hKcard : Nat.card K = 5616 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_projectiveSL_three_of_card_three hF3
  have hXdvd : Nat.card X ∣ 5616 := hKcard ▸ Subgroup.card_dvd_of_le hXK
  have hpX : p ∣ Nat.card X := by
    rcases hX.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hX1
    · exact h
  have hp13 : p = 13 := by
    refine prime_eq_thirteen (Fact.out) hp2 ?_ (hpX.trans hXdvd)
    rwa [hF3] at hpF
  subst hp13
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hXcard : Nat.card X = 13 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · exact absurd (Subgroup.card_eq_one.1 (by simpa using hn)) hX1
      · simpa using hn
    · exfalso
      have h169 : 13 ^ 2 ∣ Nat.card X := hn ▸ pow_dvd_pow 13 h
      have := h169.trans hXdvd
      norm_num at this
  set X' : Subgroup K := X.subgroupOf K with hX'
  have hX'card : Nat.card X' = 13 := by
    rw [← hXcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  let P : Sylow 13 K := Sylow.ofCard X' (by rw [hX'card, hKcard, factorization_5616_thirteen]; rfl)
  have hP : (P : Subgroup K) = X' := rfl
  have hPc : Nat.card (P : Subgroup K) = 13 := hX'card
  let ι0 : SL(2, F) →* K := (e.symm : projectiveSL 3 F →* K).comp blockEmb
  have hι0 : Function.Injective ι0 := e.symm.injective.comp blockEmb_injective
  have hS : (ι0.range : Subgroup K) ≤ normalizer ((P : Subgroup K) : Set K) := by
    rintro _ ⟨g, rfl⟩
    have hc : e (ι0 g) * tInv = tInv * e (ι0 g) := by
      have := blockSub_le_centralizer (blockEmb_mem g)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      simpa [ι0] using this
    have hn := hJ (ι0 g) hc
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro h
    rw [hP, hX', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hn h
  have hSc : Nat.card ι0.range = 24 := by
    rw [← card_sl_two_of_card_three hF3]
    exact (Nat.card_congr (MonoidHom.ofInjective hι0).toEquiv).symm
  have h24 : 24 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) := by
    have := Subgroup.card_dvd_of_le hS
    rwa [hSc] at this
  have h13 : 13 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup K)))
    rwa [hPc] at this
  have h312 : 312 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) :=
    (show Nat.Coprime 24 13 by norm_num).mul_dvd_of_dvd_of_dvd h24 h13
  obtain ⟨m, hm⟩ := h312
  have hidx := Subgroup.index_mul_card (normalizer ((P : Subgroup K) : Set K))
  rw [hm, hKcard] at hidx
  have hidx18 : (normalizer ((P : Subgroup K) : Set K)).index * m = 18 := by nlinarith
  have hmod := card_sylow_modEq_one 13 K
  rw [P.card_eq_index_normalizer] at hmod
  have hone : (normalizer ((P : Subgroup K) : Set K)).index = 1 := by
    have h18 : (normalizer ((P : Subgroup K) : Set K)).index ∣ 18 := ⟨m, hidx18.symm⟩
    have hle : (normalizer ((P : Subgroup K) : Set K)).index ≤ 18 := Nat.le_of_dvd (by norm_num) h18
    unfold Nat.ModEq at hmod
    interval_cases hi : (normalizer ((P : Subgroup K) : Set K)).index <;>
      first | rfl | omega
  have htop : normalizer ((P : Subgroup K) : Set K) = ⊤ := Subgroup.index_eq_one.1 hone
  have hnorm : (P : Subgroup K).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have := isSimpleGroup_projectiveSL_three F
  have : IsSimpleGroup K := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup K) with h | h
  · rw [h, Subgroup.card_bot] at hPc
    omega
  · rw [h, Subgroup.card_top, hKcard] at hPc
    omega

theorem fl3_inner_cross_false {A : Type} [Group A] [Finite A] {K : Subgroup A} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) (e : ↥K ≃* projectiveSL 3 F) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hXK : X ≤ K) (hJ : ∀ j : ↥K, e j * tInv = tInv * e j → (j : A) ∈ normalizer (X : Set A))
    (hcomm : ⁅X, zpowers ((e.symm tInv : ↥K) : A)⁆ = X) : False := by
  by_cases h5 : 5 ≤ Nat.card F
  · let ι : SL2 F →* A := K.subtype.comp ((e.symm : projectiveSL 3 F →* K).comp blockEmb)
    have hnorm : ∀ g, ι g ∈ normalizer (X : Set A) := by
      intro g
      refine hJ (e.symm (blockEmb g)) ?_
      have := blockSub_le_centralizer (blockEmb_mem g)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      simpa using this
    have hι : ι (-1) = ((e.symm tInv : ↥K) : A) := by simp [ι, blockEmb_neg_one]
    have hcomm' : ⁅X, zpowers (ι (-1))⁆ = X := by rw [hι]; exact hcomm
    have hK : Nat.card K = psl3Order (Nat.card F) := by
      rw [Nat.card_congr e.toEquiv]
      exact card_projectiveSL_three
    exact false_of_sl2_psl3 hp2 hodd h5 hpF ι hXK hX hX1 hnorm hcomm' hK
  · have h3' : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact fl3_cross_three h3' e hp2 hpF hX hX1 hXK hJ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
