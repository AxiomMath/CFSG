module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem isExtraspecial_five_of_data {G : Type*} [Group G] (N : Subgroup G)
    (hN : Nat.card ↥N = 125) (hexp : ∀ x ∈ N, x ^ 5 = 1) {u v : G} (hu : u ∈ N) (hv : v ∈ N)
    (huv : u * v ≠ v * u) : CFSG.IsExtraspecial 5 ↥N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  let Z : Subgroup ↥N := Subgroup.center ↥N
  have hZproper : Z ≠ ⊤ := by
    intro hZtop
    have hcomm : IsMulCommutative ↥N := Subgroup.center_eq_top_iff.mp hZtop
    exact huv (congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : ↥N) (⟨v, hv⟩ : ↥N)))
  obtain ⟨k, hkpos, hkcard⟩ :=
    IsPGroup.card_center_eq_prime_pow (p := 5) (G := ↥N) (n := 3)
      (by rw [hN]; norm_num) (by norm_num)
  have hk_card : Nat.card Z = 5 ^ k := hkcard
  have hZlt : Nat.card Z < Nat.card ↥N := by
    simpa [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (H := Z) (K := ⊤) (lt_top_iff_ne_top.mpr hZproper)
  have hklt : k < 3 := by
    have h1 : Nat.card Z = (5 : ℕ) ^ k := hk_card
    have h2 : Nat.card ↥N = (5 : ℕ) ^ 3 := by rw [hN]; norm_num
    rw [h1, h2] at hZlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp hZlt
  have hZ5 : Nat.card Z = 5 := by
    rcases (by omega : k = 1 ∨ k = 2) with hk1 | hk2
    · rw [hk_card, hk1]; norm_num
    · exfalso
      have hcenter : Nat.card Z = 25 := by rw [hk_card, hk2]; norm_num
      have hidx : Z.index = 5 := by
        have h := Subgroup.card_mul_index (H := Z)
        rw [hcenter, hN] at h
        omega
      have hquot : Nat.card (↥N ⧸ Z) = 5 := by
        rw [← Subgroup.index_eq_card, hidx]
      haveI : IsCyclic (↥N ⧸ Z) := isCyclic_of_prime_card hquot
      have hcomm : IsMulCommutative ↥N :=
        isMulCommutative_of_isCyclic_quotient_center_self ↥N
      exact huv (congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : ↥N) (⟨v, hv⟩ : ↥N)))
  have hidx25 : Z.index = 25 := by
    have h := Subgroup.card_mul_index (H := Z)
    rw [hZ5, hN] at h
    omega
  have hqcard : Nat.card (↥N ⧸ Z) = 5 ^ 2 := by
    rw [← Subgroup.index_eq_card, hidx25]
    norm_num
  refine ⟨hZ5, ?_, ?_⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) hqcard
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      refine QuotientGroup.induction_on x fun g => ?_
      have hg : (g : ↥N) ^ 5 = 1 := Subtype.ext (hexp (g : G) g.2)
      rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  · exact QuotientGroup.nontrivial_iff.mpr hZproper

theorem isShapeCentralizerFiveA_of_data {G : Type} [Group G] [Finite G] (X N S : Subgroup G)
    (hNX : N ≤ X) (hSX : S ≤ X) (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hX : Nat.card ↥X = Nat.card ↥N * Nat.card ↥S) (hN : Nat.card ↥N = 125)
    (hS : Nat.card ↥S = 16) (hexp : ∀ x ∈ N, x ^ 5 = 1) {u v : G} (hu : u ∈ N) (hv : v ∈ N)
    (huv : u * v ≠ v * u)
    (hSiso : Nonempty (↥S ≃* Multiplicative (ZMod 2) × QuaternionGroup 2)) :
    IsShapeCentralizerFiveA ↥X := by
  let N' : Subgroup ↥X := N.subgroupOf X
  let S' : Subgroup ↥X := S.subgroupOf X
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hS'card : Nat.card ↥S' = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have hN'norm : N'.Normal :=
    ⟨fun n hn x => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm x.1 x.2 n.1 hn⟩
  have hN'125 : Nat.card ↥N' = 125 := by rw [hN'card, hN]
  have hN'cube : Nat.card N' = 5 ^ 3 := by
    show Nat.card ↥N' = 5 ^ 3
    rw [hN'125]; norm_num
  have hN'exp : ∀ x : N', x ^ 5 = 1 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hexp x.1.1 (Subgroup.mem_subgroupOf.mp x.2)
  have hExtN : CFSG.IsExtraspecial 5 ↥N :=
    isExtraspecial_five_of_data N hN hexp hu hv huv
  have hExt : CFSG.IsExtraspecial 5 ↥N' :=
    isExtraspecial_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNX).symm hExtN
  have hS'iso : Nonempty (S' ≃* Multiplicative (ZMod 2) × QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hSX).trans hSiso.some⟩
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX, hN, hS]; norm_num)
  have hdisj : Disjoint N' S' := Subgroup.disjoint_of_coprime_natCard (by
    rw [hN'card, hS'card, hN, hS]; norm_num)
  have hcardmul : Nat.card ↥N' * Nat.card ↥S' = Nat.card ↥X := by
    rw [hN'card, hS'card, hX]
  have hcompl : N'.IsComplement' S' :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul hdisj
  exact ⟨N', S', hN'norm, hExt, hN'cube, hN'exp, hS'iso, hcompl⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
