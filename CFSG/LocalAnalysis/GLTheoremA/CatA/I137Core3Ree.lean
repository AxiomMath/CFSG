module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3ReeParab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.Open CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator.I1420
open CFSG.Blueprint (reeF4Perm reeF4Long reeFixedGroup)

namespace Core3Ree

theorem fixed_not_dvd {Q N : ℕ} (hQ : Q ∈ list93FixedOrders) (hN : N ∈ reeParabolicOrders) :
    ¬ Q ∣ N := by
  have key : ∀ Q ∈ list93FixedOrders, ∀ N ∈ reeParabolicOrders, ¬ Q ∣ N := by decide +kernel
  exact key Q hQ N hN

theorem two_pow_37_not_dvd {N : ℕ} (hN : N ∈ reeParabolicOrders) : ¬ (2 : ℕ) ^ 37 ∣ N := by
  have key : ∀ N ∈ reeParabolicOrders, ¬ (2 : ℕ) ^ 37 ∣ N := by decide +kernel
  exact key N hN

theorem l3_not_dvd {e N : ℕ} (hN : N ∈ reeParabolicOrders) (he : 3 ≤ e) (hev : Even e) :
    ¬ orderA 2 (2 ^ e) ∣ N := by
  intro hd
  have h3 : (2 : ℕ) ^ (3 * e) ∣ N := by
    have : (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 := by rw [mul_comm, pow_mul]
    rw [this]
    exact (Core3Arith.pow_three_dvd_orderA_two _).trans hd
  have he12 : e ≤ 12 := by
    by_contra h
    exact two_pow_37_not_dvd hN ((pow_dvd_pow 2 (by omega : 37 ≤ 3 * e)).trans h3)
  have key : ∀ N ∈ reeParabolicOrders, ¬ orderA 2 (2 ^ 4) ∣ N ∧ ¬ orderA 2 (2 ^ 6) ∣ N ∧
      ¬ orderA 2 (2 ^ 8) ∣ N ∧ ¬ orderA 2 (2 ^ 10) ∣ N ∧ ¬ orderA 2 (2 ^ 12) ∣ N := by
    decide +kernel
  obtain ⟨k, hk⟩ := hev
  have he' : e = 4 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by omega
  obtain ⟨k4, k6, k8, k10, k12⟩ := key N hN
  rcases he' with rfl | rfl | rfl | rfl | rfl
  exacts [k4 hd, k6 hd, k8 hd, k10 hd, k12 hd]

theorem u3_not_dvd {e N : ℕ} (hN : N ∈ reeParabolicOrders) (he : 3 ≤ e) (hodd : Odd e) :
    ¬ orderTwistedA 2 (2 ^ e) ∣ N := by
  intro hd
  have h3 : (2 : ℕ) ^ (3 * e) ∣ N := by
    have : (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 := by rw [mul_comm, pow_mul]
    rw [this]
    exact (Core3Arith.pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow).trans hd
  have he12 : e ≤ 12 := by
    by_contra h
    exact two_pow_37_not_dvd hN ((pow_dvd_pow 2 (by omega : 37 ≤ 3 * e)).trans h3)
  have key : ∀ N ∈ reeParabolicOrders, ¬ orderTwistedA 2 (2 ^ 3) ∣ N ∧
      ¬ orderTwistedA 2 (2 ^ 5) ∣ N ∧ ¬ orderTwistedA 2 (2 ^ 7) ∣ N ∧
      ¬ orderTwistedA 2 (2 ^ 9) ∣ N ∧ ¬ orderTwistedA 2 (2 ^ 11) ∣ N := by
    decide +kernel
  obtain ⟨k, hk⟩ := hodd
  have he' : e = 3 ∨ e = 5 ∨ e = 7 ∨ e = 9 ∨ e = 11 := by omega
  obtain ⟨k3, k5, k7, k9, k11⟩ := key N hN
  rcases he' with rfl | rfl | rfl | rfl | rfl
  exacts [k3 hd, k5 hd, k7 hd, k9 hd, k11 hd]

theorem nonempty_dcqEquiv {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient H ≃* ↥C) := by
  subst hHC
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

section Certified


theorem reeFilter {Q₀ : Type} [Group Q₀] [Finite Q₀] (hQ : catalogIs Q₀ (S9.isList93 3))
    {N : ℕ} (hN : N ∈ reeParabolicOrders) (hd : Nat.card Q₀ ∣ N) :
    catalogIs Q₀ S9.isL3four := by
  rcases card_list93three hQ with hfix | ⟨e, he2, hev, hcard, hcat⟩ | ⟨e, he3, hodd, hcard⟩
  · exact (fixed_not_dvd hfix hN hd).elim
  · by_cases h2 : e = 2
    · exact hcat h2
    · have h4 : 3 ≤ e := by
        obtain ⟨k, hk⟩ := hev
        omega
      exact (l3_not_dvd hN h4 hev (hcard ▸ hd)).elim
  · exact (u3_not_dvd hN he3 hodd (hcard ▸ hd)).elim

theorem exists_equiv_reeGamma {S : Type} [Group S] (hv : (LieTypeIndex.reeF4 1).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.reeF4 1, hv⟩) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 8 ∧ Nonempty (S ≃* ↥(ReeTag.F4.reeGamma K 1)) := by
  obtain ⟨-, a, hf, K, _, _, hK, ⟨e₂⟩⟩ :=
    CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 1 hv e
  obtain rfl : a = 1 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hc : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  haveI : CharP K ReeTag.F4.prime := hc
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * 1 + 1) := hK
  have hperf : ⁅ReeTag.F4.reeGamma K 1, ReeTag.F4.reeGamma K 1⁆ = ReeTag.F4.reeGamma K 1 := by
    rw [← Subgroup.map_subtype_commutator,
      (ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 1 le_rfl K hK').2.1,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hH : ReeTag.F4.reeGamma K 1 = reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ 1 else 2 ^ (1 + 1)) := ReeTag.reeGamma_eq_reeFixedGroup
  have hHC : ⁅reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ 1 else 2 ^ (1 + 1)),
      reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ 1 else 2 ^ (1 + 1))⁆ = ReeTag.F4.reeGamma K 1 := by
    rw [← hH]
    exact hperf
  obtain ⟨κ⟩ := nonempty_dcqEquiv (reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ 1 else 2 ^ (1 + 1))) (ReeTag.F4.reeGamma K 1)
    hHC (ReeTag.large_Ree_fixed_group_center_trivial 1 K hK)
  exact ⟨K, inferInstance, inferInstance, inferInstance, by rw [hK]; norm_num, ⟨e₂.trans κ⟩⟩

theorem core3Group_reeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 8) : Core3Group ↥(ReeTag.F4.reeGamma K 1) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  intro T A hT2 hT0 hA Q₀ _ ⟨f, hf⟩ hQ
  obtain ⟨P, hNP, hPcard⟩ := exists_parabolic_card hK hT2 hT0
  have : Finite Q₀ := Finite.of_surjective f hf
  exact reeFilter hQ hPcard ((card_dvd_of_surjective f hf).trans
    (Subgroup.card_dvd_of_le (hA.trans hNP)))

end Certified

end Core3Ree

section Certified


theorem core3At_reeF48 : Core3At fun d => d = .reeF4 1 := by
  intro d hd S _ _ ⟨e⟩
  obtain ⟨d, hv⟩ := d
  have hd' : d = .reeF4 1 := hd
  subst hd'
  obtain ⟨K, _, _, _, hK, ⟨eΓ⟩⟩ := Core3Ree.exists_equiv_reeGamma hv e
  exact Core3Group.of_mulEquiv eΓ (Core3Ree.core3Group_reeGamma hK)

end Certified

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
