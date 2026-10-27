module

public import CFSG.GH74.GLS.Stage4.Statements
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.Bender.Suzuki
public import CFSG.GH74.Bender.Unitary
public import CFSG.Milestones.SE_simple_strong_embedding_models

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint

theorem sylow_comm_of_psl2Model {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.PSL2Model n) (S : Sylow 2 G) :
    IsMulCommutative (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv G e.toEquiv
  have hT : IsPGroup 2 ((S : Subgroup G).map e.toMonoidHom) := S.isPGroup'.map e.toMonoidHom
  obtain ⟨Q, hQ⟩ := hT.exists_le_sylow
  obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : e a.1 ∈ Q := hQ ⟨a.1, a.2, rfl⟩
  have hb : e b.1 ∈ Q := hQ ⟨b.1, b.2, rfl⟩
  have key : (⟨e a.1, ha⟩ : Q) * ⟨e b.1, hb⟩ = ⟨e b.1, hb⟩ * ⟨e a.1, ha⟩ := by
    apply f.symm.injective
    simp only [map_mul]
    exact mul_comm _ _
  apply Subtype.ext
  apply e.injective
  have := congrArg Subtype.val key
  simpa using this

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq := two_pow_odd_mod_three a
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem three_not_dvd_card_of_szModel
    {G : Type} [Group G] {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.SzModel n) : ¬ 3 ∣ Nat.card G := by
  have e' : G ≃* CFSG.Open.Sz n := e.trans (MulEquiv.subgroupCongr (Bender.szModel_eq_sz n))
  obtain ⟨-, a, -, K, _, _, hfa, hK, ⟨e''⟩⟩ := Bender.suzukiModel_of_mulEquiv_sz hn e'
  obtain rfl : a = n := by omega
  rw [Nat.card_congr e''.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact not_three_dvd_suzuki_order a

theorem three_dvd_mul_sq_sub_one (m : ℕ) : 3 ∣ m * (m ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    omega
  rw [h]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h0 | h1 | h2
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h0) _) _
  · exact Dvd.dvd.mul_left
      (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega : (k + 2) % 3 = 0)) _) _
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega : (k + 1) % 3 = 0)) _

theorem three_dvd_card_statedSL {F : Type} [Field F] [Finite F] :
    3 ∣ Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 F) := by
  rw [← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact three_dvd_mul_sq_sub_one _

theorem three_dvd_card_of_g2 {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs]
    (h : IsTwoCentralG2TypeG2 G Gs) : 3 ∣ Nat.card G := by
  obtain ⟨-, z, -, -, -, p, f, -, -, -, hSL⟩ := h
  obtain ⟨F, F₁, F₂, _, _, _, _, _, _, hF, o1, o2, hle, h5, e1, e2, K, hKC, hidx, A, B, hAB,
    hcomm, hAB2, ⟨eA⟩, ⟨eB⟩⟩ := hSL
  have h1 : 3 ∣ Nat.card A := by
    rw [Nat.card_congr eA.toEquiv]
    exact three_dvd_card_statedSL
  exact h1.trans ((Subgroup.card_subgroup_dvd_card A).trans (Subgroup.card_subgroup_dvd_card _))

theorem no_stronglyEmbedded
    {G : Type} [Group G] [Finite G] (hStd : Std G) {Gs : Type} [Group Gs]
    (hG2 : IsTwoCentralG2TypeG2 G Gs) :
    ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  intro M hM
  have : IsSimpleGroup G := hStd.kps.1
  have hrank : 3 ≤ CFSG.Open.twoRank G := by
    rw [← pRank_two_eq_twoRank]
    exact hStd.rank.1
  rcases CFSG.Milestones.bender_suzuki M hM with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
    exact hStd.nonab S (sylow_comm_of_psl2Model (by omega) e S)
  · exact three_not_dvd_card_of_szModel hn e (three_dvd_card_of_g2 hG2)
  · exact Bender.false_of_mulEquiv_psu3Model hn e hrank hStd.gen4

end CFSG.GH74.GLS.Stage4
