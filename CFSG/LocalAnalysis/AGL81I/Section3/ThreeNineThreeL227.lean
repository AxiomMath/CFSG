module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberTits
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open scoped MatrixGroups
open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section L227

variable {G F : Type} [Group G] [Field F] [Finite F]

theorem two_ne_zero_of_natCard_eq_twentySeven (hF : Nat.card F = 3 ^ 3) : (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  refine Ring.two_ne_zero fun h => ?_
  have h2 := (FiniteField.even_card_iff_char_two (F := F)).mp h
  rw [← Nat.card_eq_fintype_card, hF] at h2
  norm_num at h2

theorem card_psl_two_of_natCard_eq_twentySeven (hF : Nat.card F = 3 ^ 3) :
    Nat.card PSL(2, F) = 9828 := by
  have := Fintype.ofFinite F
  have h := CFSG.PSL2Table.card_PSL (two_ne_zero_of_natCard_eq_twentySeven hF)
  rw [← Nat.card_eq_fintype_card, hF] at h
  norm_num at h
  omega

theorem card_normalizer_sylow_three_psl_two_twentySeven [Finite G] (hF : Nat.card F = 3 ^ 3)
    (ψ : G ≃* PSL(2, F)) (T : Sylow 3 G) :
    Nat.card (Subgroup.normalizer ((T : Subgroup G) : Set G)) = 351 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := two_ne_zero_of_natCard_eq_twentySeven hF
  let W : Sylow 3 PSL(2, F) := T.mapSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hW : (W : Subgroup PSL(2, F)) = (T : Subgroup G).map ψ.toMonoidHom := rfl
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_conj_eq_unipotent hF W
  have hN := CFSG.GH74.GLS.IVK.L2Borel.normalizer_map_equiv ψ (T : Subgroup G)
  rw [← hW, hc, CFSG.GH74.GLS.IVK.L2Borel.normalizer_map_equiv (MulAut.conj c),
    CFSG.GH74.GLS.IVK.L2Borel.normalizer_unipotent_eq h2] at hN
  have h3 : Nat.card ((CFSG.PSL2Table.borel F).map (MulAut.conj c).toMonoidHom) =
      Nat.card ((Subgroup.normalizer ((T : Subgroup G) : Set G)).map ψ.toMonoidHom) := by
    rw [hN]
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
    Subgroup.card_map_of_injective ψ.injective] at h3
  rw [← h3]
  have := Fintype.ofFinite F
  have hB := CFSG.PSL2Table.card_borel h2
  rw [← Nat.card_eq_fintype_card, hF] at hB
  norm_num at hB
  omega

theorem invariants_of_stated_psl_two_three_three {K : Type} [Group K] [Finite K]
    (hK : StatedClassicalModel K .PSL 2 3 3) :
    Nat.card K = 9828 ∧ Subgroup.center K = ⊥ ∧ Nat.card (Outer K) ∣ 6 ∧
      ∀ T : Sylow 3 K, Nat.card (Subgroup.normalizer ((T : Subgroup K) : Set K)) = 351 := by
  have hsimple := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hK
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  let ψ : K ≃* PSL(2, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hcard : Nat.card K = 9828 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact card_psl_two_of_natCard_eq_twentySeven hF
  refine ⟨hcard, ?_, ?_, fun T => card_normalizer_sylow_three_psl_two_twentySeven hF ψ T⟩
  · refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => ?_
    have := hc
    have hp := Group.is_simple_iff_prime_card.mp hsimple
    rw [hcard] at hp
    norm_num at hp
  · have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor (p := 3) (f := 3)
      Nat.prime_three F hF).2 K ⟨ψ⟩
    rwa [show (3 : ℕ) * Nat.gcd 2 (3 ^ 3 - 1) = 6 by norm_num] at h

end L227

theorem false_of_threeNineHyp_L227 {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    {d : ℕ} (h : ThreeNineHyp K E D X₁ 3 d) (hK : StatedClassicalModel ↥K .PSL 2 3 3) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨hcardK, hZ, hOut, hNorm⟩ := invariants_of_stated_psl_two_three_three hK
  have hd2 : ¬ d ∣ 2 := fun hd =>
    h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp hd)
  have hd3 : ¬ d ∣ 3 := fun hd =>
    h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp hd)
  have hout : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    rcases (Nat.Prime.dvd_mul h.d_prime).mp (hd.trans hOut : d ∣ 2 * 3) with h1 | h1
    · exact hd2 h1
    · exact hd3 h1
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hout
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  have hDcard := hDsylK.card_eq
  rw [hcardK] at hDcard
  have hdK : d ∣ 9828 := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hDcard
    exact h.D_ne_bot (Subgroup.card_eq_one.mp hDcard)
  have hd713 : d = 7 ∨ d = 13 := by
    have hfac : (9828 : ℕ) = 2 ^ 2 * 3 ^ 3 * 7 * 13 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd (h.d_prime.dvd_of_dvd_pow h1) hd2
        · exact absurd (h.d_prime.dvd_of_dvd_pow h1) hd3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  have hDd : Nat.card D = d := by
    rw [hDcard]
    rcases hd713 with rfl | rfl
    · have h1 : (7 : ℕ) ^ (9828 : ℕ).factorization 7 = 7 ^ 1 :=
        (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 7) (a := 1)
          (k := 1404) (by norm_num) (by norm_num)).symm
      rw [h1, pow_one]
    · have h1 : (13 : ℕ) ^ (9828 : ℕ).factorization 13 = 13 ^ 1 :=
        (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 13) (a := 1)
          (k := 756) (by norm_num) (by norm_num)).symm
      rw [h1, pow_one]
  set Y : Subgroup ↥K := X₁.subgroupOf K
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := htop ▸ Subgroup.mem_top _
    exact this
  have hi1 : Y.index ≠ 1 := fun h1 => hYtop (Subgroup.index_eq_one.mp h1)
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup X) ⊓ K) K := by
    have hQ : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup X) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index
    exact hQ.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  let T : Sylow 3 ↥K := Sylow.ofCard (((Q : Subgroup X) ⊓ K).subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hQsyl.card_eq)
  have hTcard : Nat.card (T : Subgroup ↥K) = 27 := by
    have h3 : (3 : ℕ) ^ (9828 : ℕ).factorization 3 = 3 ^ 3 :=
      (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3)
        (k := 364) (by norm_num) (by norm_num)).symm
    rw [Sylow.card_eq_multiplicity, hcardK, h3]
    norm_num
  have hTY : (T : Subgroup ↥K) ≤ Y := fun x hx => h.inf_K_le Q.isPGroup' hEQ hx
  have hDY : D.subgroupOf K ≤ Y := fun x hx => h.D_le hx
  have hDKc : Nat.card (D.subgroupOf K) = d := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDd]
  let SD : Sylow d ↥K := Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard, hcardK])
  have hN : Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ Y := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
    exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
  have hmod := index_modEq_one_of_normalizer_le SD hN
  have hidx := Y.card_mul_index
  rw [hcardK] at hidx
  have h27 : 27 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hTY
    rwa [hTcard] at this
  have hdY : d ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hDY
    rwa [hDKc] at this
  rcases hd713 with rfl | rfl
  ·
    obtain ⟨q, hq⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 7) h27 hdY
    have hqi : q * Y.index = 52 := by
      have h1 : 27 * 7 * (q * Y.index) = 9828 := by rw [← hidx, hq]; ring
      omega
    have key : ∀ m ∈ Nat.divisors 52, m ≡ 1 [MOD 7] → m = 1 := by decide +kernel
    exact hi1 (key _ (Nat.mem_divisors.mpr ⟨Dvd.intro_left q hqi, by norm_num⟩) hmod)
  ·
    obtain ⟨q, hq⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 13) h27 hdY
    have hqi : q * Y.index = 28 := by
      have h1 : 27 * 13 * (q * Y.index) = 9828 := by rw [← hidx, hq]; ring
      omega
    have key : ∀ m ∈ Nat.divisors 28, m ≡ 1 [MOD 13] → m = 1 ∨ m = 14 := by decide +kernel
    rcases key _ (Nat.mem_divisors.mpr ⟨Dvd.intro_left q hqi, by norm_num⟩) hmod with h1 | h14
    · exact hi1 h1
    · have hY702 : Nat.card Y = 702 := by
        rw [h14] at hidx
        omega
      set TY : Subgroup ↥Y := (T : Subgroup ↥K).subgroupOf Y
      have hTYc : Nat.card TY = 27 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hTcard]
      have hv3 : (3 : ℕ) ^ 3 = 3 ^ (Nat.card ↥Y).factorization 3 :=
        CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3) (k := 26)
          (by rw [hY702]; norm_num) (by norm_num)
      let P' : Sylow 3 ↥Y := Sylow.ofCard TY (by rw [hTYc, ← hv3]; norm_num)
      have hcount : (Subgroup.normalizer (TY : Set ↥Y)).index ≡ 1 [MOD 3] := by
        have h := card_sylow_modEq_one (p := 3) (G := ↥Y)
        rw [Sylow.card_eq_index_normalizer P'] at h
        exact h
      have hmul := (Subgroup.normalizer (TY : Set ↥Y)).card_mul_index
      rw [hY702] at hmul
      have hTN : TY ≤ Subgroup.normalizer (TY : Set ↥Y) := Subgroup.le_normalizer
      have h27N : 27 ∣ Nat.card (Subgroup.normalizer (TY : Set ↥Y)) := by
        have := Subgroup.card_dvd_of_le hTN
        rwa [hTYc] at this
      have h351 : Nat.card (Subgroup.normalizer (TY : Set ↥Y)) ∣ 351 := by
        rw [← Subgroup.subgroupOf_normalizer_eq hTY, ← hNorm T]
        have h1 := (Nat.card_congr (Subgroup.equivMapOfInjective
          ((Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).subgroupOf Y) Y.subtype
          Y.subtype_injective).toEquiv).symm
        rw [Subgroup.subgroupOf_map_subtype] at h1
        rw [← h1]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨r, hr⟩ := h27N
      rw [hr] at h351 hmul
      have hr13 : r ∣ 13 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 27)
        (by rw [show (27 : ℕ) * 13 = 351 by norm_num]; exact h351)
      unfold Nat.ModEq at hcount
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hr13 with rfl | rfl <;> omega

end CFSG.LocalAnalysis.AGL81I.Section3
