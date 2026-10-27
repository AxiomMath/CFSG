module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONLift
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONRank3
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONRank
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCTwoLocal
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem isElemAbelian_of_le_three {G : Type*} [Group G] {A B : Subgroup G}
    (hB : IsElemAbelian 3 B) (hAB : A ≤ B) : IsElemAbelian 3 A :=
  CFSG.Open.IsElemAbelian.mono hB hAB

theorem exists_elemAbelian_card_27 {Y : Type} [Group Y] [Finite Y]
    (h : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup Y)
  have hEp : IsPGroup 3 E := IsPGroup.of_card hcard
  have hle : 3 ^ 3 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨H', hH'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hEp hle
  refine ⟨H'.map E.subtype, isElemAbelian_of_le_three hE ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hH']


theorem tables112Types_TON_twoLocal_holds :
    ∀ (K : Type) [Group K] [Finite K], IsHatON K → 3 ≤ GLATwoLocalRank 3 K := by
  rintro K _ _ hK
  obtain ⟨hperf, hZ, ⟨e⟩⟩ := hK
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective
  have hker : π.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have h4 := sporadicThreeRankGe_ONan (K ⧸ Subgroup.center K) ⟨e⟩
  obtain ⟨E₀, hE₀, hE₀card⟩ := exists_elemAbelian_card_27 (by omega)
  obtain ⟨T', hT', hT'2, hT'N⟩ := input20_29_holds (K ⧸ Subgroup.center K) ⟨e⟩ E₀ hE₀ hE₀card
  obtain ⟨T, hT, hT2, hTN⟩ := exists_two_group_lift π hπ hker hZ hT' hT'2 hT'N
  set Ê : Subgroup K := E₀.comap π with hÊ
  have hcardK : Nat.card K = 3 * Nat.card (K ⧸ Subgroup.center K) := by
    have := Subgroup.card_ker_mul_card_of_surjective hπ
    rw [hker, hZ] at this
    exact this.symm
  have hÊcard : Nat.card Ê = 81 := by
    have h1 := Subgroup.card_mul_index Ê
    have h2 := Subgroup.card_mul_index E₀
    have h3 : Ê.index = E₀.index := Subgroup.index_comap_of_surjective E₀ hπ
    rw [h3, hcardK] at h1
    have hi : E₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    rw [hE₀card] at h2
    rw [h1]
    omega
  have hÊ3 : IsPGroup 3 Ê := IsPGroup.of_card (n := 4) (by rw [hÊcard]; norm_num)
  obtain ⟨P, hÊP⟩ := hÊ3.exists_le_sylow
  obtain ⟨-, hexp, hcP, -⟩ := inputONSylow_holds K ⟨hperf, hZ, ⟨e⟩⟩ P
  have hZle : Subgroup.center K ≤ Ê := by
    intro z hz
    show π z ∈ E₀
    have : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
    rw [this]
    exact E₀.one_mem
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ê) := by
    refine three_le_pRank_of_class_two ((Subgroup.center K).subgroupOf Ê) ?_ ?_ ?_ ?_ ?_
    · intro z hz g
      have hz' : (z : K) ∈ Subgroup.center K := hz
      exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (g : K))
    · rw [← hZ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
    · exact hÊcard
    · intro g
      exact Subtype.ext (hexp g (hÊP g.2))
    · intro g h
      exact hcP g (hÊP g.2) h (hÊP h.2)
  have hrank' : 3 ≤ CFSG.Open.pRank 3 Ê := by
    have := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) Ê.subtype Ê.subtype_injective
      (⊤ : Subgroup ↥Ê)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact hrank.trans this
  have hbdd : BddAbove {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) H
    have h1 : CFSG.Open.pRank 3 H < 3 ^ CFSG.Open.pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : 3 ^ CFSG.Open.pRank 3 H ≤ Nat.card K := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank 3 H ≤ Nat.card K
    omega
  calc 3 ≤ CFSG.Open.pRank 3 Ê := hrank'
    _ ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (T : Set K)) :=
        CFSG.SectionRank.pRank_mono (by norm_num) hTN
    _ ≤ GLATwoLocalRank 3 K := le_csSup hbdd ⟨_, ⟨T, hT, hT2, rfl⟩, rfl⟩

theorem tables112Types_TON_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsHatON K →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) ∧ 3 ≤ GLATwoLocalRank 3 K := by
  intro K _ _ _ _ h
  exact ⟨tables112Types_TON_rank_holds K h, tables112Types_TON_twoLocal_holds K h⟩

end CFSG.HardMathSupport.Solomon.Coordinator
