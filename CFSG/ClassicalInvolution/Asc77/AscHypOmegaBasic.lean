module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Asc77.AscHypOmega

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem eq_top_of_perfect_of_odd_index {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {N : Subgroup L} [N.Normal] (hN : Odd N.index) : N = ⊤ := by
  by_contra hne
  have hodd : Odd (Nat.card (L ⧸ N)) := by rwa [← Subgroup.index_eq_card]
  have hsol : Group.IsSolvable (L ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have h1 : N.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hnt : Nontrivial (L ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card]
    have := N.index_ne_zero_of_finite
    omega
  have : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) hsol

variable {G : Type} [Group G] [Finite G]

theorem padicValNat_card_inf_le_one {F : Type*} [Field F] [Finite F] {K J : Subgroup G}
    (hKperf : Group.IsPerfect K) (hKJ : K ≤ Subgroup.normalizer (J : Set G)) (hne : K ≠ J)
    (hcard : Nat.card J ≤ Nat.card K) (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (e : (K ⧸ classicalInvolutionOddCore K) ≃* SL(2, F)) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 := by
  have := hKperf
  set O : Subgroup ↥K := classicalInvolutionOddCore ↥K with hO
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥K
  set N' : Subgroup ↥K := (K ⊓ J).subgroupOf K with hN'
  have hNcard : Nat.card N' = Nat.card ↥(K ⊓ J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hN'norm : N'.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnK, hnJ⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem k.2 hnK) (K.inv_mem k.2)
    · have := (Subgroup.mem_normalizer_iff.mp (hKJ k.2) (n : G)).mp hnJ
      simpa using this
  set π : ↥K →* ↥K ⧸ O := QuotientGroup.mk' O with hπ
  have hM : (N'.map π).Normal := hN'norm.map π (QuotientGroup.mk'_surjective O)
  rw [← hNcard]
  rcases normal_cases_of_equiv_sl2 h4 e (N'.map π) hM with h | h | h
  ·
    have hle : N' ≤ O := by
      intro n hn
      have : π n ∈ N'.map π := Subgroup.mem_map_of_mem π hn
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff n).mp this
    have hdvd : Nat.card N' ∣ Nat.card O := Subgroup.card_dvd_of_le hle
    have : ¬ 2 ∣ Nat.card N' := fun h2 => (Nat.not_even_iff_odd.mpr hOodd)
      (even_iff_two_dvd.mpr (h2.trans hdvd))
    rw [padicValNat.eq_zero_of_not_dvd this]
    exact Nat.zero_le _
  ·
    set φ : ↥N' →* ↥K ⧸ O := π.comp N'.subtype with hφ
    have hrange : φ.range = N'.map π := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Odd (Nat.card φ.ker) := by
      have hdvd : Nat.card φ.ker ∣ Nat.card O := by
        refine Subgroup.card_dvd_of_injective
          (MonoidHom.codRestrict ((N'.subtype).comp φ.ker.subtype) O ?_) ?_
        · intro x
          have hx := x.2
          rw [MonoidHom.mem_ker] at hx
          exact (QuotientGroup.eq_one_iff _).mp hx
        · intro x y hxy
          have := congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext this)
      exact Odd.of_dvd_nat hOodd hdvd
    have hrng : Nat.card φ.range ∣ 2 := by
      have hc : Nat.card (Subgroup.center (↥K ⧸ O)) = 2 :=
        natCard_center_of_equiv_sl2 hodd e
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rw [hrange, h]
    have hmul := Subgroup.card_ker_mul_card_range φ
    have hker0 : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    have hrng0 : Nat.card φ.range ≠ 0 := Nat.card_pos.ne'
    rw [← hmul, padicValNat.mul hker0 hrng0,
      padicValNat.eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hker |> fun h2 h3 =>
        h2 (even_iff_two_dvd.mpr h3)), zero_add]
    rcases (Nat.dvd_prime Nat.prime_two).mp hrng with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  ·
    exfalso
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' N').comp O.subtype : ↥O →* ↥K ⧸ N') := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' y
      have hx : π x ∈ N'.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hnx' : n⁻¹ * x ∈ O := QuotientGroup.eq.mp hnx
      refine ⟨⟨n⁻¹ * x, hnx'⟩, ?_⟩
      change (QuotientGroup.mk' N') (n⁻¹ * x) = QuotientGroup.mk' N' x
      have h1 : (QuotientGroup.mk' N') n⁻¹ = 1 := (QuotientGroup.eq_one_iff n⁻¹).mpr (N'.inv_mem hn)
      rw [map_mul, h1, one_mul]
    have hdvd : Nat.card (↥K ⧸ N') ∣ Nat.card O := Subgroup.card_dvd_of_surjective hsurj
    have hidx : Odd N'.index := by
      rw [Subgroup.index_eq_card]
      exact Odd.of_dvd_nat hOodd hdvd
    have htop : N' = ⊤ := eq_top_of_perfect_of_odd_index hidx
    have hKle : K ≤ J := fun x hx => by
      have : (⟨x, hx⟩ : ↥K) ∈ N' := by rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
    exact hne (Subgroup.eq_of_le_of_card_ge hKle hcard)

end CFSG.ClassicalInvolution.Asc77.AscHypOmega
