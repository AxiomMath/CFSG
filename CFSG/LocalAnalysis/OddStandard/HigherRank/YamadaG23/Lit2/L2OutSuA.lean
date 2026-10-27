module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem l2out_two_elt_oddCore {H : Type} [Group H] [Finite H] {g : H}
    (hg : g ∈ CFSG.oddCore H) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card (CFSG.oddCore H) :=
    Subgroup.orderOf_dvd_natCard (CFSG.oddCore H) hg
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore H)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (lit_odd_card_oddCore H))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem l2out_oddCore_le_center {H : Type} [Group H] [Finite H] (hq : CFSG.IsQuasisimple H)
    {z : H} (hz1 : z ≠ 1) {k : ℕ} (hk : z ^ 2 ^ k = 1) : CFSG.oddCore H ≤ center H := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (N := CFSG.oddCore H) inferInstance with
    h | h
  · exfalso
    apply hz1
    have hzO : z ∈ CFSG.oddCore H := by rw [h]; exact Subgroup.mem_top z
    exact l2out_two_elt_oddCore hzO hk
  · exact h

theorem l2out_quot_data {H : Type} [Group H] [Finite H] (hq : CFSG.IsQuasisimple H)
    (hO : CFSG.oddCore H ≤ center H) :
    CFSG.IsQuasisimple (H ⧸ CFSG.oddCore H) ∧
      Nonempty ((H ⧸ CFSG.oddCore H) ⧸ center (H ⧸ CFSG.oddCore H) ≃* H ⧸ center H) := by
  obtain ⟨hBq, -, hBc⟩ :=
    CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.oddCore H) hO
  exact ⟨hBq, ⟨(QuotientGroup.quotientMulEquivOfEq hBc).trans
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.oddCore H) (center H) hO)⟩⟩

theorem l2out_three_central {H : Type} [Group H] [Finite H] (τ : H ≃* H) {z : H}
    (hz : z ∈ center H) {k : ℕ} (hk : z ^ 2 ^ k = 1) (hτ : τ z ≠ z) :
    3 ≤ Nat.card ↥(center (H ⧸ CFSG.oddCore H)) := by
  classical
  let O := CFSG.oddCore H
  let bar : H →* H ⧸ O := QuotientGroup.mk' O
  have hz1 : z ≠ 1 := by
    intro h
    exact hτ (by rw [h, map_one])
  have hτz1 : τ z ≠ 1 := by
    intro h
    exact hz1 (τ.injective (by rw [h, map_one]))
  have hzτ : τ z ∈ center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := τ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  have hbz : bar z ∈ center (H ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  have hbτz : bar (τ z) ∈ center (H ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzτ x]
  have hτk : (τ z) ^ 2 ^ k = 1 := by
    rw [(map_pow τ z (2 ^ k)).symm, hk, map_one]
  have hbz_ne_one : bar z ≠ 1 := by
    intro h
    have hzO : z ∈ O := (QuotientGroup.eq_one_iff z).mp (by simpa [bar] using h)
    exact hz1 (l2out_two_elt_oddCore hzO hk)
  have hbτz_ne_one : bar (τ z) ≠ 1 := by
    intro h
    have hτzO : τ z ∈ O := (QuotientGroup.eq_one_iff (τ z)).mp (by simpa [bar] using h)
    exact hτz1 (l2out_two_elt_oddCore hτzO hτk)
  have hb_ne : bar z ≠ bar (τ z) := by
    intro h
    have hmem : z⁻¹ * τ z ∈ O := by
      have h1 : bar (z⁻¹ * τ z) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (z⁻¹ * τ z)).mp (by simpa [bar] using h1)
    have hcomm : Commute z⁻¹ (τ z) :=
      Commute.inv_left (Subgroup.mem_center_iff.mp hz (τ z)).symm
    have hpow : (z⁻¹ * τ z) ^ 2 ^ k = 1 := by
      rw [hcomm.mul_pow (2 ^ k), inv_pow, hk, inv_one, hτk, one_mul]
    have hone : z⁻¹ * τ z = 1 := l2out_two_elt_oddCore hmem hpow
    exact hτ (inv_mul_eq_one.mp hone).symm
  haveI : Fintype ↥(center (H ⧸ O)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let s : Finset ↥(center (H ⧸ O)) := {1, ⟨bar z, hbz⟩, ⟨bar (τ z), hbτz⟩}
  have hs : s.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hb_ne (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hbz_ne_one (congrArg Subtype.val h).symm,
        fun h => hbτz_ne_one (congrArg Subtype.val h).symm⟩
  rw [← hs]
  exact Finset.card_le_univ s

end CFSG.OddStandard.HigherRank.YamadaG23
