module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint.Multiplier CFSG.ComponentClassification.HarrisLit.T1.P54

private lemma l2out_pow_eq_one_of_dvd_zmod {a N : ℕ} (h : a ∣ N)
    (x : Multiplicative (ZMod a)) : x ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff _ _).mpr h, zero_mul]

theorem l2out_center_surj (hG : GriessNativeTable) {B : Type} [Group B]
    (hq : CFSG.IsQuasisimple B) (hL : CFSG.Blueprint.LieModel (B ⧸ center B) .PSU 4 3 1) :
    ∃ ψ : (generic .PSU 4 3 1 × exceptional .PSU 4 3 1) →* center B,
      Function.Surjective ψ := by
  have : Group.IsPerfect B := hq.1
  obtain ⟨-, ⟨eM⟩⟩ := hG (B ⧸ center B) .PSU 4 3 1 hL
  let ψ₀ : (generic .PSU 4 3 1 × exceptional .PSU 4 3 1) →*
      (QuotientGroup.mk' (center B)).ker :=
    (RankThree.PerfectCover.hopfMultiplierToKer (QuotientGroup.mk' (center B))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' (center B)).le).comp
      ((RankThree.PerfectCover.hopfMultiplierEquivGriess (B ⧸ center B)).toMonoidHom.comp
        eM.symm.toMonoidHom)
  have hψ₀ : Function.Surjective ψ₀ :=
    (RankThree.PerfectCover.hopfMultiplierToKer_surjective _ _ _).comp
      (((RankThree.PerfectCover.hopfMultiplierEquivGriess (B ⧸ center B)).surjective).comp
        eM.symm.surjective)
  refine ⟨(MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center B))).toMonoidHom.comp ψ₀, ?_⟩
  exact (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center B))).surjective.comp hψ₀

theorem l2out_center_dvd_four_cyclic (hG : GriessNativeTable) {B : Type} [Group B] [Finite B]
    (hq : CFSG.IsQuasisimple B) (hL : CFSG.Blueprint.LieModel (B ⧸ center B) .PSU 4 3 1)
    (hO : CFSG.oddCore B = ⊥) : Nat.card (center B) ∣ 4 ∧ IsCyclic (center B) := by
  obtain ⟨ψ, hψ⟩ := l2out_center_surj hG hq hL
  have hcardP : Nat.card (generic .PSU 4 3 1 × exceptional .PSU 4 3 1) = 36 := by
    rw [card_generic_prod_exceptional]
    decide
  have hdvd36 : Nat.card (center B) ∣ 36 := by
    rw [← hcardP]
    exact Subgroup.card_dvd_of_surjective hψ
  have hb : ¬ 3 ∣ Nat.card (center B) := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center B) 3 h3
    let N : Subgroup B := Subgroup.zpowers (c : B)
    have hNle : N ≤ center B := Subgroup.zpowers_le.mpr c.2
    have hNnormal : N.Normal := Subgroup.normal_of_le_center hNle
    have hcardN : Nat.card N = 3 := by
      change Nat.card (Subgroup.zpowers ((c : center B) : B)) = 3
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]
    have hoddN : Odd (Nat.card N) := by rw [hcardN]; norm_num
    have hle : N ≤ (⊥ : Subgroup B) := by
      have h := lit_le_oddCore B hNnormal hoddN
      rwa [hO] at h
    have hbot : N = ⊥ := le_bot_iff.mp hle
    have hmem : ((c : center B) : B) ∈ N := Subgroup.mem_zpowers _
    have hc1 : ((c : center B) : B) = 1 := by
      have h : ((c : center B) : B) ∈ (⊥ : Subgroup B) := by rw [← hbot]; exact hmem
      simpa using h
    have hceq : c = 1 := Subtype.ext (by simpa using hc1)
    rw [hceq, orderOf_one] at hc
    omega
  have hcop3 : Nat.Coprime (Nat.card (center B)) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hb).symm
  have hcop9 : Nat.Coprime (Nat.card (center B)) (3 ^ 2) := hcop3.pow_right 2
  have hdvd4 : Nat.card (center B) ∣ 4 := by
    have h : Nat.card (center B) ∣ 4 * 3 ^ 2 := by
      rw [show (4 * 3 ^ 2 : ℕ) = 36 by norm_num]
      exact hdvd36
    exact hcop9.dvd_of_dvd_mul_right h
  refine ⟨hdvd4, ?_⟩
  let ι : Multiplicative (ZMod (genericOrders .PSU 4 3 1).1) →*
      (generic .PSU 4 3 1 × exceptional .PSU 4 3 1) :=
    { toFun := fun a => ((a, 1), (1, 1))
      map_one' := rfl
      map_mul' := fun a b => by
        refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp }
  have hsurj : Function.Surjective (ψ.comp ι) := by
    haveI : Subsingleton (Multiplicative (ZMod (genericOrders .PSU 4 3 1).2)) := by
      have h2 : (genericOrders .PSU 4 3 1).2 = 1 := by decide
      rw [h2]
      infer_instance
    intro z
    obtain ⟨x, hx⟩ := hψ z
    rw [← hx]
    obtain ⟨⟨a, b⟩, ⟨d, e⟩⟩ := x
    have hmid : ψ ((1, b), (1, 1)) = 1 := by
      have hb' : b = 1 := Subsingleton.elim b 1
      rw [hb']
      exact map_one ψ
    have hexc : ψ ((1, 1), (d, e)) = 1 := by
      have hd3 : d ^ 3 = 1 := l2out_pow_eq_one_of_dvd_zmod (by decide) d
      have he3 : e ^ 3 = 1 := l2out_pow_eq_one_of_dvd_zmod (by decide) e
      let X : generic .PSU 4 3 1 × exceptional .PSU 4 3 1 := ((1, 1), (d, e))
      have h3 : X ^ 3 = 1 := by
        change ((1, 1), (d, e)) ^ 3 = 1
        refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp [hd3, he3]
      have hp3 : ψ ((1, 1), (d, e)) ^ 3 = 1 := by
        change ψ X ^ 3 = 1
        rw [← map_pow, h3, map_one]
      have hp4 : ψ ((1, 1), (d, e)) ^ 4 = 1 := by
        change ψ X ^ 4 = 1
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact (_root_.orderOf_dvd_natCard _).trans hdvd4
      have hy : ψ X = 1 :=
        (pow_eq_one_iff_of_coprime (a := ψ X) (m := 3) (n := 4)
          (by decide : Nat.Coprime 3 4)).mp ⟨hp3, hp4⟩
      exact hy
    have hxdecomp : ((a, 1), (1, 1)) * ((1, b), (1, 1)) * ((1, 1), (d, e)) =
        ((a, b), (d, e)) := by
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp
    have hpsi : ψ ((a, b), (d, e)) = ψ ((a, 1), (1, 1)) := by
      calc ψ ((a, b), (d, e))
          = ψ (((a, 1), (1, 1)) * ((1, b), (1, 1)) * ((1, 1), (d, e))) := by
              rw [← hxdecomp]
        _ = ψ ((a, 1), (1, 1)) * ψ ((1, b), (1, 1)) * ψ ((1, 1), (d, e)) := by
              rw [map_mul, map_mul]
        _ = ψ ((a, 1), (1, 1)) := by simp [hmid, hexc]
    exact ⟨a, hpsi.symm⟩
  exact isCyclic_of_surjective (ψ.comp ι) hsurj

end CFSG.OddStandard.HigherRank.YamadaG23
