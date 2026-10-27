module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_thompson_false {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : 2 < Nat.card G) {t : G} {T T0 : Subgroup G}
    (hT : IsSylow2Of T ⊤) (hT0 : T0 ≤ T) (hidx : T0.relIndex T = 2)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htT : t ∈ T)
    (hnc : ∀ x : G, x⁻¹ * t * x ∉ T0) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, -, hNn, hsq, htN⟩ :=
    CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
      (X := ⊤) (P := T) (Q := T0) (u := t) le_top hT.2.1 hT.2.2 hT0 hidx
      (Subgroup.mem_top t)
      (orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1)
      (fun x _ => hnc x)
  have hNnormal : N.Normal := by
    have h := hNn.map ((⊤ : Subgroup G).subtype) fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : N ≤ ⊤)] at h
  haveI : N.Normal := hNnormal
  have hNbot : N = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal N with hbot | htop
    · exact hbot
    · exact absurd (htop ▸ Subgroup.mem_top t) htN
  have hsq2 : ∀ x : G, x ^ 2 = 1 := by
    intro x
    have hx : x ^ 2 ∈ N := hsq x (Subgroup.mem_top x)
    simpa [hNbot] using hx
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq2 a)
    have hb : b⁻¹ = b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq2 b)
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq2 (a * b))
    calc
      a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha, hb]
  haveI : IsMulCommutative G := IsMulCommutative.of_comm hcomm
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := exists_ne 1
  haveI : (Subgroup.zpowers g).Normal := Subgroup.normal_of_comm _
  have hne : Subgroup.zpowers g ≠ ⊥ := by
    intro h
    have hgH : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
    rw [h] at hgH
    exact hg (Subgroup.mem_bot.1 hgH)
  have htop : Subgroup.zpowers g = ⊤ :=
    (hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g)).resolve_left hne
  have hle2 : Nat.card G ≤ 2 := by
    rw [← Subgroup.card_top (G := G), ← htop, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hsq2 g))
  exact (not_lt.mpr hle2) hcard

end CFSG.OddStandard.SmallF3.Omega
