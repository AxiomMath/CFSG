module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.AltPerm

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem z2s6_mod_alt_numeric {n r : ℕ} (hn : 7 ≤ n) (hr : 1 ≤ r) (h2r : 2 * r ≤ n)
    (h360 : 360 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial)
    (h64 : ¬ 2 ^ 6 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial) :
    n = 8 ∨ (n = 9 ∧ r = 1) := by
  have h5 : 5 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
    dvd_trans (by norm_num) h360
  have hr4 : r ≤ 4 := by
    by_contra h
    have hr5 : 5 ≤ r := by omega
    have h24 : 2 ^ 4 ∣ 2 ^ (r - 1) := pow_dvd_pow 2 (by omega)
    have h23 : 2 ^ 3 ∣ r.factorial :=
      dvd_trans (by norm_num) (Nat.factorial_dvd_factorial hr5)
    have h27 : 2 ^ 7 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      dvd_trans (dvd_trans (by norm_num : 2 ^ 7 ∣ 2 ^ 4 * 2 ^ 3) (mul_dvd_mul h24 h23))
        (dvd_mul_right _ _)
    exact h64 (dvd_trans (by norm_num) h27)
  have hf7 : n - 2 * r ≤ 7 := by
    by_contra h
    have hf8 : 8 ≤ n - 2 * r := by omega
    have h128 : 2 ^ 7 ∣ (n - 2 * r).factorial :=
      dvd_trans (by norm_num) (Nat.factorial_dvd_factorial hf8)
    have h27 : 2 ^ 7 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      dvd_trans h128 (dvd_mul_left _ _)
    exact h64 (dvd_trans (by norm_num) h27)
  have hf5 : 5 ≤ n - 2 * r := by
    by_contra h
    have hf4 : n - 2 * r ≤ 4 := by omega
    have hp : Nat.Prime 5 := by norm_num
    have hnd : ¬ 5 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
      rintro hd
      rcases hp.dvd_mul.mp hd with hd | hd
      · rcases hp.dvd_mul.mp hd with hd | hd
        · exact absurd (hp.dvd_of_dvd_pow hd) (by norm_num)
        · have := hp.dvd_factorial.mp hd
          omega
      · have := hp.dvd_factorial.mp hd
        omega
    exact hnd h5
  have hn15 : n ≤ 15 := by omega
  interval_cases n <;> interval_cases r <;> revert h360 h64 <;> decide

theorem mem_of_orderOf_eq_seven {F : Type} [Group F] [Finite F] (N : Subgroup F) [N.Normal]
    (hN : Nat.card (F ⧸ N) ∣ 1440) {x : F} (hx : orderOf x = 7) : x ∈ N := by
  have hdvd7 : orderOf (QuotientGroup.mk x : F ⧸ N) ∣ 7 := by
    rw [← hx]
    exact orderOf_map_dvd (QuotientGroup.mk' N) x
  have hdvdCard : orderOf (QuotientGroup.mk x : F ⧸ N) ∣ Nat.card (F ⧸ N) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime 7 1440 := by norm_num
  have h1 : orderOf (QuotientGroup.mk x : F ⧸ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd7 (dvd_trans hdvdCard hN)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)

theorem z2s6_mod_alt_arm {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J) {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) : Nonempty (S ≃* alternatingGroup (Fin 8)) := by
  rcases lt_or_ge n 7 with hnlt | hn7
  · interval_cases n
    · exfalso
      have hcardS : Nat.card S = 60 := by
        rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
      have hle : Nat.card ↥(fixedSubgroup σ) ≤ Nat.card S :=
        Subgroup.card_le_card_group (fixedSubgroup σ)
      rw [hcardS] at hle
      haveI : Nonempty ↥(fixedSubgroup σ) := ⟨1⟩
      have hpos : 0 < Nat.card ↥(fixedSubgroup σ) := Nat.card_pos
      have hge : 360 ≤ Nat.card ↥(fixedSubgroup σ) := Nat.le_of_dvd hpos hdata.dvd_card
      omega
    · exfalso
      have hcardS : Nat.card S = 360 := by
        rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
      have hle : Nat.card ↥(fixedSubgroup σ) ≤ Nat.card S :=
        Subgroup.card_le_card_group (fixedSubgroup σ)
      rw [hcardS] at hle
      haveI : Nonempty ↥(fixedSubgroup σ) := ⟨1⟩
      have hpos : 0 < Nat.card ↥(fixedSubgroup σ) := Nat.card_pos
      have hge : 360 ≤ Nat.card ↥(fixedSubgroup σ) := Nat.le_of_dvd hpos hdata.dvd_card
      have hcardF : Nat.card ↥(fixedSubgroup σ) = Nat.card S := by omega
      have htop : fixedSubgroup σ = ⊤ :=
        Subgroup.eq_top_of_card_eq (H := fixedSubgroup σ) hcardF
      have hfix : ∀ x : S, σ x = x := by
        intro x
        have hx : x ∈ fixedSubgroup σ := by rw [htop]; exact Subgroup.mem_top x
        exact hx
      have hσ1 : σ = 1 := MulEquiv.ext hfix
      have hord : orderOf σ = 1 := by rw [hσ1]; exact orderOf_one
      have h2 : orderOf σ = 2 := hdata.order_two
      omega
  · have hσ : orderOf σ = 2 := hdata.order_two
    obtain ⟨r, π, hr1, hr2, hcyc, hkey, hcard⟩ := exists_perm_fixedSubgroup_alt hn7 θ hσ
    have h360 := hdata.dvd_card
    have h64 := hdata.not_two_pow_six
    rw [hcard] at h360 h64
    rcases z2s6_mod_alt_numeric hn7 hr1 hr2 h360 h64 with hn8 | ⟨hn9, hr1'⟩
    · subst hn8
      exact ⟨θ⟩
    · exfalso
      subst hn9
      subst hr1'
      obtain ⟨x, y, hx7, hy7, hxy2⟩ := alt9_seven_pair θ hcyc hkey
      obtain ⟨N, hNnormal, hNodd, hNdvd⟩ := hdata.odd_quotient
      haveI := hNnormal
      have hxN : x ∈ N := mem_of_orderOf_eq_seven N hNdvd hx7
      have hyN : y ∈ N := mem_of_orderOf_eq_seven N hNdvd hy7
      have hxyN : x * y ∈ N := N.mul_mem hxN hyN
      exact hNodd.ne_two_of_dvd_nat (N.orderOf_dvd_natCard hxyN) hxy2

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
