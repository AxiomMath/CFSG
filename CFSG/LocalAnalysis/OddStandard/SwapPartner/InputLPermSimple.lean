module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPerm
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

open scoped Nat

variable {m : ℕ}

private lemma eight_le_of_factorial_ge {f : ℕ} (h : 40320 ≤ (f)!) : 8 ≤ f := by
  by_contra hf
  have hf' : f ≤ 7 := by omega
  have hle : (f)! ≤ 7! := Nat.factorial_le hf'
  norm_num [Nat.factorial] at hle
  omega

private lemma two_le_of_factorial_ge {f : ℕ} (h : 20160 ≤ (f)!) : 2 ≤ f := by
  by_contra hf
  have hf' : f ≤ 1 := by omega
  have hle : (f)! ≤ 1! := Nat.factorial_le hf'
  norm_num [Nat.factorial] at hle
  omega

private lemma seven_le_of_dvd {k : ℕ} (h : 20160 ∣ 2 ^ k * (k)!) : 7 ≤ k := by
  have h7 : 7 ∣ 2 ^ k * (k)! := dvd_trans (by norm_num : 7 ∣ 20160) h
  rcases Nat.prime_seven.dvd_mul.mp h7 with hpow | hfac
  · exact absurd (Nat.prime_seven.dvd_of_dvd_pow hpow) (by norm_num)
  · exact (Nat.prime_seven.dvd_factorial).mp hfac

theorem card_alt_inf_centralizer_gt {π : Perm (Fin m)} (hπ : π * π = 1) (h1 : π ≠ 1)
    (hk : 7 ≤ Multiset.card π.cycleType) :
    161280 < Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
      Subgroup (Perm (Fin m))) := by
  let k := Multiset.card π.cycleType
  let f := Fintype.card {x : Fin m // π x = x}
  have hk' : 7 ≤ k := hk
  have h : 2 * Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
      Subgroup (Perm (Fin m))) = (f)! * 2 ^ k * (k)! := two_mul_card_alt_inf_centralizer hπ h1
  have hf : 1 ≤ (f)! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero f)
  have h2k : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk'
  have hkf : 7! ≤ (k)! := Nat.factorial_le hk'
  have hmul : 2 ^ 7 * 7! ≤ (f)! * 2 ^ k * (k)! := by
    have hA : 2 ^ 7 ≤ (f)! * 2 ^ k := by
      calc 2 ^ 7 = 1 * 2 ^ 7 := by ring
        _ ≤ (f)! * 2 ^ k := Nat.mul_le_mul hf h2k
    calc 2 ^ 7 * 7! ≤ ((f)! * 2 ^ k) * (k)! := Nat.mul_le_mul hA hkf
      _ = (f)! * 2 ^ k * (k)! := rfl
  have hbig : 645120 ≤ (f)! * 2 ^ k * (k)! := by
    norm_num [Nat.factorial] at hmul
    exact hmul
  have hmain : 645120 ≤ 2 * Nat.card (alternatingGroup (Fin m) ⊓
      centralizer ({π} : Set (Perm (Fin m))) : Subgroup (Perm (Fin m))) := by
    rw [h]
    exact hbig
  omega

theorem le_fixingMoved_of_simple {π : Perm (Fin m)} (hπ : π * π = 1) (h1 : π ≠ 1)
    {A : Subgroup (Perm (Fin m))}
    (hA : A ≤ alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))))
    (hcard : Nat.card A = 20160) (hsimple : IsSimpleGroup A)
    (hle : Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
      Subgroup (Perm (Fin m))) ≤ 161280) :
    A ≤ fixingMoved π := by
  have hnorm : ((A ⊓ fixingMoved π).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨A.mul_mem (A.mul_mem hk hh.1) (A.inv_mem hk),
      conj_mem_fixingMoved (hA hk).2 hh.2⟩
  haveI := hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal ((A ⊓ fixingMoved π).subgroupOf A) with hbot | htop
  · exfalso
    have hbot' : A ⊓ fixingMoved π = ⊥ := by
      have hd : Disjoint (A ⊓ fixingMoved π) A := (Subgroup.subgroupOf_eq_bot).mp hbot
      rw [disjoint_iff] at hd
      rwa [inf_eq_left.mpr inf_le_left] at hd
    set C : Subgroup (Perm (Fin m)) := centralizer ({π} : Set (Perm (Fin m))) with hC
    have hAD' : A ≤ C := fun x hx => (hA hx).2
    have hND' : fixingMoved π ≤ C := fixingMoved_le_centralizer hπ
    let N' : Subgroup C := (fixingMoved π).subgroupOf C
    haveI hN'norm : N'.Normal := by
      show ((fixingMoved π).subgroupOf C).Normal
      rw [Subgroup.normal_subgroupOf_iff hND']
      intro h k hh hk
      exact conj_mem_fixingMoved hk hh
    have hinj : Function.Injective
        ((QuotientGroup.mk' N').comp (Subgroup.inclusion hAD')) := by
      intro a b hab
      have h1 : ((QuotientGroup.mk' N').comp (Subgroup.inclusion hAD')) (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      have h2 : Subgroup.inclusion hAD' (a * b⁻¹) ∈ N' := by
        simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          using h1
      rw [Subgroup.mem_subgroupOf] at h2
      have hmem : ((a * b⁻¹ : A) : Perm (Fin m)) ∈ A ⊓ fixingMoved π :=
        ⟨(a * b⁻¹).2, h2⟩
      rw [hbot'] at hmem
      simp only [Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp (Subtype.ext hmem)
    have hdiv : 20160 ∣ Nat.card (C ⧸ N') := by
      have h := Subgroup.card_dvd_of_injective
        ((QuotientGroup.mk' N').comp (Subgroup.inclusion hAD')) hinj
      rwa [hcard] at h
    have hN'card : Nat.card N' = (Fintype.card {x : Fin m // π x = x}).factorial := by
      have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND').toEquiv
      rwa [card_fixingMoved (π := π)] at h
    have hDcard : Nat.card C = (Fintype.card {x : Fin m // π x = x}).factorial *
        2 ^ Multiset.card π.cycleType * (Multiset.card π.cycleType).factorial := by
      rw [hC]
      rw [CFSG.OddStandard.AltStdSec.nat_card_centralizer_of_mul_self (σ := π) hπ,
        Fintype.card_fin]
      have hm : m - 2 * Multiset.card π.cycleType = Fintype.card {x : Fin m // π x = x} := by
        have hsum := card_fixed_add_two_mul_card_cycleType (π := π) hπ
        omega
      rw [hm]
    have hquot : Nat.card (C ⧸ N') = 2 ^ Multiset.card π.cycleType *
        (Multiset.card π.cycleType).factorial := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
      rw [hDcard, hN'card] at h
      rw [mul_comm (Nat.card (C ⧸ N'))] at h
      rw [mul_assoc] at h
      exact (Nat.mul_left_cancel (Nat.factorial_pos _) h).symm
    have hdiv2 : 20160 ∣ 2 ^ Multiset.card π.cycleType *
        (Multiset.card π.cycleType).factorial := by
      rwa [hquot] at hdiv
    have hk7 : 7 ≤ Multiset.card π.cycleType := seven_le_of_dvd hdiv2
    have hgt := card_alt_inf_centralizer_gt (π := π) hπ h1 hk7
    exact absurd hgt (not_lt.mpr hle)
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

theorem card_fixed_eq_eight {π : Perm (Fin m)} (hπ : π * π = 1) (h1 : π ≠ 1)
    {A : Subgroup (Perm (Fin m))}
    (hA : A ≤ alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))))
    (hcard : Nat.card A = 20160) (hsimple : IsSimpleGroup A)
    (hle : Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
      Subgroup (Perm (Fin m))) ≤ 161280) :
    Fintype.card {x : Fin m // π x = x} = 8 ∧ Multiset.card π.cycleType ≤ 2 ∧
      A = altFixingMoved π := by
  have hAN : A ≤ fixingMoved π := le_fixingMoved_of_simple hπ h1 hA hcard hsimple hle
  have hAalt : A ≤ alternatingGroup (Fin m) := fun x hx => (hA hx).1
  have hAle : A ≤ altFixingMoved π := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hAalt hx, hAN hx⟩
  have hcard_le : Nat.card A ≤ Nat.card (altFixingMoved π) := Subgroup.card_le_of_le hAle
  have hAF_ge : 20160 ≤ Nat.card (altFixingMoved π) := by rwa [hcard] at hcard_le
  have hcardN_le : Nat.card A ≤ Nat.card (fixingMoved π) := Subgroup.card_le_of_le hAN
  have hf_ge20160 : 20160 ≤ (Fintype.card {x : Fin m // π x = x}).factorial := by
    rw [card_fixingMoved (π := π)] at hcardN_le
    rwa [hcard] at hcardN_le
  have hf2 : 2 ≤ Fintype.card {x : Fin m // π x = x} := two_le_of_factorial_ge hf_ge20160
  have htwo := two_mul_card_altFixingMoved (π := π) hf2
  have hf_ge40320 : 40320 ≤ (Fintype.card {x : Fin m // π x = x}).factorial := by
    have h : 2 * 20160 ≤ 2 * Nat.card (altFixingMoved π) := Nat.mul_le_mul_left 2 hAF_ge
    rw [htwo] at h
    norm_num at h
    exact h
  have hf8 : 8 ≤ Fintype.card {x : Fin m // π x = x} := eight_le_of_factorial_ge hf_ge40320
  have hP : (Fintype.card {x : Fin m // π x = x}).factorial *
      (2 ^ Multiset.card π.cycleType * (Multiset.card π.cycleType).factorial) ≤ 322560 := by
    have h := two_mul_card_alt_inf_centralizer (π := π) hπ h1
    have h2 : 2 * Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
        Subgroup (Perm (Fin m))) ≤ 2 * 161280 := Nat.mul_le_mul_left 2 hle
    rw [h] at h2
    rw [mul_assoc] at h2
    norm_num at h2
    exact h2
  have hf_le8 : Fintype.card {x : Fin m // π x = x} ≤ 8 := by
    by_contra hf
    have hf' : 9 ≤ Fintype.card {x : Fin m // π x = x} := by omega
    have h9 : 9! ≤ (Fintype.card {x : Fin m // π x = x}).factorial := Nat.factorial_le hf'
    have h4 : (Fintype.card {x : Fin m // π x = x}).factorial ≤ 322560 :=
      le_trans (Nat.le_mul_of_pos_right _
        (Nat.mul_pos (Nat.pow_pos (by norm_num : 0 < 2)) (Nat.factorial_pos _))) hP
    norm_num [Nat.factorial] at h9
    omega
  have hf8eq : Fintype.card {x : Fin m // π x = x} = 8 := le_antisymm hf_le8 hf8
  have hk2 : Multiset.card π.cycleType ≤ 2 := by
    by_contra hk
    have hk' : 3 ≤ Multiset.card π.cycleType := by omega
    have h1' : 8 ≤ 2 ^ Multiset.card π.cycleType := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk'
      norm_num [Nat.factorial] at this
      exact this
    have h2' : 6 ≤ (Multiset.card π.cycleType).factorial := by
      have := Nat.factorial_le hk'
      norm_num [Nat.factorial] at this
      exact this
    have h3' : 48 ≤ 2 ^ Multiset.card π.cycleType * (Multiset.card π.cycleType).factorial := by
      calc 48 = 8 * 6 := by norm_num
        _ ≤ 2 ^ Multiset.card π.cycleType * (Multiset.card π.cycleType).factorial :=
          Nat.mul_le_mul h1' h2'
    have h4 : (Fintype.card {x : Fin m // π x = x}).factorial * 48 ≤ 322560 :=
      le_trans (Nat.mul_le_mul_left _ h3') hP
    have h5 : 8! ≤ (Fintype.card {x : Fin m // π x = x}).factorial := Nat.factorial_le hf8
    norm_num [Nat.factorial] at h4 h5
    omega
  have hcardAF : Nat.card (altFixingMoved π) = 20160 := by
    have h := htwo
    rw [hf8eq] at h
    norm_num [Nat.factorial] at h
    omega
  have hAeq : A = altFixingMoved π :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardAF, hcard])
  exact ⟨hf8eq, hk2, hAeq⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
