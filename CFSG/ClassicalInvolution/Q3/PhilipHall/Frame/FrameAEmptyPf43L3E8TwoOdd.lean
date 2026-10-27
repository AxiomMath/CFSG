module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8TwoCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Fac

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem withSylow (cfg : L3E8Cfg K z J zJ H Q E S) {S' : Subgroup T}
    (hS' : IsSylow2In S' (sigmaNorm K)) (hzS' : z ∈ S') : L3E8Cfg K z J zJ H Q (Q ⊓ S') S' :=
  { cfg with hS := hS', hzS := hzS', hE := rfl }

theorem oddCore_cent_prod_le (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) (hnot : h⁻¹ * z * h ∉ firstFactor K) :
    oddCoreOf (Subgroup.centralizer ({z * (h⁻¹ * z * h)} : Set T)) ≤ sigmaNorm K := by
  have hz := cfg.datum.unique
  set w : T := h⁻¹ * z * h with hw
  set X : Subgroup T := Subgroup.centralizer ({z * w} : Set T) with hX
  have hhM : h⁻¹ ∈ sigmaNorm K := (sigmaNorm K).inv_mem (cfg.prod_mem_sigmaNorm hc)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hF₂ne : conjSub (1 : T) (firstFactor K) ≠ conjSub h⁻¹ (firstFactor K) := by
    rw [h1Ht]
    exact (cfg.prod_factor_ne hnot).symm
  have hwu := cfg.prod_isUniqueInvolution h
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one, pow_one])
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hwu.sq) hwu.ne_one, pow_one])
  have hzwN : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers w : Set T) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_left (show Commute w z from hc.symm) k
  have hP₀ : IsPGroup 2 ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers w) :=
    hz2.to_sup_of_normal_right' hw2 hzwN
  have hzM : z ∈ sigmaNorm K := cfg.cz_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hwM : w ∈ sigmaNorm K := cfg.cz_le (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm)
  obtain ⟨S', hS', hP₀S'⟩ := IsSylow2In.exists_ge hP₀
    (sup_le (Subgroup.zpowers_le.mpr hzM) (Subgroup.zpowers_le.mpr hwM))
  have hzS' : z ∈ S' := hP₀S' (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hwS' : w ∈ S' := hP₀S' (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have cfg' := cfg.withSylow hS' hzS'
  obtain ⟨hEab, hE8⟩ := cfg'.E8
  have hE'X : Q ⊓ S' ≤ X := by
    intro e he
    have he' : e ∈ firstFactor K := cfg.Q_le_ht he.1
    have hez : e * z = z * e := by
      have := hEab.1.1.comm ⟨e, he⟩ ⟨z, cfg'.z_mem_E⟩
      simpa using congrArg Subtype.val this
    have hew : e * w = w * e := by
      have hc1 := cfg.factor_comm (Subgroup.one_mem _) hhM hF₂ne (by rw [h1Ht]; exact he')
        (cfg.prod_mem_factor h)
      have hcS : e * w * e⁻¹ * w⁻¹ ∈ S' :=
        S'.mul_mem (S'.mul_mem (S'.mul_mem he.2 hwS') (S'.inv_mem he.2)) (S'.inv_mem hwS')
      have h1 : e * w * e⁻¹ * w⁻¹ = 1 :=
        eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc1
          (hS'.2.1.to_le (Subgroup.zpowers_le.mpr hcS))
      have h2 := mul_inv_eq_one.mp h1
      calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h2]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e * (z * w) = (e * z) * w := by group
      _ = (z * e) * w := by rw [hez]
      _ = z * (e * w) := by group
      _ = z * (w * e) := by rw [hew]
      _ = z * w * e := by group
  have hAX : Q ⊓ S' ≤ Subgroup.normalizer (oddCoreOf X : Set T) := fun e he =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hE'X he))
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreOf X)) :=
    Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard X)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hEab (by rw [hE8]; norm_num) hAX hcop
  rw [← hgen]
  refine iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_
  obtain ⟨l, hl, hle⟩ := cfg'.E_conj he he1
  exact inf_le_right.trans (T7A.centralizer_conj_le (H := sigmaNorm K) (y := l⁻¹)
    ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl)) (by rw [inv_inv, hle]) cfg.cz_le)

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
