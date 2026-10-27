module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208SpCen
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208SpAlt
public import CFSG.GH74.GLS.Stage2.Final.M12Odd
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128Cop

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage1.Thm4.L97 CFSG.GH74.GLS.Stage1.Thm6.Prod

section Key

variable {G : Type} [Group G] [Finite G] {z : G}

theorem toBar_not_center {t : G} (htC : t ∈ Cen z) (ht2 : orderOf t = 2) (htz : t ≠ z)
    (hz2 : orderOf z = 2) (hZ : Nat.card ↥(center (CentralizerBar z)) = 2) :
    toBar z ⟨t, htC⟩ ∉ center (CentralizerBar z) := by
  intro hcen
  have hzC : z ∈ Cen z := z_mem_Cen z
  have hzbc : toBar z ⟨z, hzC⟩ ∈ center (CentralizerBar z) :=
    Subgroup.mem_center_iff.2 fun c => zBar_central z c
  have hz1 : toBar z ⟨z, hzC⟩ ≠ 1 := by
    intro h
    have hk : (⟨z, hzC⟩ : ↥(Cen z)) ∈ (toBar z).ker := h
    rw [ker_toBar] at hk
    have hzo : z ∈ OddCore z := ⟨⟨z, hzC⟩, hk, rfl⟩
    have := coprime_orderOf_of_mem_OddCore hzo
    rw [hz2] at this
    exact absurd this (by norm_num)
  obtain ⟨c0, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥(center (CentralizerBar z)))).mp hZ
  have hzb : (⟨toBar z ⟨z, hzC⟩, hzbc⟩ : ↥(center (CentralizerBar z))) = c0 :=
    hu _ (fun h => hz1 (congrArg Subtype.val h))
  by_cases ht1 : toBar z ⟨t, htC⟩ = 1
  · have hk : (⟨t, htC⟩ : ↥(Cen z)) ∈ (toBar z).ker := ht1
    rw [ker_toBar] at hk
    have hto : t ∈ OddCore z := ⟨⟨t, htC⟩, hk, rfl⟩
    have := coprime_orderOf_of_mem_OddCore hto
    rw [ht2] at this
    exact absurd this (by norm_num)
  · have hte : (⟨toBar z ⟨t, htC⟩, hcen⟩ : ↥(center (CentralizerBar z))) = c0 :=
      hu _ (fun h => ht1 (congrArg Subtype.val h))
    have heq : toBar z ⟨t, htC⟩ = toBar z ⟨z, hzC⟩ := by
      have := hte.trans hzb.symm
      exact congrArg Subtype.val this
    have hk : (⟨t, htC⟩ : ↥(Cen z))⁻¹ * ⟨z, hzC⟩ ∈ (toBar z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    rw [ker_toBar] at hk
    have hmem : t⁻¹ * z ∈ OddCore z := ⟨_, hk, rfl⟩
    have htz' : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp htC
    have hsq : (t⁻¹ * z) ^ 2 = 1 := by
      have ht1' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
      have hz1' : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
      have hc : Commute t⁻¹ z := (Commute.inv_left (show Commute t z from htz'))
      rw [hc.mul_pow, inv_pow, ht1', inv_one, hz1', one_mul]
    have h1 : t⁻¹ * z = 1 :=
      eq_one_of_two_pow_of_mem_OddCore hmem (k := 1) (by simpa using hsq)
    exact htz (inv_mul_eq_one.mp h1)

theorem exists_involution_lift {t : G} (htC : t ∈ Cen z) (ht2 : orderOf t = 2)
    {w : CentralizerBar z} (hw2 : w ^ 2 = 1) (hwt : Commute w (toBar z ⟨t, htC⟩)) :
    ∃ (y : G) (hy : y ∈ Cen z), y * t = t * y ∧ y ^ 2 = 1 ∧ toBar z ⟨y, hy⟩ = w := by
  have htt : t * t = 1 := by
    rw [← sq]
    rw [← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨c, hct, hcw⟩ := Bender.Thm2.L128.exists_centralizer_preimage (N := Cen z) (z := t) htC htt w
    hwt.eq.symm
  have hc2 : c ^ 2 ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar, MonoidHom.mem_ker, map_pow]
    have : toBar z c = w := hcw
    rw [this, hw2]
  have hc2o : ((c ^ 2 : ↥(Cen z)) : G) ∈ OddCore z := ⟨c ^ 2, hc2, rfl⟩
  have hodd : Odd (orderOf (c ^ 2)) := by
    have h1 := coprime_orderOf_of_mem_OddCore hc2o
    rw [Subgroup.orderOf_coe] at h1
    exact Nat.coprime_two_left.mp h1
  obtain ⟨r, hr⟩ := hodd
  refine ⟨((c ^ orderOf (c ^ 2) : ↥(Cen z)) : G), (c ^ orderOf (c ^ 2)).2, ?_, ?_, ?_⟩
  · have hct' : (c : G) * t = t * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp hct
    have := (Commute.pow_left (show Commute (c : G) t from hct') (orderOf (c ^ 2))).eq
    simpa using this
  · have : (c ^ orderOf (c ^ 2)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val this
  · have : toBar z c = w := hcw
    rw [map_pow, this, hr, pow_succ, pow_mul, hw2, one_pow, one_mul]

theorem conj_oddCore_le {n : ℕ} (hn : 8 ≤ n) (hn' : n ≤ 11) (h4a : Thm4a (Cen z))
    (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n) (hz2 : orderOf z = 2)
    {t g : G} (htC : t ∈ Cen z) (ht2 : orderOf t = 2)
    (htk : toBar z ⟨t, htC⟩ ∉ center (CentralizerBar z)) (hg : g * z * g⁻¹ = t) :
    ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := by
  intro a ha
  obtain ⟨π, hπ, hker⟩ := exists_twoCover hcov
  have hq : CFSG.IsQuasisimple (CentralizerBar z) := hcov.1
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp htC
  have haC : a ∈ Cen z := Bender.Thm2.L128.pPrimeCoreOf_le (Cen z) ha
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haC
  have hzt : z = g⁻¹ * t * g := by rw [← hg]; group
  have hy0C : g⁻¹ * z * g ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * z = g⁻¹ * z * g * (g⁻¹ * t * g) := by rw [← hzt]
      _ = g⁻¹ * (z * t) * g := by group
      _ = g⁻¹ * (t * z) * g := by rw [htz]
      _ = z * (g⁻¹ * z * g) := by
        calc g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
          _ = z * (g⁻¹ * z * g) := by rw [← hzt]
  have hy0 : (g⁻¹ * z * g) ^ (2 ^ 1) = 1 := by
    have : (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [pow_one, this, ← hz2, pow_orderOf_eq_one z]
    group
  have hcz : (g⁻¹ * z * g) * a = a * (g⁻¹ * z * g) := twoElt_comm_oddCore h4a hq hy0C hy0 a ha
  have hz' : z * (g * a * g⁻¹) = (g * a * g⁻¹) * z := by
    calc z * (g * a * g⁻¹) = g * ((g⁻¹ * z * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcz]
      _ = (g * a * g⁻¹) * z := by group
  have ha'C : g * a * g⁻¹ ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hz'.symm
  have hat : (g * a * g⁻¹) * t = t * (g * a * g⁻¹) := by
    rw [← hg]
    calc g * a * g⁻¹ * (g * z * g⁻¹) = g * (a * z) * g⁻¹ := by group
      _ = g * (z * a) * g⁻¹ := by rw [haz]
      _ = g * z * g⁻¹ * (g * a * g⁻¹) := by group
  let ν : CentralizerBar z := toBar z ⟨g * a * g⁻¹, ha'C⟩
  have hνodd : Odd (orderOf ν) := by
    have h1 : orderOf ν ∣ orderOf (⟨g * a * g⁻¹, ha'C⟩ : ↥(Cen z)) := orderOf_map_dvd (toBar z) _
    have h2 : orderOf (⟨g * a * g⁻¹, ha'C⟩ : ↥(Cen z)) = orderOf a := by
      rw [Subgroup.orderOf_mk]
      have := MulEquiv.orderOf_eq (MulAut.conj g) a
      rw [MulAut.conj_apply] at this
      exact this
    rw [h2] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_orderOf_of_mem_OddCore ha)) h1
  have ht2' : orderOf (toBar z ⟨t, htC⟩) = 2 := by
    have hsq : toBar z ⟨t, htC⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨t, htC⟩ : ↥(Cen z)) ^ 2 = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, OneMemClass.coe_one]
        rw [← ht2]
        exact pow_orderOf_eq_one t
      rw [this, map_one]
    have hne : toBar z ⟨t, htC⟩ ≠ 1 := fun h => htk (h ▸ one_mem _)
    exact orderOf_eq_prime hsq hne
  have hνw : ∀ w : CentralizerBar z, w ^ 2 = 1 → Commute w (toBar z ⟨t, htC⟩) → Commute ν w := by
    intro w hw2 hwt
    obtain ⟨y, hyC, hyt, hy2, hyw⟩ := exists_involution_lift htC ht2 hw2 hwt
    have hyC' : g⁻¹ * y * g ∈ Cen z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * z = g⁻¹ * (y * t) * g := by rw [hzt]; group
        _ = g⁻¹ * (t * y) * g := by rw [hyt]
        _ = z * (g⁻¹ * y * g) := by rw [hzt]; group
    have hy' : (g⁻¹ * y * g) ^ (2 ^ 1) = 1 := by
      have : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by
        rw [pow_two, pow_two]
        group
      rw [pow_one, this, hy2]
      group
    have hcy := twoElt_comm_oddCore h4a hq hyC' hy' a ha
    have hyc : y * (g * a * g⁻¹) = (g * a * g⁻¹) * y := by
      calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcy]
        _ = (g * a * g⁻¹) * y := by group
    have hcomm : Commute w ν := by
      rw [← hyw]
      show toBar z ⟨y, hyC⟩ * toBar z ⟨g * a * g⁻¹, ha'C⟩ = toBar z ⟨g * a * g⁻¹, ha'C⟩ * toBar z ⟨y, hyC⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyc
    exact hcomm.symm
  have hν1 : ν = 1 :=
    eq_one_of_commute_involutions hπ hn hn' ht2' (by rw [hker]; exact htk) hνodd hνw
  have hk : (⟨g * a * g⁻¹, ha'C⟩ : ↥(Cen z)) ∈ (toBar z).ker := hν1
  rw [ker_toBar] at hk
  exact ⟨_, hk, rfl⟩

end Key

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp
