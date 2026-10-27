module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLeafRootCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzD

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78

private theorem eq_of_rho0_eq
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160)
    {a b : Equiv.Perm (Fin 1782)} (ha : a ∈ K) (hb : b ∈ K)
    (h : rho0 ⟨a, hK ha⟩ = rho0 ⟨b, hK hb⟩) : a = b := by
  obtain ⟨hperf', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hmem : (⟨a, hK ha⟩ : invE 0)⁻¹ * ⟨b, hK hb⟩ ∈ K.subgroupOf (invE 0) :=
    Subgroup.mem_subgroupOf.2 (K.mul_mem (K.inv_mem ha) hb)
  have h1 : rho0 ((⟨a, hK ha⟩ : invE 0)⁻¹ * ⟨b, hK hb⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := suz_quot2Data.eq_one_of_map_eq_one hperf' hcard' hmem h1
  have h3 : (⟨a, hK ha⟩ : invE 0) = ⟨b, hK hb⟩ := by
    calc (⟨a, hK ha⟩ : invE 0)
        = (⟨a, hK ha⟩ : invE 0) * ((⟨a, hK ha⟩ : invE 0)⁻¹ * ⟨b, hK hb⟩) := by
          rw [h2, mul_one]
      _ = ⟨b, hK hb⟩ := by group
  exact congrArg Subtype.val h3

theorem exists_mem_rho0_conj_eq_repPerm_six
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0) (hperf : Group.IsPerfect K)
    (hcard : Nat.card K = 20160) {d : Equiv.Perm (Fin 1782)} (hd : d ∈ K) (hd2 : orderOf d = 2) :
    ∃ c, ∃ hc : c ∈ K, rho0 ⟨c, hK hc⟩ * rho0 ⟨d, hK hd⟩ * (rho0 ⟨c, hK hc⟩)⁻¹ = repPerm 6 := by
  obtain ⟨hperf', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hmap := suz_quot2Data.map_eq hperf' hcard'
  have hxmem : rho0 ⟨d, hK hd⟩ ∈ suzD := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem rho0 (Subgroup.mem_subgroupOf.2 hd)
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rwa [hd2] at h
  have hx2 : rho0 ⟨d, hK hd⟩ * rho0 ⟨d, hK hd⟩ = 1 := by
    have hsub : (⟨d, hK hd⟩ : invE 0) * ⟨d, hK hd⟩ = 1 := Subtype.ext hdd
    rw [← map_mul, hsub, map_one]
  have hx1 : rho0 ⟨d, hK hd⟩ ≠ 1 := by
    intro h1
    have h2 := suz_quot2Data.eq_one_of_map_eq_one hperf' hcard'
      (Subgroup.mem_subgroupOf.2 hd) h1
    have h3 : d = 1 := congrArg Subtype.val h2
    rw [h3, orderOf_one] at hd2
    norm_num at hd2
  have hcls := suzD_involution_class suz_classCheck hxmem hx2 hx1
  have hconj : IsConj (⟨rho0 ⟨d, hK hd⟩, hxmem⟩ : suzD) ⟨repPerm 6, repPerm_mem 6⟩ :=
    ConjClasses.mk_eq_mk_iff_isConj.1 (hcls.trans rfl)
  obtain ⟨cD, hcD⟩ := isConj_iff.1 hconj
  have hcD' : (cD : Equiv.Perm (Fin 42)) * rho0 ⟨d, hK hd⟩ *
      (cD : Equiv.Perm (Fin 42))⁻¹ = repPerm 6 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hcD
  have hcDmem : (cD : Equiv.Perm (Fin 42)) ∈ (K.subgroupOf (invE 0)).map rho0 := by
    rw [hmap]
    exact cD.2
  obtain ⟨k, hk, hkc⟩ := hcDmem
  refine ⟨(k : Equiv.Perm (Fin 1782)), Subgroup.mem_subgroupOf.1 hk, ?_⟩
  have hsub : (⟨(k : Equiv.Perm (Fin 1782)), hK (Subgroup.mem_subgroupOf.1 hk)⟩ : invE 0) = k :=
    Subtype.ext rfl
  rw [hsub, hkc]
  exact hcD'

theorem exists_mem_rho0_eq_suzRootPerm
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0) (hperf : Group.IsPerfect K)
    (hcard : Nat.card K = 20160) (j : ℕ) :
    ∃ y, ∃ hy : y ∈ K, rho0 ⟨y, hK hy⟩ = suzRootPerm j := by
  obtain ⟨hperf', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hmap := suz_quot2Data.map_eq hperf' hcard'
  have hmem : suzRootPerm j ∈ (K.subgroupOf (invE 0)).map rho0 := by
    rw [hmap]
    exact suzRootPerm_mem j
  obtain ⟨y, hy, hry⟩ := hmem
  refine ⟨(y : Equiv.Perm (Fin 1782)), Subgroup.mem_subgroupOf.1 hy, ?_⟩
  rw [show (⟨(y : Equiv.Perm (Fin 1782)), hK (Subgroup.mem_subgroupOf.1 hy)⟩ : invE 0) = y
    from Subtype.ext rfl]
  exact hry

theorem exists_mem_invE_zero_and_rho0_mem_suzD_of_forall_comm
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0) (hperf : Group.IsPerfect K)
    (hcard : Nat.card K = 20160) {d : Equiv.Perm (Fin 1782)} (hd : d ∈ K) (hd2 : orderOf d = 2)
    {τ : Equiv.Perm (Fin 1782)} (hτ : τ ∈ suzT) (hτt : τ * suzInv 0 = suzInv 0 * τ)
    (hc : ∀ x ∈ K, x * d = d * x → x ^ 4 = 1 → τ * x = x * τ) :
    ∃ hτE : τ ∈ invE 0, rho0 ⟨τ, hτE⟩ ∈ suzD := by
  obtain ⟨hperf', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hmap := suz_quot2Data.map_eq hperf' hcard'
  obtain ⟨c, hcK, hc_conj⟩ := exists_mem_rho0_conj_eq_repPerm_six hK hperf hcard hd hd2
  obtain ⟨y0, hy0K, hy0⟩ := exists_mem_rho0_eq_suzRootPerm hK hperf hcard 0
  obtain ⟨y1, hy1K, hy1⟩ := exists_mem_rho0_eq_suzRootPerm hK hperf hcard 1
  have hx0K : c⁻¹ * y0 * c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hcK) hy0K) hcK
  have hx1K : c⁻¹ * y1 * c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hcK) hy1K) hcK
  have hcE : c ∈ invE 0 := hK hcK
  have hy0E : y0 ∈ invE 0 := hK hy0K
  have hy1E : y1 ∈ invE 0 := hK hy1K
  have hdconj : rho0 ⟨d, hK hd⟩ =
      (rho0 ⟨c, hK hcK⟩)⁻¹ * repPerm 6 * rho0 ⟨c, hK hcK⟩ := by
    rw [← hc_conj]
    group
  have hY0comm : rho0 ⟨y0, hK hy0K⟩ * repPerm 6 = repPerm 6 * rho0 ⟨y0, hK hy0K⟩ := by
    rw [hy0]
    exact suzRootPerm_comm (j := 0) (by norm_num)
  have hY1comm : rho0 ⟨y1, hK hy1K⟩ * repPerm 6 = repPerm 6 * rho0 ⟨y1, hK hy1K⟩ := by
    rw [hy1]
    exact suzRootPerm_comm (j := 1) (by norm_num)
  have hY0pow : rho0 ⟨y0, hK hy0K⟩ ^ 4 = 1 := by
    rw [hy0]
    exact suzRootPerm_pow_four (j := 0) (by norm_num)
  have hY1pow : rho0 ⟨y1, hK hy1K⟩ ^ 4 = 1 := by
    rw [hy1]
    exact suzRootPerm_pow_four (j := 1) (by norm_num)
  have hX0 : rho0 ⟨c⁻¹ * y0 * c, hK hx0K⟩ =
      (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y0, hK hy0K⟩ * rho0 ⟨c, hK hcK⟩ := by
    rw [show (⟨c⁻¹ * y0 * c, hK hx0K⟩ : invE 0) =
      (⟨c, hK hcK⟩ : invE 0)⁻¹ * ⟨y0, hK hy0K⟩ * ⟨c, hK hcK⟩ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv]
  have hX1 : rho0 ⟨c⁻¹ * y1 * c, hK hx1K⟩ =
      (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y1, hK hy1K⟩ * rho0 ⟨c, hK hcK⟩ := by
    rw [show (⟨c⁻¹ * y1 * c, hK hx1K⟩ : invE 0) =
      (⟨c, hK hcK⟩ : invE 0)⁻¹ * ⟨y1, hK hy1K⟩ * ⟨c, hK hcK⟩ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv]
  have hcomm0 : (c⁻¹ * y0 * c) * d = d * (c⁻¹ * y0 * c) := by
    refine eq_of_rho0_eq hK hperf hcard (K.mul_mem hx0K hd) (K.mul_mem hd hx0K) ?_
    rw [show (⟨(c⁻¹ * y0 * c) * d, hK (K.mul_mem hx0K hd)⟩ : invE 0) =
        ⟨c⁻¹ * y0 * c, hK hx0K⟩ * ⟨d, hK hd⟩ from Subtype.ext rfl,
      show (⟨d * (c⁻¹ * y0 * c), hK (K.mul_mem hd hx0K)⟩ : invE 0) =
        ⟨d, hK hd⟩ * ⟨c⁻¹ * y0 * c, hK hx0K⟩ from Subtype.ext rfl,
      map_mul, map_mul, hX0, hdconj]
    calc (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y0, hK hy0K⟩ * rho0 ⟨c, hK hcK⟩ *
          ((rho0 ⟨c, hK hcK⟩)⁻¹ * repPerm 6 * rho0 ⟨c, hK hcK⟩)
        = (rho0 ⟨c, hK hcK⟩)⁻¹ * (rho0 ⟨y0, hK hy0K⟩ * repPerm 6) *
            rho0 ⟨c, hK hcK⟩ := by group
      _ = (rho0 ⟨c, hK hcK⟩)⁻¹ * (repPerm 6 * rho0 ⟨y0, hK hy0K⟩) *
            rho0 ⟨c, hK hcK⟩ := by rw [hY0comm]
      _ = (rho0 ⟨c, hK hcK⟩)⁻¹ * repPerm 6 * rho0 ⟨c, hK hcK⟩ *
            ((rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y0, hK hy0K⟩ * rho0 ⟨c, hK hcK⟩) := by group
  have hcomm1 : (c⁻¹ * y1 * c) * d = d * (c⁻¹ * y1 * c) := by
    refine eq_of_rho0_eq hK hperf hcard (K.mul_mem hx1K hd) (K.mul_mem hd hx1K) ?_
    rw [show (⟨(c⁻¹ * y1 * c) * d, hK (K.mul_mem hx1K hd)⟩ : invE 0) =
        ⟨c⁻¹ * y1 * c, hK hx1K⟩ * ⟨d, hK hd⟩ from Subtype.ext rfl,
      show (⟨d * (c⁻¹ * y1 * c), hK (K.mul_mem hd hx1K)⟩ : invE 0) =
        ⟨d, hK hd⟩ * ⟨c⁻¹ * y1 * c, hK hx1K⟩ from Subtype.ext rfl,
      map_mul, map_mul, hX1, hdconj]
    calc (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y1, hK hy1K⟩ * rho0 ⟨c, hK hcK⟩ *
          ((rho0 ⟨c, hK hcK⟩)⁻¹ * repPerm 6 * rho0 ⟨c, hK hcK⟩)
        = (rho0 ⟨c, hK hcK⟩)⁻¹ * (rho0 ⟨y1, hK hy1K⟩ * repPerm 6) *
            rho0 ⟨c, hK hcK⟩ := by group
      _ = (rho0 ⟨c, hK hcK⟩)⁻¹ * (repPerm 6 * rho0 ⟨y1, hK hy1K⟩) *
            rho0 ⟨c, hK hcK⟩ := by rw [hY1comm]
      _ = (rho0 ⟨c, hK hcK⟩)⁻¹ * repPerm 6 * rho0 ⟨c, hK hcK⟩ *
            ((rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y1, hK hy1K⟩ * rho0 ⟨c, hK hcK⟩) := by group
  have hpow0 : (c⁻¹ * y0 * c) ^ 4 = 1 := by
    refine eq_of_rho0_eq hK hperf hcard (K.pow_mem hx0K 4) K.one_mem ?_
    rw [show (⟨(c⁻¹ * y0 * c) ^ 4, hK (K.pow_mem hx0K 4)⟩ : invE 0) =
        ⟨c⁻¹ * y0 * c, hK hx0K⟩ ^ 4 from Subtype.ext rfl, map_pow, hX0,
      show (⟨(1 : Equiv.Perm (Fin 1782)), hK K.one_mem⟩ : invE 0) = 1 from Subtype.ext rfl,
      map_one]
    calc ((rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y0, hK hy0K⟩ * rho0 ⟨c, hK hcK⟩) ^ 4
        = (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y0, hK hy0K⟩ ^ 4 * rho0 ⟨c, hK hcK⟩ := by
          simpa using conj_pow (a := (rho0 ⟨c, hK hcK⟩)⁻¹) (b := rho0 ⟨y0, hK hy0K⟩) (i := 4)
      _ = 1 := by rw [hY0pow]; group
  have hpow1 : (c⁻¹ * y1 * c) ^ 4 = 1 := by
    refine eq_of_rho0_eq hK hperf hcard (K.pow_mem hx1K 4) K.one_mem ?_
    rw [show (⟨(c⁻¹ * y1 * c) ^ 4, hK (K.pow_mem hx1K 4)⟩ : invE 0) =
        ⟨c⁻¹ * y1 * c, hK hx1K⟩ ^ 4 from Subtype.ext rfl, map_pow, hX1,
      show (⟨(1 : Equiv.Perm (Fin 1782)), hK K.one_mem⟩ : invE 0) = 1 from Subtype.ext rfl,
      map_one]
    calc ((rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y1, hK hy1K⟩ * rho0 ⟨c, hK hcK⟩) ^ 4
        = (rho0 ⟨c, hK hcK⟩)⁻¹ * rho0 ⟨y1, hK hy1K⟩ ^ 4 * rho0 ⟨c, hK hcK⟩ := by
          simpa using conj_pow (a := (rho0 ⟨c, hK hcK⟩)⁻¹) (b := rho0 ⟨y1, hK hy1K⟩) (i := 4)
      _ = 1 := by rw [hY1pow]; group
  have hτx0 : τ * (c⁻¹ * y0 * c) = (c⁻¹ * y0 * c) * τ := hc _ hx0K hcomm0 hpow0
  have hτx1 : τ * (c⁻¹ * y1 * c) = (c⁻¹ * y1 * c) * τ := hc _ hx1K hcomm1 hpow1
  have hcT : c ∈ suzT := suzM_le_suzT (mem_invE_zero.1 hcE).1
  have hcC : c ∈ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) :=
    Subgroup.mem_centralizer_singleton_iff.2 (mem_invE_zero.1 hcE).2
  have hτC : τ ∈ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) :=
    Subgroup.mem_centralizer_singleton_iff.2 hτt
  have hτ'T : c * τ * c⁻¹ ∈ suzT := suzT.mul_mem (suzT.mul_mem hcT hτ) (suzT.inv_mem hcT)
  have hτ'C : c * τ * c⁻¹ ∈ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) :=
    (centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))).mul_mem
      ((centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))).mul_mem hcC hτC)
      ((centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))).inv_mem hcC)
  let Ê : Subgroup (Equiv.Perm (Fin 1782)) :=
    suzT ⊓ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))
  have hτ'mem : c * τ * c⁻¹ ∈ Ê := ⟨hτ'T, hτ'C⟩
  have hy0Ê : y0 ∈ Ê :=
    ⟨suzM_le_suzT (mem_invE_zero.1 hy0E).1,
      Subgroup.mem_centralizer_singleton_iff.2 (mem_invE_zero.1 hy0E).2⟩
  have hy1Ê : y1 ∈ Ê :=
    ⟨suzM_le_suzT (mem_invE_zero.1 hy1E).1,
      Subgroup.mem_centralizer_singleton_iff.2 (mem_invE_zero.1 hy1E).2⟩
  have hρy0 : rhoHat (⟨y0, hy0Ê⟩ : Ê) = suzRootPerm 0 := by
    rw [show rhoHat (⟨y0, hy0Ê⟩ : Ê) = rho0 ⟨y0, hy0E⟩ from rfl, hy0]
  have hρy1 : rhoHat (⟨y1, hy1Ê⟩ : Ê) = suzRootPerm 1 := by
    rw [show rhoHat (⟨y1, hy1Ê⟩ : Ê) = rho0 ⟨y1, hy1E⟩ from rfl, hy1]
  have hτ'y0 : c * τ * c⁻¹ * y0 = y0 * (c * τ * c⁻¹) := by
    calc c * τ * c⁻¹ * y0 = c * (τ * (c⁻¹ * y0 * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y0 * c) * τ) * c⁻¹ := by rw [hτx0]
      _ = y0 * (c * τ * c⁻¹) := by group
  have hτ'y1 : c * τ * c⁻¹ * y1 = y1 * (c * τ * c⁻¹) := by
    calc c * τ * c⁻¹ * y1 = c * (τ * (c⁻¹ * y1 * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y1 * c) * τ) * c⁻¹ := by rw [hτx1]
      _ = y1 * (c * τ * c⁻¹) := by group
  have hcommrho0 : rhoHat (⟨c * τ * c⁻¹, hτ'mem⟩ : Ê) * suzRootPerm 0 =
      suzRootPerm 0 * rhoHat (⟨c * τ * c⁻¹, hτ'mem⟩ : Ê) := by
    rw [← hρy0, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hτ'y0
  have hcommrho1 : rhoHat (⟨c * τ * c⁻¹, hτ'mem⟩ : Ê) * suzRootPerm 1 =
      suzRootPerm 1 * rhoHat (⟨c * τ * c⁻¹, hτ'mem⟩ : Ê) := by
    rw [← hρy1, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hτ'y1
  obtain ⟨hτ'E, hτ'D⟩ := exists_mem_invE_zero_and_rho0_mem_suzD (τ := c * τ * c⁻¹) hτ'mem
    (fun j hj => by
      have h01 : j = 0 ∨ j = 1 := by omega
      rcases h01 with rfl | rfl
      · exact hcommrho0
      · exact hcommrho1)
  have hτE : τ ∈ invE 0 := by
    have h1 : c⁻¹ * (c * τ * c⁻¹) * c ∈ invE 0 :=
      (invE 0).mul_mem ((invE 0).mul_mem ((invE 0).inv_mem hcE) hτ'E) hcE
    rwa [show c⁻¹ * (c * τ * c⁻¹) * c = τ by group] at h1
  have hcD : rho0 ⟨c, hK hcK⟩ ∈ suzD := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem rho0 (Subgroup.mem_subgroupOf.2 hcK)
  have hτD : rho0 ⟨τ, hτE⟩ ∈ suzD := by
    have hτeq : (⟨τ, hτE⟩ : invE 0) =
        (⟨c, hK hcK⟩ : invE 0)⁻¹ * ⟨c * τ * c⁻¹, hτ'E⟩ * ⟨c, hK hcK⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hτeq, map_mul, map_mul, map_inv]
    exact suzD.mul_mem (suzD.mul_mem (suzD.inv_mem hcD) hτ'D) hcD
  exact ⟨hτE, hτD⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
