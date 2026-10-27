module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78
open CFSG.QuasiDihedralFusion

private theorem card_inf_centralizer_conj {G : Type*} [Group G] {M : Subgroup G} {a b c : G}
    (hc : c ∈ M) (hab : a = c * b * c⁻¹) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(M ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hM : M.map (MulAut.conj c).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)
  have hcent : Subgroup.centralizer ({a} : Set G) =
      (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj c).toMonoidHom := by
    rw [hab]
    exact (map_conj_centralizer_singleton c b).symm
  calc Nat.card ↥(M ⊓ Subgroup.centralizer ({a} : Set G))
      = Nat.card ↥(M ⊓ (Subgroup.centralizer ({b} : Set G)).map
          (MulAut.conj c).toMonoidHom) := by rw [hcent]
    _ = Nat.card ↥((M ⊓ Subgroup.centralizer ({b} : Set G)).map
          (MulAut.conj c).toMonoidHom) := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, hM]
    _ = Nat.card ↥(M ⊓ Subgroup.centralizer ({b} : Set G)) :=
        Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem card_suzM_inf_centralizer_of_mem
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect ↥K) (hcard : Nat.card ↥K = 20160) {x : Equiv.Perm (Fin 1782)}
    (hx : x ∈ K) (hx2 : orderOf x = 2) :
    Nat.card ↥(suzM ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1782)))) = 3317760 := by
  obtain ⟨A, B, Z, l, hA, hB, hAM, hBM, hlM, hA3, hB3, hZclosure, hZ2, hlZ, hMgen,
    hZfix, h0fix, hKcard, ht0M, hZne, ⟨hZE, hZρ⟩, hZnotconj⟩ := suz_row_facts
  have hAodd : Odd (orderOf A) := by
    have hdvd : orderOf A ∣ 3 := orderOf_dvd_of_pow_eq_one hA3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · rw [h]; exact ⟨0, by norm_num⟩
    · rw [h]; exact ⟨1, by norm_num⟩
  have hBodd : Odd (orderOf B) := by
    have hdvd : orderOf B ∣ 3 := orderOf_dvd_of_pow_eq_one hB3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · rw [h]; exact ⟨0, by norm_num⟩
    · rw [h]; exact ⟨1, by norm_num⟩
  have hK' := suz_subgroupOf_data hK hperf hcard
  have hperf' : Group.IsPerfect (K.subgroupOf (invE 0)) := hK'.1
  have hcard' : Nat.card (K.subgroupOf (invE 0)) = Nat.card suzD := hK'.2
  have hAK : A ∈ K := by
    have hA_odd : Odd (orderOf (⟨A, hA⟩ : invE 0)) := by
      rwa [Subgroup.orderOf_mk]
    exact suz_quot2Data.odd_mem hperf' hcard' hA_odd
  have hBK : B ∈ K := by
    have hB_odd : Odd (orderOf (⟨B, hB⟩ : invE 0)) := by
      rwa [Subgroup.orderOf_mk]
    exact suz_quot2Data.odd_mem hperf' hcard' hB_odd
  have hZK : Z ∈ K := by
    have hsub : ({A, B} : Set (Equiv.Perm (Fin 1782))) ⊆ K := by
      intro y hy
      rcases hy with rfl | rfl
      · exact hAK
      · exact hBK
    exact (Subgroup.closure_le K).2 hsub hZclosure
  have hZorder : orderOf Z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hZ2) hZne
  have hZM : Z ∈ suzM := (mem_invE_zero.1 hZE).1
  have hZ_t1 : ∃ m ∈ suzM, Z = m * suzInv 1 * m⁻¹ := by
    rcases CFSG.ComponentClassification.AS81.suzM_conj_cases hZM hZorder with
      ⟨m, hm, hZm⟩ | ⟨m, hm, hZm⟩
    · exact absurd hZm.symm (hZnotconj m hm)
    · exact ⟨m, hm, hZm⟩
  obtain ⟨m, hm, hZm⟩ := hZ_t1
  have hmapK : (K.subgroupOf (invE 0)).map rho0 = suzD :=
    suz_quot2Data.map_eq hperf' hcard'
  have hxE : x ∈ invE 0 := hK hx
  have hxmap_mem : rho0 ⟨x, hxE⟩ ∈ suzD := by
    rw [← hmapK]
    exact ⟨⟨x, hxE⟩, hx, rfl⟩
  have hZmap_mem : rho0 ⟨Z, hZE⟩ ∈ suzD := by
    rw [← hmapK]
    exact ⟨⟨Z, hZE⟩, hZK, rfl⟩
  have hx_sq : x * x = 1 := by
    have h : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    rwa [pow_two] at h
  have hx_img_sq : rho0 ⟨x, hxE⟩ * rho0 ⟨x, hxE⟩ = 1 := by
    have h : (⟨x, hxE⟩ : invE 0) * ⟨x, hxE⟩ = 1 := Subtype.ext hx_sq
    rw [← map_mul, h, map_one]
  have hZ_img_sq : rho0 ⟨Z, hZE⟩ * rho0 ⟨Z, hZE⟩ = 1 := by
    have h : (⟨Z, hZE⟩ : invE 0) * ⟨Z, hZE⟩ = 1 := Subtype.ext hZ2
    rw [← map_mul, h, map_one]
  have hx_img_ne : rho0 ⟨x, hxE⟩ ≠ 1 := by
    intro h
    have hx_one : (⟨x, hxE⟩ : invE 0) = 1 :=
      suz_quot2Data.eq_one_of_map_eq_one hperf' hcard' hx h
    have hx_eq_one : x = 1 := congrArg Subtype.val hx_one
    rw [hx_eq_one, orderOf_one] at hx2
    exact (by norm_num : (1 : ℕ) ≠ 2) hx2
  have hZ_img_ne : rho0 ⟨Z, hZE⟩ ≠ 1 := hZρ
  obtain ⟨c, hcD, hc⟩ := suzD_involutions_conj suz_classCheck
    (rho0 ⟨x, hxE⟩) hxmap_mem (rho0 ⟨Z, hZE⟩) hZmap_mem
    hx_img_sq hZ_img_sq hx_img_ne hZ_img_ne
  obtain ⟨k, hkK, hkρ⟩ := show c ∈ (K.subgroupOf (invE 0)).map rho0 from by
    rw [hmapK]; exact hcD
  have hkK' : (k : Equiv.Perm (Fin 1782)) ∈ K := Subgroup.mem_subgroupOf.1 hkK
  have hKprod : (k * ⟨x, hxE⟩ * k⁻¹) ∈ K.subgroupOf (invE 0) := by
    rw [Subgroup.mem_subgroupOf]
    exact K.mul_mem (K.mul_mem hkK' hx) (K.inv_mem hkK')
  have hZK' : (⟨Z, hZE⟩ : invE 0) ∈ K.subgroupOf (invE 0) := hZK
  have hcalc : rho0 (k * ⟨x, hxE⟩ * k⁻¹) = c * rho0 ⟨x, hxE⟩ * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, hkρ]
  have hprod_rho : rho0 ((k * ⟨x, hxE⟩ * k⁻¹ : invE 0)⁻¹ * ⟨Z, hZE⟩) = 1 := by
    rw [map_mul, map_inv, hcalc, hc, inv_mul_cancel]
  have hprod_mem : ((k * ⟨x, hxE⟩ * k⁻¹ : invE 0)⁻¹ * ⟨Z, hZE⟩) ∈ K.subgroupOf (invE 0) :=
    (K.subgroupOf (invE 0)).mul_mem ((K.subgroupOf (invE 0)).inv_mem hKprod) hZK'
  have hprod_one : ((k * ⟨x, hxE⟩ * k⁻¹ : invE 0)⁻¹ * ⟨Z, hZE⟩) = 1 :=
    suz_quot2Data.eq_one_of_map_eq_one hperf' hcard' hprod_mem hprod_rho
  have hkxk_eq : (k * ⟨x, hxE⟩ * k⁻¹ : invE 0) = ⟨Z, hZE⟩ :=
    inv_mul_eq_one.1 hprod_one
  have hconj_x_Z : (k : Equiv.Perm (Fin 1782)) * x * (k : Equiv.Perm (Fin 1782))⁻¹ = Z := by
    have := congrArg Subtype.val hkxk_eq
    simpa using this
  have hkM : (k : Equiv.Perm (Fin 1782)) ∈ suzM := (mem_invE_zero.1 (hK hkK')).1
  have hx_Z_M : x = (k : Equiv.Perm (Fin 1782))⁻¹ * Z * (k : Equiv.Perm (Fin 1782)) := by
    rw [← hconj_x_Z]
    group
  have hcard_x_Z : Nat.card ↥(suzM ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1782)))) =
      Nat.card ↥(suzM ⊓ centralizer ({Z} : Set (Equiv.Perm (Fin 1782)))) :=
    (card_inf_centralizer_conj hkM (hconj_x_Z.symm)).symm
  have hcard_Z_t1 : Nat.card ↥(suzM ⊓ centralizer ({Z} : Set (Equiv.Perm (Fin 1782)))) =
      Nat.card ↥(suzM ⊓ centralizer ({suzInv 1} : Set (Equiv.Perm (Fin 1782)))) :=
    card_inf_centralizer_conj hm hZm
  rw [hcard_x_Z, hcard_Z_t1]
  rw [inf_comm]
  change Nat.card ↥(centM (suzInv 1)) = 3317760
  rw [← invE_eq_centM (by norm_num : 1 < 4), card_invE (by norm_num : 1 < 4)]
  norm_num [invInnerOrders]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
