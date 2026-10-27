module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatFrame
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatPermLem
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatSpec

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

variable {K : Type} [Group K]

theorem exists_lift_mem (C : CoverSetup 11 K) {S : Subgroup K} (hSP : S = (P0 11).comap C.ρ)
    {p : Perm (Fin 11)} (hp : p ∈ P0 11) : ∃ s ∈ S, C.ρ s = p := by
  obtain ⟨s, hs⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1
    (P0_le_alternatingGroup (by norm_num) (by norm_num) hp))
  exact ⟨s, by rw [hSP, Subgroup.mem_comap, hs]; exact hp, hs⟩

theorem rho_mem (C : CoverSetup 11 K) {S : Subgroup K} (hSP : S = (P0 11).comap C.ρ) {s : K}
    (hs : s ∈ S) : C.ρ s ∈ P0 11 := by
  rw [hSP] at hs
  exact hs

theorem center_le_U [Finite K] {S U : Subgroup K} (hF : AhatFrame K S U) : center K ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hF.four.1
  have : Group.IsNilpotent S := hF.sylow.isNilpotent
  have : (U.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hF.U_le).2 hF.U_norm
  have hU1 : U ≠ ⊥ := fun h => by
    have := hF.four.2
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hU1
  have hne : U.subgroupOf S ≠ ⊥ := by
    intro h
    have hm : (⟨u, hF.U_le huU⟩ : S) ∈ U.subgroupOf S := Subgroup.mem_subgroupOf.2 huU
    rw [h, Subgroup.mem_bot] at hm
    have e : u = 1 := congrArg Subtype.val hm
    exact hu1 (Subtype.ext e)
  obtain ⟨⟨w, hwU, hwZ⟩, hw1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hw1' : (w : K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  have hw2 : (w : K) * w = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (A := U) _ (Subgroup.mem_subgroupOf.1 hwU)
  have hwc : (w : K) ∈ center K := by
    refine CFSG.OddStandard.Solomon75.mem_center_of_mem_center_sylow (by norm_num) hF.cover
      (hF.sylow.toSylow (index_odd hF.cover hF.card)) (fun s hs => ?_) hw2
    have := mem_center_iff.1 hwZ ⟨s, hs⟩
    exact congrArg Subtype.val this
  intro c hc
  by_cases hc1 : c = 1
  · rw [hc1]
    exact one_mem _
  · rw [Cov.center_eq (CoverSetup.ofCover hF.cover) hc hwc hc1 hw1']
    exact Subgroup.mem_subgroupOf.1 hwU

theorem rho_U [Finite K] (C : CoverSetup 11 K) {S U : Subgroup K} (hF : AhatFrame K S U)
    {u v : K} (hu : u ∈ U) (hv : v ∈ U) (huz : u ∉ center K) (hvz : v ∉ center K) :
    C.ρ u = C.ρ v := by
  have hker : C.ρ.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker, C.ρ_eq_one_iff]
  have h := card_eq_card_map_mul_card_ker C.ρ U (hker ▸ center_le_U hF)
  rw [hF.four.2, hker, C.center_card] at h
  have h2 : Nat.card (U.map C.ρ) = 2 := by omega
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : U.map C.ρ)).1 h2
  have e1 := hy ⟨C.ρ u, u, hu, rfl⟩ (fun h => huz (C.ρ_eq_one_iff.1 (congrArg Subtype.val h)))
  have e2 := hy ⟨C.ρ v, v, hv, rfl⟩ (fun h => hvz (C.ρ_eq_one_iff.1 (congrArg Subtype.val h)))
  have e := congrArg Subtype.val (e1.trans e2.symm)
  exact e

theorem rho_eq_u0 [Finite K] (C : CoverSetup 11 K) {S U : Subgroup K}
    (hSP : S = (P0 11).comap C.ρ) (hF : AhatFrame K S U) {v : K} (hv : v ∈ U)
    (hvz : v ∉ center K) : C.ρ v = u0 := by
  refine eq_u0_of_comm (C.sign_ρ v) (fun h => hvz (C.ρ_eq_one_iff.1 h)) fun p hp => ?_
  obtain ⟨s, hs, rfl⟩ := exists_lift_mem C hSP hp
  have hsv : s * v * s⁻¹ ∈ U := (mem_normalizer_iff.1 (hF.U_norm hs) v).1 hv
  have hsvz : s * v * s⁻¹ ∉ center K := fun h => hvz (by
    have := (inferInstance : (center K).Normal).conj_mem' _ h s
    simpa [mul_assoc] using this)
  have e := rho_U C hF hsv hv hsvz hvz
  simp only [map_mul, map_inv] at e
  calc C.ρ v * C.ρ s = (C.ρ s * C.ρ v * (C.ρ s)⁻¹) * C.ρ s := by rw [e]
    _ = C.ρ s * C.ρ v := by group

theorem exists_x0 (C : CoverSetup 11 K) : ∃ x₀ : K, C.ρ x₀ = t3 ∧ orderOf x₀ = 3 := by
  obtain ⟨y, hy⟩ := C.exists_ρ_eq (show sign t3 = 1 by decide)
  obtain ⟨c, hc, hyc⟩ := Cov.exists_lift_prime C Nat.prime_three (by norm_num)
    (y := y) (by rw [hy]; decide) (by rw [hy]; decide)
  refine ⟨y * c, ?_, hyc⟩
  rw [map_mul, hy, (C.ρ_eq_one_iff).2 hc, mul_one]

theorem eq_of_pow_three (C : CoverSetup 11 K) {x y : K} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (h : C.ρ x = C.ρ y) : x = y := by
  have hc : x⁻¹ * y ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, h, inv_mul_cancel]
  have hc2 := C.sq_of_mem_center hc
  have e : y = x * (x⁻¹ * y) := by group
  rw [e, (Cov.comm_of_center hc).mul_pow, hx, one_mul, pow_succ, pow_two, hc2, one_mul] at hy
  rw [e, hy, mul_one]

theorem mem_zpowers_x0 (C : CoverSetup 11 K) {x₀ : K} (hx₀ : C.ρ x₀ = t3) (h3 : orderOf x₀ = 3)
    {k : K} (hk : C.ρ k ∈ zpowers t3) (hodd : Odd (orderOf k)) : k ∈ zpowers x₀ := by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hk
  set c := (x₀ ^ j)⁻¹ * k with hcdef
  have hc : c ∈ center K := by
    rw [← C.ρ_eq_one_iff, hcdef, map_mul, map_inv, map_zpow, hx₀, hj, inv_mul_cancel]
  have e : k = x₀ ^ j * c := by rw [hcdef]; group
  have hc2 := C.sq_of_mem_center hc
  obtain ⟨m, hm⟩ := hodd
  have hk1 : k ^ orderOf k = 1 := pow_orderOf_eq_one k
  rw [hm, e, (Cov.comm_of_center (x := x₀ ^ j) hc).mul_pow, pow_succ c (2 * m), pow_mul c 2 m,
    sq, hc2, one_pow, one_mul] at hk1
  have hcx : c ∈ zpowers x₀ := by
    rw [eq_inv_of_mul_eq_one_right hk1]
    exact inv_mem (pow_mem (zpow_mem (mem_zpowers x₀) j) _)
  have h1 : orderOf c ∣ 3 := h3 ▸ orderOf_dvd_of_mem_zpowers hcx
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hc2)
  have h12 : orderOf c ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h12
  rw [e, h12, mul_one]
  exact zpow_mem (mem_zpowers x₀) j

theorem conj_x0 (C : CoverSetup 11 K) {x₀ : K} (hx₀ : C.ρ x₀ = t3) (h3 : orderOf x₀ = 3)
    {c : K} (hc : C.ρ c * u0 = u0 * C.ρ c) : c * x₀ * c⁻¹ = x₀ ∨ c * x₀ * c⁻¹ = x₀⁻¹ := by
  have hx3 : x₀ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one x₀
  have hy3 : (c * x₀ * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  rcases conj_t3_of_comm_u0 hc with h | h
  · left
    refine eq_of_pow_three C hy3 hx3 ?_
    rw [map_mul, map_mul, map_inv, hx₀, h]
  · right
    refine eq_of_pow_three C hy3 (by rw [inv_pow, hx3, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hx₀, h]

theorem mem_normalizer_x0 (C : CoverSetup 11 K) {x₀ : K} (hx₀ : C.ρ x₀ = t3)
    (h3 : orderOf x₀ = 3) {c : K} (hc : C.ρ c * u0 = u0 * C.ρ c) :
    c ∈ normalizer (zpowers x₀ : Set K) := by
  have key : ∀ d : K, C.ρ d * u0 = u0 * C.ρ d → ∀ h ∈ zpowers x₀, d * h * d⁻¹ ∈ zpowers x₀ := by
    intro d hd h hh
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    rcases conj_x0 C hx₀ h3 hd with e | e <;> rw [e]
    · exact zpow_mem (mem_zpowers x₀) j
    · exact zpow_mem (inv_mem (mem_zpowers x₀)) j
  have hc' : C.ρ c⁻¹ * u0 = u0 * C.ρ c⁻¹ := by
    rw [map_inv]
    exact Commute.inv_left hc
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key c hc h, fun hh => ?_⟩
  have := key c⁻¹ hc' _ hh
  simpa [mul_assoc] using this

end CFSG.OddStandard.GH71.AhatB
