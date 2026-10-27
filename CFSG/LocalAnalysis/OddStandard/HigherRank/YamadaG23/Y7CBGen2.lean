module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBGen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBGl3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem isElemAbelian_top_iff {Γ : Type} [Group Γ] {X : Subgroup Γ} :
    IsElemAbelian 2 (⊤ : Subgroup X) ↔ IsElemAbelian 2 X := by
  constructor
  · intro h
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact congrArg Subtype.val
        (h.1.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup X)) ⟨b, trivial⟩)
    · intro x hx
      have hx2 := h.2 ⟨x, hx⟩ trivial
      simpa using congrArg (fun z : X => (z : Γ)) hx2
  · intro h
    haveI := h.1
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact Subtype.ext (mul_comm' a.1 b.1)
    · intro x _
      exact Subtype.ext (h.2 (x : Γ) x.2)

private theorem isPGroup_zpowers_of_orderOf_dvd {Γ : Type} [Group Γ] {p N : ℕ} {x : Γ}
    (h : orderOf x ∣ N) (hN : ∃ n, N ∣ p ^ n) : IsPGroup p ↥(zpowers x) := by
  obtain ⟨n, hn⟩ := hN
  exact IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact h.trans hn)

private theorem exists_orderOf_dvd_of_isPGroup_zpowers {Γ : Type} [Group Γ] {p : ℕ} {y : Γ}
    (hy : IsPGroup p ↥(zpowers y)) : ∃ n, orderOf y ∣ p ^ n := by
  obtain ⟨n, hn⟩ := hy.exists_orderOf_dvd_pow (⟨y, Subgroup.mem_zpowers y⟩ : ↥(zpowers y))
  rw [Subgroup.orderOf_mk y (Subgroup.mem_zpowers y)] at hn
  exact ⟨n, hn⟩

private theorem orderOf_pi_dvd (s : Setting3 G L) (x : ↥(y7cX s)) :
    orderOf (y7cPi s x) ∣ orderOf (x : G) := by
  rw [Subgroup.orderOf_coe x]
  exact orderOf_map_dvd (y7cPi s) x

theorem y7c_cent_le_A (c : Ctx7 G L) (hb : B7Std c) :
    ∀ m ∈ y7cM6C c, m * y7cTC c hb = y7cTC c hb * m → m ∈ y7cImg c.s c.s.fr.A := by
  intro m hm hcomm
  obtain ⟨x, hxM6, rfl⟩ := (mem_y7cImg c.s).mp hm
  have hcm : (x : G) * c.s.t * (x : G)⁻¹ * c.s.t⁻¹ ∈ M3 c.s :=
    y7c_comm_mem_M3 c hb x.2 hcomm
  obtain ⟨w, hwM3, hwH⟩ := y7c_coset_cent c hb hcm
  have hwX : w ∈ y7cX c.s := y7c_M3_le_X c.s hwM3
  have hwxM6 : w⁻¹ * (x : G) ∈ M6 c.e :=
    (M6 c.e).mul_mem ((M6 c.e).inv_mem (y7c_M3_le_M6 c hb hwM3)) hxM6
  have hwxA : w⁻¹ * (x : G) ∈ c.s.fr.A := by
    rw [← hb.h71.2.1.2.1]
    exact ⟨hwH, hwxM6⟩
  have hwxX : w⁻¹ * (x : G) ∈ y7cX c.s :=
    (y7cX c.s).mul_mem ((y7cX c.s).inv_mem hwX) x.2
  refine (mem_y7cImg c.s).mpr ⟨⟨w⁻¹ * (x : G), hwxX⟩, hwxA, ?_⟩
  have hw1 : y7cPi c.s ⟨w, hwX⟩ = 1 := (y7cPi_eq_one_iff c.s ⟨w, hwX⟩).mpr hwM3
  have heq : (⟨w⁻¹ * (x : G), hwxX⟩ : ↥(y7cX c.s)) = ⟨w, hwX⟩⁻¹ * x := by ext; rfl
  rw [heq, map_mul, map_inv, hw1, inv_one, one_mul]

theorem y7c_cent_le_B (c : Ctx7 G L) (hb : B7Std c) :
    ∀ m ∈ y7cM7C c, m * y7cTC c hb = y7cTC c hb * m → m ∈ y7cImg c.s c.s.fr.B := by
  intro m hm hcomm
  obtain ⟨x, hxM7, rfl⟩ := (mem_y7cImg c.s).mp hm
  have hcm : (x : G) * c.s.t * (x : G)⁻¹ * c.s.t⁻¹ ∈ M3 c.s :=
    y7c_comm_mem_M3 c hb x.2 hcomm
  obtain ⟨w, hwM3, hwH⟩ := y7c_coset_cent c hb hcm
  have hwX : w ∈ y7cX c.s := y7c_M3_le_X c.s hwM3
  have hwxM7 : w⁻¹ * (x : G) ∈ M7 c.s :=
    (M7 c.s).mul_mem ((M7 c.s).inv_mem (y7b_M3_le_M7 c hwM3)) hxM7
  have hwxB : w⁻¹ * (x : G) ∈ c.s.fr.B := by
    rw [← hb.h75.1.2.1]
    exact ⟨hwH, hwxM7⟩
  have hwxX : w⁻¹ * (x : G) ∈ y7cX c.s :=
    (y7cX c.s).mul_mem ((y7cX c.s).inv_mem hwX) x.2
  refine (mem_y7cImg c.s).mpr ⟨⟨w⁻¹ * (x : G), hwxX⟩, hwxB, ?_⟩
  have hw1 : y7cPi c.s ⟨w, hwX⟩ = 1 := (y7cPi_eq_one_iff c.s ⟨w, hwX⟩).mpr hwM3
  have heq : (⟨w⁻¹ * (x : G), hwxX⟩ : ↥(y7cX c.s)) = ⟨w, hwX⟩⁻¹ * x := by ext; rfl
  rw [heq, map_mul, map_inv, hw1, inv_one, one_mul]

theorem y7c_B_M6_gen (c : Ctx7 G L) (hb : B7Std c) : y7cM6C c ≤ ⁅y7cJC c, y7cM6C c⁆ := by
  obtain ⟨k, hkAF, hk3, hk1⟩ := y7c_exists_yA hb.hH
  have hkF : k ∈ JF c.s := by
    rw [← y7c_NLF_eq_JF hb.hH]
    exact hkAF.2
  have hkX : k ∈ y7cX c.s := y7c_JF_le_X c hb hkF
  let kbar : y7cGam c.s := y7cPi c.s ⟨k, hkX⟩
  have hkbarJ : kbar ∈ y7cJC c := (mem_y7cImg c.s).mpr ⟨⟨k, hkX⟩, hkF, rfl⟩
  have hkbar_ne : kbar ≠ 1 := by
    intro h
    have hkM3 : k ∈ M3 c.s := (y7cPi_eq_one_iff c.s ⟨k, hkX⟩).mp h
    have hkF' : k ∈ c.s.fr.F := by
      rw [← y7c_JF_inf_M3 c.toCtx5 hb.hH]
      exact ⟨hkF, hkM3⟩
    have hdvd2 : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (y54_F_sq hb.hH k hkF')
    obtain ⟨n, hn⟩ := hk3.exists_orderOf_dvd_pow (⟨k, Subgroup.mem_zpowers k⟩ : ↥(zpowers k))
    rw [Subgroup.orderOf_mk k (Subgroup.mem_zpowers k)] at hn
    have h1 : orderOf k = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exact h1
      · rw [h2] at hn
        exact absurd (Nat.prime_two.dvd_of_dvd_pow hn) (by norm_num)
    exact hk1 (orderOf_eq_one_iff.mp h1)
  have hkbar3 : IsPGroup 3 ↥(zpowers kbar) := by
    show IsPGroup 3 ↥(zpowers (y7cPi c.s ⟨k, hkX⟩))
    exact isPGroup_zpowers_of_orderOf_dvd (orderOf_pi_dvd c.s ⟨k, hkX⟩)
      (exists_orderOf_dvd_of_isPGroup_zpowers hk3)
  have hkt : kbar * y7cTC c hb = y7cTC c hb * kbar := by
    have hcomm : k * c.s.t = c.s.t * k := y7c_JF_comm_t c.s k hkF
    have heq : (⟨k, hkX⟩ * ⟨c.s.t, y7c_t_mem_X c hb⟩ : ↥(y7cX c.s)) =
        ⟨c.s.t, y7c_t_mem_X c hb⟩ * ⟨k, hkX⟩ := Subtype.ext hcomm
    show y7cPi c.s ⟨k, hkX⟩ * y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ =
      y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ * y7cPi c.s ⟨k, hkX⟩
    simpa only [map_mul] using congrArg (y7cPi c.s) heq
  have hkW : ∀ m ∈ y7cM6C c, kbar * m * kbar⁻¹ ∈ y7cM6C c := by
    intro m hm
    obtain ⟨y, hyM6, rfl⟩ := (mem_y7cImg c.s).mp hm
    have hkH : k ∈ normIn c.s.H c.s.fr.A :=
      Subgroup.mem_inf.mpr ⟨s3_L_le_H c.s hb.hH.hS hkAF.1.1, hkAF.1.2⟩
    have hkNM6 : k ∈ normalizer (M6 c.e : Set G) :=
      y7b_NHA_le_NM6 c hb.toB6Std.toB5Std hkH
    have hkyM6 : k * (y : G) * k⁻¹ ∈ M6 c.e :=
      (Subgroup.mem_normalizer_iff.mp hkNM6 (y : G)).mp hyM6
    have hyX : (y : G) ∈ y7cX c.s := y7c_M6_le_X c hb hyM6
    have hkyX : k * (y : G) * k⁻¹ ∈ y7cX c.s :=
      (y7cX c.s).mul_mem ((y7cX c.s).mul_mem hkX hyX) ((y7cX c.s).inv_mem hkX)
    refine (mem_y7cImg c.s).mpr ⟨⟨k * (y : G) * k⁻¹, hkyX⟩, hkyM6, ?_⟩
    have heq : (⟨k * (y : G) * k⁻¹, hkyX⟩ : ↥(y7cX c.s)) = ⟨k, hkX⟩ * y * ⟨k, hkX⟩⁻¹ := by
      ext; rfl
    show y7cPi c.s ⟨k * (y : G) * k⁻¹, hkyX⟩ = kbar * y7cPi c.s y * kbar⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have htW : ∀ m ∈ y7cM6C c, y7cTC c hb * m * (y7cTC c hb)⁻¹ ∈ y7cM6C c := by
    intro m hm
    obtain ⟨y, hyM6, rfl⟩ := (mem_y7cImg c.s).mp hm
    have htNM6 : c.s.t ∈ normalizer (M6 c.e : Set G) :=
      y7b_R_le_NM6 c hb.toB6Std.toB5Std (s3_t_mem_R c.s)
    have htyM6 : c.s.t * (y : G) * c.s.t⁻¹ ∈ M6 c.e :=
      (Subgroup.mem_normalizer_iff.mp htNM6 (y : G)).mp hyM6
    have hyX : (y : G) ∈ y7cX c.s := y7c_M6_le_X c hb hyM6
    have htX : c.s.t ∈ y7cX c.s := y7c_t_mem_X c hb
    have htyX : c.s.t * (y : G) * c.s.t⁻¹ ∈ y7cX c.s :=
      (y7cX c.s).mul_mem ((y7cX c.s).mul_mem htX hyX) ((y7cX c.s).inv_mem htX)
    refine (mem_y7cImg c.s).mpr ⟨⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩, htyM6, ?_⟩
    have heq : (⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩ : ↥(y7cX c.s)) =
        ⟨c.s.t, y7c_t_mem_X c hb⟩ * y * ⟨c.s.t, y7c_t_mem_X c hb⟩⁻¹ := by ext; rfl
    show y7cPi c.s ⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩ =
      y7cTC c hb * y7cPi c.s y * (y7cTC c hb)⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have hA_le_J : c.s.fr.A ≤ JF c.s := (s3_A_le_S c.s).trans (y7c_S_le_JF hb.hH)
  have hImgA_le_J : y7cImg c.s c.s.fr.A ≤ y7cJC c := y7cImg_mono c.s hA_le_J
  obtain ⟨e⟩ := y7c_B_J_iso c hb
  have hkA : ∀ a ∈ y7cImg c.s c.s.fr.A, kbar * a * kbar⁻¹ = a → a = 1 := by
    intro a ha hfix
    have haJ : a ∈ y7cJC c := hImgA_le_J ha
    have ha2 : IsPGroup 2 ↥(zpowers a) := by
      obtain ⟨x, hxA, rfl⟩ := (mem_y7cImg c.s).mp ha
      exact isPGroup_zpowers_of_orderOf_dvd (orderOf_pi_dvd c.s x)
        (exists_orderOf_dvd_of_isPGroup_zpowers (s3_isPGroup_zpowers c.s (s3_A_le_S c.s hxA)))
    have hcomm : kbar * a = a * kbar := by
      calc kbar * a = (kbar * a * kbar⁻¹) * kbar := by group
        _ = a * kbar := by rw [hfix]
    exact y7c_cent_three_of_iso e hkbarJ haJ hkbar_ne hkbar3 ha2 hcomm
  have hW : IsElemAbelian 2 (y7cM6C c) := isElemAbelian_top_iff.mp (y7c_B_M6_E c hb).1
  refine y7c_gen_of_fpf hW hkbarJ hkW ?_
  exact y7c_fpf_of_cent_t hW (y7c_B_t_sq c hb) htW (y7c_cent_le_A c hb) hkt hkW hkA

theorem y7c_B_M7_gen (c : Ctx7 G L) (hb : B7Std c) : y7cM7C c ≤ ⁅y7cJC c, y7cM7C c⁆ := by
  obtain ⟨k, hkB, hk3, hk1⟩ := y7c_exists_yB hb.hH
  have hkF : k ∈ JF c.s := by
    rw [← y7c_NLF_eq_JF hb.hH]
    exact hb.hH.hLF.fact18.2.1.2.1 hkB
  have hkX : k ∈ y7cX c.s := y7c_JF_le_X c hb hkF
  let kbar : y7cGam c.s := y7cPi c.s ⟨k, hkX⟩
  have hkbarJ : kbar ∈ y7cJC c := (mem_y7cImg c.s).mpr ⟨⟨k, hkX⟩, hkF, rfl⟩
  have hkbar_ne : kbar ≠ 1 := by
    intro h
    have hkM3 : k ∈ M3 c.s := (y7cPi_eq_one_iff c.s ⟨k, hkX⟩).mp h
    have hkF' : k ∈ c.s.fr.F := by
      rw [← y7c_JF_inf_M3 c.toCtx5 hb.hH]
      exact ⟨hkF, hkM3⟩
    have hdvd2 : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (y54_F_sq hb.hH k hkF')
    obtain ⟨n, hn⟩ := hk3.exists_orderOf_dvd_pow (⟨k, Subgroup.mem_zpowers k⟩ : ↥(zpowers k))
    rw [Subgroup.orderOf_mk k (Subgroup.mem_zpowers k)] at hn
    have h1 : orderOf k = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exact h1
      · rw [h2] at hn
        exact absurd (Nat.prime_two.dvd_of_dvd_pow hn) (by norm_num)
    exact hk1 (orderOf_eq_one_iff.mp h1)
  have hkbar3 : IsPGroup 3 ↥(zpowers kbar) := by
    show IsPGroup 3 ↥(zpowers (y7cPi c.s ⟨k, hkX⟩))
    exact isPGroup_zpowers_of_orderOf_dvd (orderOf_pi_dvd c.s ⟨k, hkX⟩)
      (exists_orderOf_dvd_of_isPGroup_zpowers hk3)
  have hkt : kbar * y7cTC c hb = y7cTC c hb * kbar := by
    have hcomm : k * c.s.t = c.s.t * k := y7c_JF_comm_t c.s k hkF
    have heq : (⟨k, hkX⟩ * ⟨c.s.t, y7c_t_mem_X c hb⟩ : ↥(y7cX c.s)) =
        ⟨c.s.t, y7c_t_mem_X c hb⟩ * ⟨k, hkX⟩ := Subtype.ext hcomm
    show y7cPi c.s ⟨k, hkX⟩ * y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ =
      y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ * y7cPi c.s ⟨k, hkX⟩
    simpa only [map_mul] using congrArg (y7cPi c.s) heq
  have hkW : ∀ m ∈ y7cM7C c, kbar * m * kbar⁻¹ ∈ y7cM7C c := by
    intro m hm
    obtain ⟨y, hyM7, rfl⟩ := (mem_y7cImg c.s).mp hm
    have hkNM7 : k ∈ normalizer (M7 c.s : Set G) := y7c_NLB_le_NM7 hb.hH hkB
    have hkyM7 : k * (y : G) * k⁻¹ ∈ M7 c.s :=
      (Subgroup.mem_normalizer_iff.mp hkNM7 (y : G)).mp hyM7
    have hyX : (y : G) ∈ y7cX c.s := y7c_M7_le_X c hb hyM7
    have hkyX : k * (y : G) * k⁻¹ ∈ y7cX c.s :=
      (y7cX c.s).mul_mem ((y7cX c.s).mul_mem hkX hyX) ((y7cX c.s).inv_mem hkX)
    refine (mem_y7cImg c.s).mpr ⟨⟨k * (y : G) * k⁻¹, hkyX⟩, hkyM7, ?_⟩
    have heq : (⟨k * (y : G) * k⁻¹, hkyX⟩ : ↥(y7cX c.s)) = ⟨k, hkX⟩ * y * ⟨k, hkX⟩⁻¹ := by
      ext; rfl
    show y7cPi c.s ⟨k * (y : G) * k⁻¹, hkyX⟩ = kbar * y7cPi c.s y * kbar⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have htW : ∀ m ∈ y7cM7C c, y7cTC c hb * m * (y7cTC c hb)⁻¹ ∈ y7cM7C c := by
    intro m hm
    obtain ⟨y, hyM7, rfl⟩ := (mem_y7cImg c.s).mp hm
    have htNM7 : c.s.t ∈ normalizer (M7 c.s : Set G) :=
      y7b_R_le_NM7 hb.hH (s3_t_mem_R c.s)
    have htyM7 : c.s.t * (y : G) * c.s.t⁻¹ ∈ M7 c.s :=
      (Subgroup.mem_normalizer_iff.mp htNM7 (y : G)).mp hyM7
    have hyX : (y : G) ∈ y7cX c.s := y7c_M7_le_X c hb hyM7
    have htX : c.s.t ∈ y7cX c.s := y7c_t_mem_X c hb
    have htyX : c.s.t * (y : G) * c.s.t⁻¹ ∈ y7cX c.s :=
      (y7cX c.s).mul_mem ((y7cX c.s).mul_mem htX hyX) ((y7cX c.s).inv_mem htX)
    refine (mem_y7cImg c.s).mpr ⟨⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩, htyM7, ?_⟩
    have heq : (⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩ : ↥(y7cX c.s)) =
        ⟨c.s.t, y7c_t_mem_X c hb⟩ * y * ⟨c.s.t, y7c_t_mem_X c hb⟩⁻¹ := by ext; rfl
    show y7cPi c.s ⟨c.s.t * (y : G) * c.s.t⁻¹, htyX⟩ =
      y7cTC c hb * y7cPi c.s y * (y7cTC c hb)⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have hB_le_J : c.s.fr.B ≤ JF c.s := (s3_B_le_S c.s).trans (y7c_S_le_JF hb.hH)
  have hImgB_le_J : y7cImg c.s c.s.fr.B ≤ y7cJC c := y7cImg_mono c.s hB_le_J
  obtain ⟨e⟩ := y7c_B_J_iso c hb
  have hkA : ∀ a ∈ y7cImg c.s c.s.fr.B, kbar * a * kbar⁻¹ = a → a = 1 := by
    intro a ha hfix
    have haJ : a ∈ y7cJC c := hImgB_le_J ha
    have ha2 : IsPGroup 2 ↥(zpowers a) := by
      obtain ⟨x, hxB, rfl⟩ := (mem_y7cImg c.s).mp ha
      exact isPGroup_zpowers_of_orderOf_dvd (orderOf_pi_dvd c.s x)
        (exists_orderOf_dvd_of_isPGroup_zpowers (s3_isPGroup_zpowers c.s (s3_B_le_S c.s hxB)))
    have hcomm : kbar * a = a * kbar := by
      calc kbar * a = (kbar * a * kbar⁻¹) * kbar := by group
        _ = a * kbar := by rw [hfix]
    exact y7c_cent_three_of_iso e hkbarJ haJ hkbar_ne hkbar3 ha2 hcomm
  have hW : IsElemAbelian 2 (y7cM7C c) := isElemAbelian_top_iff.mp (y7c_B_M7_E c hb).1
  refine y7c_gen_of_fpf hW hkbarJ hkW ?_
  exact y7c_fpf_of_cent_t hW (y7c_B_t_sq c hb) htW (y7c_cent_le_B c hb) hkt hkW hkA

end CFSG.OddStandard.HigherRank.YamadaG23
