module

public import CFSG.ClassicalInvolution.Q3.M11Branch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Open
open scoped MatrixGroups

section SD16

private theorem m11Sd_center_sq : ∀ p : Fin 8 × Fin 2,
    m11SdMap p * m11SdX = m11SdX * m11SdMap p →
      m11SdMap p * m11SdY = m11SdY * m11SdMap p → m11SdMap p * m11SdMap p = 1 := by
  decide +kernel

theorem m11SdS_center_sq {s : ↥NativeSporadic.M11} (hs : s ∈ m11SdS)
    (hc : ∀ t ∈ m11SdS, s * t = t * s) : s * s = 1 := by
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem hs
  have hxS : (⟨m11SdX, m11SdX_mem⟩ : ↥NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyS : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h1 := congrArg Subtype.val (hc _ hxS)
  have h2 := congrArg Subtype.val (hc _ hyS)
  have h3 := m11Sd_center_sq p (by rw [hp]; exact h1) (by rw [hp]; exact h2)
  exact Subtype.ext (by rw [Subgroup.coe_mul, ← hp]; exact h3)

theorem exists_conj_m11SdS {T : Subgroup ↥NativeSporadic.M11} (hT : Nat.card T = 16) :
    ∃ g : ↥NativeSporadic.M11, ∀ t, t ∈ T ↔ ∃ s ∈ m11SdS, g * s * g⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 m11SdS := IsPGroup.of_card (n := 4) (by rw [card_m11SdS]; norm_num)
  have hidx : ¬ 2 ∣ m11SdS.index := by
    have h := Subgroup.card_mul_index m11SdS
    rw [card_m11SdS, card_m11_kernel] at h
    have : m11SdS.index = 495 := by omega
    rw [this]
    norm_num
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 4) (by rw [hT]; norm_num)
  have hTidx : ¬ 2 ∣ T.index := by
    have h := Subgroup.card_mul_index T
    rw [hT, card_m11_kernel] at h
    have : T.index = 495 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 (hS.toSylow hidx)
    (hT2.toSylow hTidx)
  refine ⟨g, fun t => ?_⟩
  have hgT : ((g • hS.toSylow hidx : Sylow 2 ↥NativeSporadic.M11) : Subgroup _) = T := by
    rw [hg]
    rfl
  rw [← hgT, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def, MulAut.conj_apply]

end SD16

section SL23

private theorem sl23_center_sq : ∀ g : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y * g = g * y) →
    g * g = 1 := by
  decide +kernel

end SL23

section Key

theorem classicalInvolutionOddCore_eq_bot_of_m11 {J : Subgroup ↥NativeSporadic.M11}
    {w : ↥NativeSporadic.M11} (hJ : IsClassicalMember3 J w) :
    classicalInvolutionOddCore J = ⊥ := by
  have hc : Nat.card J = 24 := hJ.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨e'⟩ := hJ.nonempty_equiv
  have hq : Nat.card (J ⧸ classicalInvolutionOddCore J) = 24 := by
    rw [Nat.card_congr e'.toEquiv, natCard_sl2Three]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore J)
  rw [hq, hc] at hmul
  apply Subgroup.eq_bot_of_card_eq
  omega

theorem m11_no_sqrt_centralizing {J : Subgroup ↥NativeSporadic.M11} {w k : ↥NativeSporadic.M11}
    (hJ : IsClassicalMember3 J w) (hk : k * k = w) (hkJ : ∀ y ∈ J, k * y = y * k) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2 : w * w = 1 := by
    rw [← sq, ← hJ.orderOf_eq_two]
    exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := hJ.ne_one
  have hc : Nat.card J = 24 := hJ.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨e⟩ := hJ.nonempty_equiv_sl2 (classicalInvolutionOddCore_eq_bot_of_m11 hJ)
  set C : Subgroup ↥NativeSporadic.M11 := Subgroup.centralizer ({k} : Set ↥NativeSporadic.M11)
    with hC
  have hmemC : ∀ y : ↥NativeSporadic.M11, y ∈ C ↔ k * y = y * k := by
    intro y
    rw [hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact h k (Set.mem_singleton k)
    · intro h x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
  have hJC : J ≤ C := fun y hy => (hmemC y).2 (hkJ y hy)
  have hkC : k ∈ C := (hmemC k).2 rfl
  have hCw : C ≤ Subgroup.centralizer ({w} : Set ↥NativeSporadic.M11) := by
    intro y hy
    rw [hmemC] at hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hk]
    calc k * k * y = k * (k * y) := mul_assoc _ _ _
      _ = k * (y * k) := by rw [hy]
      _ = (k * y) * k := (mul_assoc _ _ _).symm
      _ = (y * k) * k := by rw [hy]
      _ = y * (k * k) := mul_assoc _ _ _
  have hCle : Nat.card C ≤ 48 :=
    (Subgroup.card_le_of_le hCw).trans (card_centralizer_le_of_orderOf_eq_two hJ.orderOf_eq_two)
  have hdvd : 24 ∣ Nat.card C := hc ▸ Subgroup.card_dvd_of_le hJC
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hC24 : Nat.card C = 24 ∨ Nat.card C = 48 := by omega
  have hk2 : k ^ 2 = w := by rw [sq]; exact hk
  have hk4 : orderOf k = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, hk2]
      exact hw1
    · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hk2, sq, hw2]
  rcases hC24 with h24 | h48
  ·
    have hJeq : J = C := Subgroup.eq_of_le_of_card_ge hJC (by omega)
    have hkJ' : k ∈ J := hJeq ▸ hkC
    set k' : ↥J := ⟨k, hkJ'⟩ with hk'
    have hcen : ∀ y : SL(2, ZMod 3), y * e k' = e k' * y := by
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hkJ y' y'.2).symm
    have h1 := sl23_center_sq _ hcen
    rw [← map_mul] at h1
    have h2 : k' * k' = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : k * k = 1 := congrArg Subtype.val h2
    exact hw1 (hk ▸ h3)
  ·
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
    have hS16 : Nat.card S = 16 := by
      rw [Sylow.card_eq_multiplicity, h48]
      have : Nat.factorization 48 2 = 4 := by decide +kernel
      rw [this]
      norm_num
    set kC : ↥C := ⟨k, hkC⟩ with hkC'
    have hkcen : ∀ y : ↥C, y * kC = kC * y := fun y =>
      Subtype.ext ((hmemC y).1 y.2).symm
    have hN : (Subgroup.zpowers kC).Normal := ⟨fun n hn x => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc' : Commute x kC := hkcen x
      rw [(hc'.zpow_right m).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m⟩
    have hNp : IsPGroup 2 (Subgroup.zpowers kC) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_zpowers]
      have : orderOf kC = 4 := by
        rw [Subgroup.orderOf_mk, hk4]
        norm_num
      rw [this]
      norm_num
    have hkS : kC ∈ S := hNp.le_sylow_of_normal S (Subgroup.mem_zpowers kC)
    set T : Subgroup ↥NativeSporadic.M11 := (S : Subgroup ↥C).map C.subtype with hT
    have hT16 : Nat.card T = 16 := by
      rw [hT, Subgroup.card_map_of_injective C.subtype_injective]
      exact hS16
    obtain ⟨g, hg⟩ := exists_conj_m11SdS hT16
    have hkT : k ∈ T := ⟨kC, hkS, rfl⟩
    obtain ⟨s, hsS, hs⟩ := (hg k).1 hkT
    have hscen : ∀ t ∈ m11SdS, s * t = t * s := by
      intro t ht
      have hmem : g * t * g⁻¹ ∈ T := (hg _).2 ⟨t, ht, rfl⟩
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp hmem
      have hy' : k * (g * t * g⁻¹) = (g * t * g⁻¹) * k := by
        rw [← hy]
        exact (hmemC (y : ↥NativeSporadic.M11)).1 y.2
      rw [← hs] at hy'
      have hst : g * (s * t) * g⁻¹ = g * (t * s) * g⁻¹ := by
        calc g * (s * t) * g⁻¹ = (g * s * g⁻¹) * (g * t * g⁻¹) := by group
          _ = (g * t * g⁻¹) * (g * s * g⁻¹) := hy'
          _ = g * (t * s) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel hst)
    have hss := m11SdS_center_sq hsS hscen
    have hkk : k * k = 1 := by
      rw [← hs]
      calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = 1 := by rw [hss]; group
    exact hw1 (hk ▸ hkk)

end Key

end CFSG.ClassicalInvolution.Q3
