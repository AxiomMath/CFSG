module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y3

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

variable {G : Type} [Group G]

theorem conj_zpow_of_inv {z c : G} (hc : z * c * z⁻¹ = c⁻¹) (n : ℤ) :
    z * c ^ n * z⁻¹ = c ^ (-n) := by
  rw [← conj_zpow, hc, inv_zpow, zpow_neg]

theorem exists_conj_comm_of_odd [Finite G] {O : Subgroup G} (hO : Odd (Nat.card O)) {z σ : G}
    (hz : z * z = 1) (hσ : σ * σ = 1) (hzσ : z * σ * z * σ ∈ O) :
    ∃ o ∈ O, (o * σ * o⁻¹) * z = z * (o * σ * o⁻¹) := by
  obtain ⟨k, hk⟩ := hO
  set c := z * σ with hcdef
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hcc : c * c ∈ O := by
    have e : c * c = c * z * σ := by simp only [hcdef, mul_assoc]
    rwa [e]
  have hm : (c * c) ^ (2 * k + 1) = 1 := by
    have h1 : (⟨c * c, hcc⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 : (c * c) ^ Nat.card O = 1 := congrArg Subtype.val h1
    rwa [hk] at h2
  have hc2 : c ^ (2 * (2 * (k : ℤ) + 1)) = 1 := by
    rw [zpow_mul, zpow_two, ← zpow_natCast] at *
    exact_mod_cast hm
  have hzc : z * c * z⁻¹ = c⁻¹ := by
    rw [hcdef, hzi, mul_inv_rev, hσi, hzi]
    calc z * (z * σ) * z = (z * z) * σ * z := by group
      _ = σ * z := by rw [hz, one_mul]
  set N : ℤ := 2 * ((k : ℤ) + 1) ^ 2 with hN
  have hσc : σ = z * c := by rw [hcdef, ← mul_assoc, hz, one_mul]
  refine ⟨c ^ N, ?_, ?_⟩
  · have : c ^ N = (c * c) ^ (((k : ℤ) + 1) ^ 2) := by
      rw [hN, ← zpow_two, ← zpow_mul]
    rw [this]
    exact O.zpow_mem hcc _
  ·
    have hzN : ∀ n : ℤ, z * c ^ n = c ^ (-n) * z := by
      intro n
      have := conj_zpow_of_inv hzc n
      calc z * c ^ n = (z * c ^ n * z⁻¹) * z := by group
        _ = c ^ (-n) * z := by rw [this]
    have key : c ^ N * σ * (c ^ N)⁻¹ = c ^ (2 * N - 1) * z := by
      rw [hσc, ← zpow_neg]
      calc c ^ N * (z * c) * c ^ (-N) = c ^ N * (z * c ^ (1 + -N)) := by
            rw [zpow_add, zpow_one]; group
        _ = c ^ N * (c ^ (-(1 + -N)) * z) := by rw [hzN]
        _ = c ^ (2 * N - 1) * z := by
            rw [← mul_assoc, ← zpow_add]; congr 2; ring
    rw [key]
    have h4 : c ^ (4 * N - 2) = 1 := by
      have : 4 * N - 2 = 2 * (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3) := by rw [hN]; ring
      rw [this, zpow_mul, hc2, one_zpow]
    calc c ^ (2 * N - 1) * z * z = c ^ (2 * N - 1) := by rw [mul_assoc, hz, mul_one]
      _ = c ^ (4 * N - 2) * c ^ (-(2 * N - 1)) := by rw [← zpow_add]; congr 1; ring
      _ = c ^ (-(2 * N - 1)) := by rw [h4, one_mul]
      _ = z * (c ^ (2 * N - 1) * z) := by rw [← mul_assoc z, hzN, mul_assoc, hz, mul_one]

theorem exists_mul_comm_of_odd [Finite G] {O : Subgroup G} (hO : Odd (Nat.card O)) {b y : G}
    (hb : b * b = 1) (hy : y⁻¹ * b * y * b ∈ O) :
    ∃ o ∈ O, (y * o) * b = b * (y * o) := by
  have hu : (y⁻¹ * b * y) * (y⁻¹ * b * y) = 1 := by
    calc (y⁻¹ * b * y) * (y⁻¹ * b * y) = y⁻¹ * (b * b) * y := by group
      _ = 1 := by rw [hb]; group
  obtain ⟨n, hn, hbn⟩ := C25Y.exists_conj_of_involutions_odd hO hu hb hy
  refine ⟨n⁻¹, O.inv_mem hn, ?_⟩
  calc y * n⁻¹ * b = y * n⁻¹ * (n * (y⁻¹ * b * y) * n⁻¹) := by rw [← hbn]
    _ = b * (y * n⁻¹) := by group

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

theorem layerAut_mk_eq_iff (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) (y : ↥Y) :
    C25Y.layerAut Y hb (QuotientGroup.mk y) = QuotientGroup.mk y ↔
      ⁅b, (y : G)⁆ ∈ oddCoreIn Y := by
  rw [C25Y.layerAut_mk, QuotientGroup.eq]
  set w := C25Y.conjOnSub Y hb y with hw
  have hN : (classicalInvolutionOddCore ↥Y).Normal := inferInstance
  have e : ⁅b, (y : G)⁆ = ((w * y⁻¹ : ↥Y) : G) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hw,
      C25Y.coe_conjOnSub]
  have hiff : ((w * y⁻¹ : ↥Y) : G) ∈ oddCoreIn Y ↔ w * y⁻¹ ∈ classicalInvolutionOddCore ↥Y := by
    have h0 : CFSG.Open.componentClassificationOddCore ↥Y = classicalInvolutionOddCore ↥Y := rfl
    unfold oddCoreIn
    rw [h0]
    exact Subgroup.mem_map_iff_mem (x := w * y⁻¹) Y.subtype_injective
  rw [e, hiff]
  constructor
  · intro h
    have h1 : y * w⁻¹ ∈ classicalInvolutionOddCore ↥Y := hN.mem_comm h
    have h2 := (classicalInvolutionOddCore ↥Y).inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  · intro h
    have h2 := (classicalInvolutionOddCore ↥Y).inv_mem h
    rw [mul_inv_rev, inv_inv] at h2
    exact hN.mem_comm h2

theorem layerAut_eq_id_iff [Finite G] (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) :
    (∀ y, C25Y.layerAut Y hb y = y) ↔ b ∈ trivialOnQuot Y := by
  constructor
  · intro h
    refine ⟨mem_normalizer_of_conjSub_eq hb, fun x hx => ?_⟩
    exact (layerAut_mk_eq_iff Y hb ⟨x, hx⟩).mp (h _)
  · intro h y
    induction y using QuotientGroup.induction_on with
    | H y => exact (layerAut_mk_eq_iff Y hb y).mpr (h.2 y y.2)

theorem eq_one_of_isPGroup_of_odd [Finite G] {P O : Subgroup G} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) {x : G} (hxP : x ∈ P) (hxO : x ∈ O) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxP]; exact hk
  have h2 : orderOf x ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨x, hxO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rw [h1] at h2
  have hk0 : k = 0 := by
    by_contra hk0
    have h3 : 2 ∣ Nat.card O := (dvd_pow_self 2 hk0).trans h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h3)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem mk_eq_one_iff (Y : Subgroup G) (y : ↥Y) :
    (QuotientGroup.mk y : ↥Y ⧸ classicalInvolutionOddCore ↥Y) = 1 ↔ (y : G) ∈ oddCoreIn Y := by
  rw [QuotientGroup.eq_one_iff]
  have h0 : CFSG.Open.componentClassificationOddCore ↥Y = classicalInvolutionOddCore ↥Y := rfl
  unfold oddCoreIn
  rw [h0]
  exact (Subgroup.mem_map_iff_mem (x := y) Y.subtype_injective).symm

theorem layerAut_of_mem (Y : Subgroup G) {c : G} (hc : c ∈ Y) (hb : conjSub c Y = Y)
    (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hb e =
      QuotientGroup.mk ⟨c, hc⟩ * e * (QuotientGroup.mk ⟨c, hc⟩)⁻¹ := by
  induction e using QuotientGroup.induction_on with
  | H y =>
    rw [C25Y.layerAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

theorem exists_oddCore_mul_of_normalizer_le [Finite G] {C P : Subgroup G}
    (hP : IsSylow2In P C)
    (hNC : ∀ g ∈ C, (∀ x : G, x ∈ P ↔ g * x * g⁻¹ ∈ P) → ∀ x ∈ P, g * x = x * g) :
    ∀ c ∈ C, ∃ o ∈ oddCoreIn C, ∃ b ∈ P, c = o * b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'map⟩ := IsSylow2Of.exists_sylow (show IsSylow2Of P C from hP)
  have hP' : ∀ y : ↥C, y ∈ (P' : Subgroup ↥C) ↔ (y : G) ∈ P := by
    intro y
    rw [← hP'map]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      rwa [← this]
  have hN : Subgroup.normalizer ((P' : Subgroup ↥C) : Set ↥C) ≤
      Subgroup.centralizer ((P' : Subgroup ↥C) : Set ↥C) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hgn : ∀ x : G, x ∈ P ↔ (g : G) * x * (g : G)⁻¹ ∈ P := by
      intro x
      constructor
      · intro hx
        have hxC : x ∈ C := hP.1 hx
        have := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxC⟩).mp ((hP' _).mpr hx)
        exact (hP' _).mp this
      · intro hx
        have hxC : x ∈ C := by
          have h1 : (g : G) * x * (g : G)⁻¹ ∈ C := hP.1 hx
          have h2 := C.mul_mem (C.mul_mem (C.inv_mem g.2) h1) g.2
          simpa [mul_assoc] using h2
        have h3 : (g * ⟨x, hxC⟩ * g⁻¹ : ↥C) ∈ (P' : Subgroup ↥C) := (hP' _).mpr hx
        exact (hP' _).mp ((Subgroup.mem_normalizer_iff.mp hg ⟨x, hxC⟩).mpr h3)
    have := hNC g g.2 hgn y ((hP' y).mp hy)
    exact (Subtype.ext this).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P' hN
  set M := (MonoidHom.transferSylow P' hN).ker with hM
  have hModd : Odd (Nat.card M) := by
    have hnot : ¬ 2 ∣ Nat.card M := by
      intro h2
      have : 2 ∣ (P' : Subgroup ↥C).index := by
        simpa [hcomp.index_eq_card] using h2
      exact P'.not_dvd_index this
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnot)
  have hMle : M ≤ classicalInvolutionOddCore ↥C :=
    le_sSup ⟨inferInstance, hModd⟩
  intro c hc
  obtain ⟨⟨⟨m, hm⟩, ⟨b, hb⟩⟩, hmb, -⟩ := hcomp.existsUnique ⟨c, hc⟩
  refine ⟨(m : G), ⟨m, hMle hm, rfl⟩, (b : G), (hP' b).mp hb, ?_⟩
  exact (congrArg Subtype.val hmb).symm

end CFSG.ClassicalInvolution.Asc77.C5O
