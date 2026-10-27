module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QPair
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFC

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

@[expose] def Y (_ : PairCtx X n z s A A' M M') : Subgroup X := A' ⊓ centralizer ({z} : Set X)

@[expose] def OR (h : PairCtx X n z s A A' M M') : Subgroup X := h.R ⊓ oddCoreOf A'

@[expose] noncomputable def Bgrp (h : PairCtx X n z s A A' M M') : Subgroup (Perm (Fin n)) :=
  (h.OR.subgroupOf (centralizer ({z} : Set X))).map h.psi

theorem Y_mem_Cs (h : PairCtx X n z s A A' M M') {y : X} (hy : y ∈ h.Y) :
    y ∈ centralizer ({s} : Set X) := h.hAs hy.1

theorem OR_odd (h : PairCtx X n z s A A' M M') : Odd (Nat.card h.OR) :=
  Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right)

theorem OR_conj (h : PairCtx X n z s A A' M M') {u p : X} (hu : u ∈ centralizer ({z} : Set X))
    (hus : u ∈ centralizer ({s} : Set X)) (hp : p ∈ h.OR) : u * p * u⁻¹ ∈ h.OR :=
  ⟨h.R_conj hu hus hp.1,
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_oddCoreOf_of_mem_normalizer (h.hNs hus)) p).1
      hp.2⟩

theorem mem_Bgrp_iff (h : PairCtx X n z s A A' M M') {b : Perm (Fin n)} :
    b ∈ h.Bgrp ↔ ∃ q ∈ h.OR, M.permX q = b := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, (h.psi_apply q).symm⟩
  · rintro ⟨q, hq, rfl⟩
    have hqz : q ∈ centralizer ({z} : Set X) := (h.mem_R_iff.1 hq.1).1
    exact ⟨⟨q, hqz⟩, hq, h.psi_apply ⟨q, hqz⟩⟩

theorem Bgrp_odd (h : PairCtx X n z s A A' M M') : Odd (Nat.card h.Bgrp) := by
  have h1 : Nat.card h.Bgrp ∣ Nat.card (h.OR.subgroupOf (centralizer ({z} : Set X))) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card (h.OR.subgroupOf (centralizer ({z} : Set X))) = Nat.card h.OR :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun p (hp : p ∈ h.OR) => (h.mem_R_iff.1 hp.1).1)).toEquiv
  rw [h2] at h1
  exact Odd.of_dvd_nat h.OR_odd h1

theorem Bgrp_conj (h : PairCtx X n z s A A' M M') {u : X} (hu : u ∈ centralizer ({z} : Set X))
    (hus : u ∈ centralizer ({s} : Set X)) {b : Perm (Fin n)} (hb : b ∈ h.Bgrp) :
    M.permX u * b * (M.permX u)⁻¹ ∈ h.Bgrp := by
  obtain ⟨q, hq, rfl⟩ := h.mem_Bgrp_iff.1 hb
  refine h.mem_Bgrp_iff.2 ⟨u * q * u⁻¹, h.OR_conj hu hus hq, ?_⟩
  exact M.permX_conj h.hn (h.hNz hu) (h.hNz (h.mem_R_iff.1 hq.1).1)

theorem commutator_mem_Bgrp (h : PairCtx X n z s A A' M M') {y x : X} (hy : y ∈ h.Y)
    (hx : x ∈ h.R) {j : ℕ} (hj : x ^ (2 ^ j) = 1) : ⁅M.permX y, M.permX x⁆ ∈ h.Bgrp := by
  obtain ⟨hyA, hyz⟩ := hy
  have hys : y ∈ centralizer ({s} : Set X) := h.hAs hyA
  obtain ⟨hxz, hxs, hxm⟩ := h.mem_R_iff.1 hx
  have hxN : x ∈ normalizer (h.OR : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact fun hq => h.OR_conj hxz hxs hq
    · intro hq
      have := h.OR_conj (Subgroup.inv_mem _ hxz) (Subgroup.inv_mem _ hxs) hq
      have e : x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q := by group
      rwa [e] at this
  have hcoset : y⁻¹ * (x * y * x⁻¹) ∈ h.OR := by
    have hyinv : y⁻¹ ∈ A' := Subgroup.inv_mem _ hyA
    have h1 : y⁻¹ * (x * y * x⁻¹) ∈ oddCoreOf A' := by
      have := hxm y⁻¹ hyinv
      simpa [commutatorElement_def, mul_assoc] using this
    have h2 : y⁻¹ * (x * y * x⁻¹) ∈ h.R := by
      have e : y⁻¹ * (x * y * x⁻¹) = (y⁻¹ * x * y⁻¹⁻¹) * x⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (h.R_conj (Subgroup.inv_mem _ hyz) (Subgroup.inv_mem _ hys) hx)
        (Subgroup.inv_mem _ hx)
    exact ⟨h2, h1⟩
  obtain ⟨p, hp, hxy⟩ := exists_mul_mem_centralizer_of_fixes_coset h.OR_odd hj hxN hcoset
  have hcD_z : y * p ∈ centralizer ({z} : Set X) :=
    Subgroup.mul_mem _ hyz (h.mem_R_iff.1 hp.1).1
  have hcD_s : y * p ∈ centralizer ({s} : Set X) :=
    Subgroup.mul_mem _ hys (h.mem_R_iff.1 hp.1).2.1
  have hcx : y * p * x = x * (y * p) := Subgroup.mem_centralizer_singleton_iff.1 hxy
  have hcxperm : M.permX (y * p) * M.permX x = M.permX x * M.permX (y * p) := by
    rw [← M.permX_mul h.hn (h.hNz hcD_z) (h.hNz hxz), ← M.permX_mul h.hn (h.hNz hxz)
      (h.hNz hcD_z), hcx]
  have hyz' : y ∈ normalizer (A : Set X) := h.hNz hyz
  have hpN : p ∈ normalizer (A : Set X) := h.hNz (h.mem_R_iff.1 hp.1).1
  have hxN' : x ∈ normalizer (A : Set X) := h.hNz hxz
  set g := M.permX y with hg
  set t := M.permX x with ht
  set b := M.permX p with hb
  set c := M.permX (y * p) with hc
  have hcgb : c = g * b := M.permX_mul h.hn hyz' hpN
  have hgcb : g = c * b⁻¹ := by rw [hcgb]; group
  have hbmem : b ∈ h.Bgrp := h.mem_Bgrp_iff.2 ⟨p, hp, rfl⟩
  have hcomm : Commute c t := hcxperm
  have e1 : ⁅g, t⁆ = c * ⁅b⁻¹, t⁆ * c⁻¹ := by
    calc ⁅g, t⁆ = c * (b⁻¹ * t * b) * (c⁻¹ * t⁻¹) := by
          rw [hgcb]; simp only [commutatorElement_def]; group
      _ = c * (b⁻¹ * t * b) * (t⁻¹ * c⁻¹) := by rw [hcomm.inv_inv.eq]
      _ = c * ⁅b⁻¹, t⁆ * c⁻¹ := by simp only [commutatorElement_def]; group
  rw [e1]
  have h3 : ⁅b⁻¹, t⁆ ∈ h.Bgrp := by
    have e2 : ⁅b⁻¹, t⁆ = b⁻¹ * (t * b * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbmem) (h.Bgrp_conj hxz hxs hbmem)
  exact h.Bgrp_conj hcD_z hcD_s h3

theorem Bgrp_le_Bn [NeZero n] (h : PairCtx X n z s A A' M M')
    (hσ8 : (M.permX s).support.card = 8) (hfcb : FCB n (M.permX s)) : h.Bgrp ≤ Bn n := by
  have hoddB : ∀ b ∈ h.Bgrp, Odd (orderOf b) := fun b hb => by
    have h1 : orderOf (⟨b, hb⟩ : h.Bgrp) ∣ Nat.card h.Bgrp := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Bgrp_odd h1
  intro b hb
  by_contra hbn
  have hbc : b ∈ centralizer ({M.permX s} : Set (Perm (Fin n))) := by
    obtain ⟨q, hq, rfl⟩ := h.mem_Bgrp_iff.1 hb
    have hqs : q ∈ centralizer ({s} : Set X) := (h.mem_R_iff.1 hq.1).2.1
    have hqc : q * s = s * q := Subgroup.mem_centralizer_singleton_iff.1 hqs
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← M.permX_mul h.hn (h.hNz (h.mem_R_iff.1 hq.1).1) (h.hNz h.s_mem_C),
      ← M.permX_mul h.hn (h.hNz h.s_mem_C) (h.hNz (h.mem_R_iff.1 hq.1).1), hqc]
  obtain ⟨g, hg, hev⟩ := hfcb b hbc (hoddB b hb) hbn
  obtain ⟨u, hu, hsu, hug⟩ := h.H0_lift hσ8 g hg
  have hus : u ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
  have h1 : g * b * g⁻¹ ∈ h.Bgrp := by
    rw [← hug]
    exact h.Bgrp_conj (h.hAz hu) hus hb
  have h2 : b * (g * b * g⁻¹) ∈ h.Bgrp := Subgroup.mul_mem _ hb h1
  exact (Nat.not_even_iff_odd.2 (hoddB _ h2)) hev

theorem permX_Y_mem_Gamma [NeZero n] (h : PairCtx X n z s A A' M M')
    (hσ8 : (M.permX s).support.card = 8) (hfcb : FCB n (M.permX s)) {x : X} (hx : x ∈ h.R)
    {j : ℕ} (hj : x ^ (2 ^ j) = 1) {S : Set (Perm (Fin n))}
    (hS : S ⊆ conjSet (H0 (M.permX s)) (M.permX x)) {y : X} (hy : y ∈ h.Y) :
    M.permX y ∈ {g | g ∈ centralizer ({M.permX s} : Set (Perm (Fin n))) ∧
      ∀ t ∈ S, ⁅g, t⁆ ∈ Bn n} := by
  refine ⟨?_, fun t ht => ?_⟩
  · have hys := h.Y_mem_Cs hy
    have hyc : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 hys
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← M.permX_mul h.hn (h.hNz hy.2) (h.hNz h.s_mem_C),
      ← M.permX_mul h.hn (h.hNz h.s_mem_C) (h.hNz hy.2), hyc]
  · obtain ⟨g, hg, rfl⟩ := hS ht
    obtain ⟨u, hu, hsu, hug⟩ := h.H0_lift hσ8 g hg
    have hus : u ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
    have hx' : u * x * u⁻¹ ∈ h.R := h.R_conj (h.hAz hu) hus hx
    have hj' : (u * x * u⁻¹) ^ (2 ^ j) = 1 := by rw [conj_pow, hj]; group
    have h1 := h.commutator_mem_Bgrp hy hx' hj'
    rw [M.permX_conj h.hn (h.hNz (h.hAz hu)) (h.hNz (h.mem_R_iff.1 hx).1), hug] at h1
    exact h.Bgrp_le_Bn hσ8 hfcb h1

end PairCtx

end CFSG.OddStandard.Solomon75
