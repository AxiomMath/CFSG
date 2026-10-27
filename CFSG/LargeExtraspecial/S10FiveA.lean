module

public import CFSG.LargeExtraspecial.S10Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem comm_mod_mul {X : Type*} [Group X] {r₁ r₂ n t : X} (h₁ : r₁ * t = t * r₁)
    (hr₁ : r₁ * n * r₁⁻¹ * n⁻¹ ∈ zpowers t) (hr₂ : r₂ * n * r₂⁻¹ * n⁻¹ ∈ zpowers t) :
    (r₁ * r₂) * n * (r₁ * r₂)⁻¹ * n⁻¹ ∈ zpowers t := by
  have e : (r₁ * r₂) * n * (r₁ * r₂)⁻¹ * n⁻¹ =
      (r₁ * (r₂ * n * r₂⁻¹ * n⁻¹) * r₁⁻¹) * (r₁ * n * r₁⁻¹ * n⁻¹) := by group
  rw [e]
  refine mul_mem ?_ hr₁
  obtain ⟨k, hk⟩ := hr₂
  rw [← hk]
  have hc : Commute r₁ (t ^ k) := (Commute.zpow_right h₁ k)
  rw [hc.eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers t) k

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Hyp10.pairGen (X : Hyp10 S g t) : PairGen S g t :=
  pairGen_of_omegaCase X.H X.hNo X.C X.ht X.ht1 X.hVQ X.hΩ

theorem Hyp10.N0 (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) : Nbar S g t = N0bar S g t :=
  Nbar_eq_N0bar_of_omegaCase hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ X.hΩ

theorem Hyp10.nqHyp (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) : NQHyp S g t := by
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have h1 : S.ρ (1 : S.M) ∈ Rbar S g t := by
    rw [map_one]
    exact one_mem _
  have hb' : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa (((1 : S.M) : G) * g) := by
    simpa using hb
  exact nqHyp_of_pair X.H X.C X.ht X.ht1 X.hVQ h1 hk (X.pairGen 1 k h1 hk hb') (X.N0 hCE)

theorem Abar_inf_Bbar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hk) = 1) :
    (S.Lbar g ⊓ Nbar S g t) ⊓ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) = zpowers t := by
  obtain ⟨hR, -, -⟩ := timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hβ
  refine le_antisymm ?_ ((zpowers_le).mpr ⟨X.t_mem_Abar, mem_Lbar_mul_of_mem_Rbar X.H X.ht hk,
    self_mem_Nbar X.H X.ht⟩)
  rw [← timmesfeld_4_7_c X.H X.C X.ht X.ht1 X.hVQ]
  intro x hx
  refine ⟨mem_centralizer_iff.mpr fun y hy => ?_, hx.1.1⟩
  rw [SetLike.mem_coe, hR] at hy
  have hle : S.Lbar g ⊔ S.Lbar ((k : G) * g) ≤ centralizer ({x} : Set S.O) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · exact mem_centralizer_singleton_iff.mpr (S4.Lbar_comm S X.haQ hz hx.1.1)
    · exact mem_centralizer_singleton_iff.mpr
        (S4.Lbar_comm S (X.H.mul k).conj_mem hz hx.2.1)
  exact mem_centralizer_singleton_iff.mp (hle hy)

theorem mem_Lbar_of_comm_tau_aux (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hxW : x ∈ fixWstar X)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) {n : S.O} (hn : n ∈ Nbar S g t)
    (hc : x * n * x⁻¹ * n⁻¹ ∈ zpowers t) : n ∈ S.Lbar g := by
  have := X.nqHyp hCE
  obtain ⟨-, Y, -, -, -, -, hcomm, -, y, hyY, hyL, hπy⟩ :=
    timmesfeld_10_2_frame hCE X F hxL hxW hπx
  have hnR0 : n ∈ R0 S g t x := Subgroup.mem_sup_left hn
  have hny : y * n * y⁻¹ * n⁻¹ ∈ zpowers t := by
    rw [← hcomm n hnR0 y hyY, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hxt : x * t = t * x := S4.Lbar_comm S X.haQ hxL X.ht
  have hyt : y * t = t * y := S4.Lbar_comm S X.haQ hyL X.ht
  have hA : ∀ a ∈ S.Lbar g ⊓ Nbar S g t, a * n * a⁻¹ * n⁻¹ ∈ zpowers t :=
    fun a ha => NQHyp.comm a ha.2 n hn
  have hxR := Lbar_le_Rbar X.ht hxL
  have hyR := Lbar_le_Rbar X.ht hyL
  have hall : ∀ l ∈ S.Lbar g, l * n * l⁻¹ * n⁻¹ ∈ zpowers t := by
    intro l hl
    have hlR := Lbar_le_Rbar X.ht hl
    have hst := F.π_mem_stabA hl
    rw [mem_stabA, act_E00_iff] at hst
    rcases hst with h | h | h | h
    · exact hA l ⟨hl, (F.ker _).mp h⟩
    · have hm : x⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxL) hl,
          (F.ker ⟨x⁻¹ * l, mul_mem (inv_mem hxR) hlR⟩).mp ?_⟩
        have e : (⟨x⁻¹ * l, mul_mem (inv_mem hxR) hlR⟩ : Rbar S g t) =
            (⟨x, hxR⟩ : Rbar S g t)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, hπx, h, inv_mul_cancel]
      have := comm_mod_mul hxt hc (hA _ hm)
      rwa [mul_inv_cancel_left] at this
    · have hm : y⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyL) hl,
          (F.ker ⟨y⁻¹ * l, mul_mem (inv_mem hyR) hlR⟩).mp ?_⟩
        have e : (⟨y⁻¹ * l, mul_mem (inv_mem hyR) hlR⟩ : Rbar S g t) =
            (⟨y, hyR⟩ : Rbar S g t)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, hπy, h, inv_mul_cancel]
      have := comm_mod_mul hyt hny (hA _ hm)
      rwa [mul_inv_cancel_left] at this
    · have hm : (x * y)⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (mul_mem hxL hyL)) hl,
          (F.ker ⟨(x * y)⁻¹ * l, mul_mem (inv_mem (mul_mem hxR hyR)) hlR⟩).mp ?_⟩
        have e : (⟨(x * y)⁻¹ * l, mul_mem (inv_mem (mul_mem hxR hyR)) hlR⟩ : Rbar S g t) =
            ((⟨x, hxR⟩ : Rbar S g t) * ⟨y, hyR⟩)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, map_mul, hπx, hπy, h, inv_mul_cancel]
      have hxy : (x * y) * t = t * (x * y) := by
        rw [mul_assoc, hyt, ← mul_assoc, hxt, mul_assoc]
      have := comm_mod_mul hxy (comm_mod_mul hxt hc hny) (hA _ hm)
      rwa [mul_inv_cancel_left] at this
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    rw [X.h4]
    norm_num
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have h1R : S.ρ (1 : S.M) ∈ Rbar S g t := by
    rw [map_one]
    exact one_mem _
  have := mem_Lbar_of_comm_mem X.H X.C X.ht X.ht1 X.hVQ X.pairGen (X.N0 hCE) h3 hk hb h1R hn
    (by simpa using hall)
  simpa using this

theorem mem_Lbar_of_comm_tau (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {x : S.O}
    (hxL : x ∈ S.Lbar g) (hxN : x ∉ Nbar S g t) (hxW : x ∈ fixWstar X) {n : S.O}
    (hn : n ∈ Nbar S g t) (hc : x * n * x⁻¹ * n⁻¹ ∈ zpowers t) : n ∈ S.Lbar g := by
  obtain ⟨F⟩ := X.exists_frame
  rcases pi_eq_τ₁_or_τ₂ hCE X F hxL hxN hxW with h1 | h2
  · exact mem_Lbar_of_comm_tau_aux hCE X F hxL hxW h1 hn hc
  · refine mem_Lbar_of_comm_tau_aux hCE X F.swap hxL hxW ?_ hn hc
    rw [F.swap_π, h2, τ₂_swap]

end CFSG.LargeExtraspecial.S10
