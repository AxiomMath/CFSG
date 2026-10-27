module

public import CFSG.LargeExtraspecial.S13Hyp
public import CFSG.LargeExtraspecial.S7SevenMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem Nbar_eq_zpowers_of_N0bar' (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hN0 : Nbar S g t = N0bar S g t) (hLN : S.Lbar g ⊓ Nbar S g t = zpowers t) :
    Nbar S g t = zpowers t := by
  have haQ := H.conj_mem
  refine le_antisymm ?_ (zpowers_le.mpr (S6.self_mem_Nbar H ht))
  rw [hN0]
  refine iSup₂_le fun k hk => ?_
  rintro y ⟨hyL, hyN⟩
  rw [Lbar_mul S k g] at hyL
  obtain ⟨x, hx, rfl⟩ := hyL
  have hc : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar haQ hk
  have hc' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
    rw [map_inv]
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hc]
      _ = t * (S.ρ k)⁻¹ := by group
  have hy : (MulAut.conj (S.ρ k)).toMonoidHom x = S.ρ k * x * (S.ρ k)⁻¹ := rfl
  rw [hy] at hyN ⊢
  have hxN : x ∈ Nbar S g t := by
    have h1 := conj_mem_Nbar haQ hc' hyN
    rwa [map_inv, inv_inv, show (S.ρ k)⁻¹ * (S.ρ k * x * (S.ρ k)⁻¹) * S.ρ k = x by group]
      at h1
  have hxZ : x ∈ zpowers t := by
    rw [← hLN]
    exact ⟨hx, hxN⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxZ
  refine mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [(Commute.zpow_right (show Commute (S.ρ k) t from hc) i).eq, mul_inv_cancel_right]

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem finrank_commSpace_of_not_mem {τ : S.O} (hτ : τ ∈ S.Lbar g) (hτE : τ ∉ Ebar S g K) :
    finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = S.width := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  have hk3 := Y.pow_three hk
  have hkk3 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hk3]; rfl
  have hfix : ∀ v, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 :=
    fun v hv => fix_eq_zero Y.card_K Y.fpf hk hk1 v hv
  have htt : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    rw [← Subgroup.coe_mul, mul_self_of_mem_Lbar S Y.haQ hτ]; rfl
  have hinv : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ * (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have e := Y.inv_of_not_mem hτ hτE k hk
    have e2 : τ * k = k⁻¹ * τ := by rw [← e]; group
    rw [← Subgroup.coe_mul, e2, Subgroup.coe_mul, Subgroup.coe_inv]
  have hdim := two_mul_finrank_commSpace_of_inverts hkk3 hfix htt hinv
  rw [S.finrank_Qt_eq_two_mul_width] at hdim
  omega

theorem finrank_Vt_of_not_mem {τ : S.O} (hτ : τ ∈ S.Lbar g) (hτE : τ ∉ Ebar S g K)
    (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g) : finrank (ZMod 2) (Vt S g τ) = S.width := by
  rw [← (commSpace_t_eq Y.H Y.C hτ hτ1 hVQ).1]
  exact Y.finrank_commSpace_of_not_mem hτ hτE

end Hyp13

theorem timmesfeld_13_4 (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) :
    Bridge.TimmesfeldAlt3 S.width S.Mbar ∨
      ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K → Rbar S g τ = S.Lbar g ∨ LinCase S g hτ := by
  by_cases hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K →
      Rbar S g τ = S.Lbar g ∨ LinCase S g hτ
  · exact Or.inr hii
  left
  push Not at hii
  obtain ⟨τ, hτ, hτE, hR, hL⟩ := hii
  have hτ1 : τ ≠ 1 := fun h => hτE (h ▸ one_mem _)
  have h7 := Y.seven_le
  rcases timmesfeld_4_5 Y.H Y.hNo Y.C hτ hτ1 with hRL | hLin | ⟨hVQ, hcase⟩
  · exact absurd hRL hR
  · exact absurd hLin hL
  have hdim := Y.finrank_Vt_of_not_mem hτ hτE hτ1 hVQ
  have h2 := card_Lbar_eq_mul Y.haQ hτ (t := τ)
  rw [Y.C.card_Lbar] at h2
  have hτA : τ ∈ S.Lbar g ⊓ Nbar S g τ := ⟨hτ, S6.self_mem_Nbar Y.H hτ⟩
  have hτ2 : Nat.card (zpowers τ) = 2 := S7.card_zpowers_eq_two Y.H hτ hτ1
  rcases hcase with hSp | hA | hΩ | hP
  · exfalso
    have hc := card_Lbar_inf_Nbar_sp Y.H Y.C hτ hτ1 hVQ hSp
    rw [hdim, Nat.sub_self, pow_zero] at hc
    have hb := Subgroup.eq_bot_of_card_eq _ hc
    have hm : τ ∈ (⊥ : Subgroup S.O) := hb ▸ hτA
    exact hτ1 ((mem_bot).mp hm)
  · rw [hA.finrank_eq] at hdim
    omega
  · have hc := S7.card_LmodN_of_omegaCase Y.H Y.C hτ hτ1 hΩ
    rw [hdim] at hc
    rw [hc] at h2
    have hLN : S.Lbar g ⊓ Nbar S g τ = zpowers τ := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hτA) ?_
      rw [hτ2]
      have e : 2 ^ (S.width - 1) = 2 ^ (S.width - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      have hpos : 0 < 2 ^ (S.width - 2) := by positivity
      rw [e] at h2
      have := Nat.eq_of_mul_eq_mul_left hpos h2
      omega
    have hN := Nbar_eq_zpowers_of_N0bar' Y.H hτ
      (S6.Nbar_eq_N0bar_of_omegaCase hCE Y.H Y.hNo Y.C hτ hτ1 hVQ hΩ) hLN
    exact S7.timmesfeldAlt3 hCE Y.H Y.hNo Y.C hτ hτ1 hR hN (by omega)
  · rw [hP.finrank_eq] at hdim
    omega

end CFSG.LargeExtraspecial.S13
