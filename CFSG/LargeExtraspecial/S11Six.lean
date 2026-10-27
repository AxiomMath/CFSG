module

public import CFSG.LargeExtraspecial.S11SixB
public import CFSG.LargeExtraspecial.S11Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem card_le_two_mul_card_inf {H : Type*} [Group H] [Finite H] {X Y N : Subgroup H}
    (hX : X ≤ N) (hY : Y ≤ N) (hN : Nat.card N ≤ 2 * Nat.card Y) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ Y : Subgroup H) := by
  have h1 := Subgroup.relIndex_mul_card Y N
  rw [inf_eq_left.mpr hY] at h1
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have h2 : Y.relIndex N ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 * Nat.card Y ≤ Y.relIndex N * Nat.card Y := Nat.mul_le_mul_right _ h
    omega
  have hne : Y.relIndex N ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := N)).ne h1
  have h3 := Subgroup.relIndex_le_of_le_right hX hne
  have h4 := Subgroup.relIndex_mul_card Y X
  rw [inf_comm] at h4
  calc Nat.card X = Y.relIndex X * Nat.card (X ⊓ Y : Subgroup H) := h4.symm
    _ ≤ 2 * Nat.card (X ⊓ Y : Subgroup H) := Nat.mul_le_mul_right _ (h3.trans h2)

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.base_change {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) : Conf S k t τ u :=
  ⟨(K.base_of_mem hk).2, K.ne_one, K.linCase_of hy hk (K.base_of_mem hk).2, K.rho_eq, K.conj_eq,
    hk.2⟩

theorem Conf.card_Lbar_inf_le (hCE : CentralExtInput.{u_G}) {k' : G}
    (hk' : k' * S.z * k'⁻¹ = (τ : G) * S.z) {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u)
    (hkb : S.cl (k * S.z * k⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    Nat.card (S.Lbar g ⊓ S.Lbar k : Subgroup S.O) ≤ 4 := by
  have Kb := K.base_change hy hk
  have hyb := hy.of_conj hk.1 (K.base_of_mem hk).1
  set C := S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) with hC
  set A := S.clSub (S.QG ⊓ S.Qa g ⊓ centralizer ({(τ : G)} : Set G)) with hA
  set B := S.clSub (S.QG ⊓ S.Qa k ⊓ centralizer ({(τ : G)} : Set G)) with hB
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set X := S.Lbar g ⊓ S.Lbar k with hX
  have h1 : finrank (ZMod 2) A + 1 = S.width := K.finrank_clSub_inf_centralizer hy
  have h2 : finrank (ZMod 2) B + 1 = S.width := Kb.finrank_clSub_inf_centralizer hyb
  have h3 : finrank (ZMod 2) C = S.width := K.finrank_clSub_centralizer hy hCE hk'
  have hAC : A ≤ C := S.clSub_mono fun x hx => ⟨hx.1.1, hx.2⟩
  have hBC : B ≤ C := S.clSub_mono fun x hx => ⟨hx.1.1, hx.2⟩
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h5 : finrank (ZMod 2) ↥(A ⊔ B) ≤ finrank (ZMod 2) C :=
    Submodule.finrank_mono (sup_le hAC hBC)
  have hfix : A ⊓ B ≤ P ⊓ fixSub S X := by
    intro v hv
    have hvP : v ∈ P := S.clSub_mono inf_le_left hv.1
    have hvPb : v ∈ S.clSub (S.QG ⊓ S.Qa k) := S.clSub_mono inf_le_left hv.2
    refine ⟨hvP, fun x hx => ?_⟩
    have ha := Lbar_apply_sub_mem_span' hy.hyp4.conj_mem hvP hx.1
    have hb := Lbar_apply_sub_mem_span' hk.1 hvPb hx.2
    rcases mem_span_cl_iff.mp hb with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (h0 ▸ ha) hkb
  have h6 := Submodule.finrank_mono hfix
  have h7 : Nat.card X * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S X) = 2 ^ S.width :=
    card_mul_two_pow_finrank_fix hy.hyp4 hy.cons inf_le_left
  have hw := hy.hyp4.two_lt_width
  have h8 : S.width - 2 ≤ finrank (ZMod 2) ↥(P ⊓ fixSub S X) := by omega
  have e : 2 ^ S.width = 4 * 2 ^ (S.width - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have h9 : Nat.card X * 2 ^ (S.width - 2) ≤ 4 * 2 ^ (S.width - 2) := by
    calc Nat.card X * 2 ^ (S.width - 2) ≤ Nat.card X * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S X) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos h8)
      _ = 4 * 2 ^ (S.width - 2) := by rw [h7, e]
  exact Nat.le_of_mul_le_mul_right h9 (by positivity)

theorem Conf.timmesfeld_11_6 (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width) {x : G}
    (hx : x * τ * x⁻¹ = (τ : G) * S.z) :
    finrank (ZMod 2) (Vt S g t) = 3 ∧ S.width = 6 := by
  have hk : (x * u) * S.z * (x * u)⁻¹ = (τ : G) * S.z := by
    rw [← hx, K.conj_eq]
    group
  obtain ⟨kb, hkb, hkbs⟩ := K.exists_base_ne hy
  obtain ⟨hkbz, -⟩ := K.base_of_mem hkb
  have Kb := K.base_change hy hkb
  have hyb := hy.of_conj hkb.1 hkbz
  have h1 := Kb.card_Nbar_le hyb hCE hk
  rw [hy.Nbar_eq hkb.1 hkbz t] at h1
  have h2 := card_le_two_mul_card_inf (inf_le_right : S.Lbar g ⊓ Nbar S g t ≤ Nbar S g t)
    (inf_le_right : S.Lbar kb ⊓ Nbar S g t ≤ Nbar S g t) h1
  have h3 : Nat.card ((S.Lbar g ⊓ Nbar S g t) ⊓ (S.Lbar kb ⊓ Nbar S g t) : Subgroup S.O) ≤ 4 :=
    (Subgroup.card_le_of_le (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left))).trans (K.card_Lbar_inf_le hy hCE hk hkb hkbs)
  have h4 : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤ 2 ^ 3 := by
    show _ ≤ 8
    omega
  have h5 := card_Lbar_inf_Nbar hy.hyp4 hy.cons K.lin
  have h6 : 2 ^ (S.width - 1) ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 1 + 3) := by
    rw [← h5, pow_add, mul_comm (2 ^ _) (2 ^ 3)]
    exact Nat.mul_le_mul_right _ h4
  have h7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h6
  have h8 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
  have h9 := Submodule.finrank_mono (Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin)
  have h10 := K.finrank_commSpace_le
  have h11 := K.lin.two_le_finrank
  omega

theorem Conf.timmesfeld_11_6_of_mem_QG (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width) {q : G}
    (hq : q ∈ S.QG) : q * τ * q⁻¹ ≠ (τ : G) * S.z := by
  intro hqτ
  have hk : (q * u) * S.z * (q * u)⁻¹ = (τ : G) * S.z := by
    rw [← hqτ, K.conj_eq]
    group
  obtain ⟨hm, hw⟩ := K.timmesfeld_11_6 hy hCE hn hqτ
  have h1 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
  have h2 := Submodule.finrank_mono (Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin)
  have h3 := K.finrank_commSpace_le
  have h4 := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h5 := S.finrank_Qt_eq_two_mul_width
  have h6 := K.finrank_clSub_centralizer hy hCE hk
  have heq : S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) =
      fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Submodule.eq_of_le_of_finrank_eq K.clSub_centralizer_le_fixSpace (by omega)
  have e1 : q * τ * q⁻¹ * (τ : G)⁻¹ = S.z := by
    rw [hqτ, S.z_comm τ.2, mul_inv_cancel_right]
  have e2 : (τ : G) * q * (τ : G)⁻¹ * q⁻¹ = S.z := by
    have := congrArg (fun v => v⁻¹) e1
    simp only [mul_inv_rev, inv_inv, S.z_inv] at this
    rw [← this]
    group
  have e3 : (τ : G) * q * (τ : G)⁻¹ = S.z * q := by
    calc (τ : G) * q * (τ : G)⁻¹ = (τ : G) * q * (τ : G)⁻¹ * q⁻¹ * q := by group
      _ = S.z * q := by rw [e2]
  have hfix : S.cl q ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [mem_fixSpace, ← K.rho_eq, S.ρ_cl τ hq, e3, S.cl_mul S.z_mem_QG hq, S.cl_z, zero_add]
  rw [← heq] at hfix
  have hqX : q ∈ S.QG ⊓ centralizer ({(τ : G)} : Set G) := by
    rw [← S.clPre_clSub (inf_le_left : S.QG ⊓ centralizer ({(τ : G)} : Set G) ≤ S.QG)
      (mem_inf.mpr ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm τ.2).symm⟩)]
    exact S.mem_clPre.mpr ⟨hq, hfix⟩
  have h7 : (τ : G) = (τ : G) * S.z := by
    rw [← hqτ, mem_centralizer_singleton_iff.mp hqX.2, mul_inv_cancel_right]
  exact S.z_ne_one (by simpa using h7)

end CFSG.LargeExtraspecial.S11
