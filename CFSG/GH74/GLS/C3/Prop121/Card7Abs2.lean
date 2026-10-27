module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs1
public import CFSG.GH74.GLS.C3.Prop121.Card7Gen2

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace Ctx

variable {G : Type} [Group G] (C : Ctx G)

structure Y1 where
  h1 : G
  hy1x : h1 * C.y0 * h1⁻¹ ∈ centralizer ({C.x} : Set G)
  b : F7
  hb : C.ι ⟨h1 * C.y0 * h1⁻¹, hy1x⟩ = b
  hbf : b * f0 = f0 * b
  hbY : YF b
  hb96 : ccard F7 f0 b = 96

variable {C}

@[expose, reducible] def Y1.y1 (Y : C.Y1) : G := Y.h1 * C.y0 * Y.h1⁻¹

theorem Y1.orderOf_y1 (Y : C.Y1) : orderOf Y.y1 = 2 := by
  unfold Y1.y1
  rw [show Y.h1 * C.y0 * Y.h1⁻¹ = MulAut.conj Y.h1 C.y0 from rfl, MulEquiv.orderOf_eq]
  exact C.hy0

theorem Y1.y1_comm_s (Y : C.Y1) : Y.y1 * C.s = C.s * Y.y1 := by
  have h1 : (⟨Y.y1, Y.hy1x⟩ : ↥(centralizer ({C.x} : Set G))) * ⟨C.s, C.hs⟩ =
      ⟨C.s, C.hs⟩ * ⟨Y.y1, Y.hy1x⟩ := by
    apply C.ι.injective
    rw [map_mul, map_mul, C.hsF]
    have hb : C.ι ⟨Y.y1, Y.hy1x⟩ = Y.b := Y.hb
    rw [hb]
    exact Y.hbf
  exact congrArg Subtype.val h1

theorem Y1.not_isConj_x (Y : C.Y1) : ¬ IsConj C.x Y.y1 := by
  intro h
  have hord : orderOf (⟨Y.y1, Y.hy1x⟩ : ↥(centralizer ({C.x} : Set G))) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact Y.orderOf_y1
  have := (C.lab ⟨Y.y1, Y.hy1x⟩ hord).1 (isConj_comm.1 h)
  have hb : C.ι ⟨Y.y1, Y.hy1x⟩ = Y.b := Y.hb
  rw [hb] at this
  have h8 := Y.hbY.2
  omega

theorem Y1.isConj_y0 (Y : C.Y1) : IsConj C.y0 Y.y1 := isConj_iff.2 ⟨Y.h1, rfl⟩

theorem Y1.mem_cent_y1 (Y : C.Y1) : C.s ∈ centralizer ({Y.y1} : Set G) :=
  mem_centralizer_singleton_iff.2 Y.y1_comm_s.symm

theorem exists_Y1 (hF : FFacts) : Nonempty C.Y1 := by
  have hex : ∃ b : F7, b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 96 := by
    by_contra hne
    have h0 : Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 96} = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨b, hb⟩ => hne ⟨b, hb⟩⟩
    rw [hF.N96] at h0
    omega
  obtain ⟨b, hbf, hbY, hb96⟩ := hex
  set y' : ↥(centralizer ({C.x} : Set G)) := C.ι.symm b with hy'
  have hy'2 : orderOf y' = 2 := by
    rw [hy', MulEquiv.orderOf_eq]
    exact isInv_iff_orderOf.1 hbY.1
  have hy'G : orderOf (y' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy'2
  have hnc : ¬ IsConj (y' : G) C.x := by
    intro hc
    have := (C.lab y' hy'2).1 hc
    have hb' : C.ι y' = b := by rw [hy']; exact C.ι.apply_symm_apply b
    rw [hb'] at this
    have h8 := hbY.2
    omega
  have hcj : IsConj C.y0 (y' : G) := by
    rcases C.hcl (y' : G) hy'G with h | h
    · exact absurd (isConj_comm.1 h) hnc
    · exact h
  obtain ⟨h1, hh1⟩ := isConj_iff.1 hcj
  refine ⟨⟨h1, ?_, b, ?_, hbf, hbY, hb96⟩⟩
  · rw [hh1]; exact y'.2
  · have : (⟨h1 * C.y0 * h1⁻¹, by rw [hh1]; exact y'.2⟩ : ↥(centralizer ({C.x} : Set G))) = y' :=
      Subtype.ext hh1
    rw [this, hy']
    exact C.ι.apply_symm_apply b

theorem Y1.cc3_x_s_y1 (Y : C.Y1) : cc3 C.x C.s Y.y1 = 96 := by
  have h := cc3_eq_ccard (a := C.x) (u := C.s) (v := Y.y1) C.ι C.hs Y.hy1x
  rw [h, C.hsF]
  have hb : C.ι ⟨Y.y1, Y.hy1x⟩ = Y.b := Y.hb
  rw [hb]
  exact Y.hb96

theorem Y1.le_cc3_y1 [Finite G] (Y : C.Y1) : 96 ≤ cc3 Y.y1 C.s C.s := by
  rw [← Y.cc3_x_s_y1]
  unfold cc3
  refine Nat.card_le_card_of_injective
    (fun c => ⟨c.1, c.2.2.2, c.2.2.1, c.2.2.1⟩) ?_
  intro c d h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

theorem Y1.tau_cases [Finite G] (hH : HFacts) (Y : C.Y1) :
    ((C.Ψh Y.h1) ⟨C.s, Y.mem_cent_y1⟩ = tau1 ∨ (C.Ψh Y.h1) ⟨C.s, Y.mem_cent_y1⟩ = tau1⁻¹) ∧
      cc3 Y.y1 C.s C.s = 576 := by
  set τ := (C.Ψh Y.h1) ⟨C.s, Y.mem_cent_y1⟩ with hτ
  have h3 : τ ^ 3 = 1 := by
    have : (⟨C.s, Y.mem_cent_y1⟩ : ↥(centralizer ({Y.y1} : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using C.s_pow_three)
    rw [hτ, ← map_pow, this, map_one]
  have h1 : τ ≠ 1 := by
    intro h
    have h' : (⟨C.s, Y.mem_cent_y1⟩ : ↥(centralizer ({Y.y1} : Set G))) = 1 :=
      (C.Ψh Y.h1).injective (by rw [← hτ, h, map_one])
    exact C.s_ne_one (congrArg Subtype.val h')
  have hc : cc3 Y.y1 C.s C.s = ccard H11 τ τ :=
    cc3_eq_ccard (a := Y.y1) (u := C.s) (v := C.s) (C.Ψh Y.h1) Y.mem_cent_y1 Y.mem_cent_y1
  have hge := Y.le_cc3_y1
  rcases hH.ord3 τ h3 h1 with ⟨hτ1, h576⟩ | hle
  · exact ⟨hτ1, by rw [hc]; exact h576⟩
  · exfalso
    rw [hc] at hge
    omega

theorem exists_conj_y [Finite G] (hH : HFacts) (Y : C.Y1) (h : G)
    (hsw : C.s ∈ centralizer ({h * Y.y1 * h⁻¹} : Set G))
    (hτ : (C.Ψh Y.h1) (conjCentEquiv Y.y1 h ⟨C.s, hsw⟩) = tau1 ∨
      (C.Ψh Y.h1) (conjCentEquiv Y.y1 h ⟨C.s, hsw⟩) = tau1⁻¹) :
    ∃ c : G, c * C.s = C.s * c ∧ c * Y.y1 * c⁻¹ = h * Y.y1 * h⁻¹ := by
  obtain ⟨hτ1, -⟩ := Y.tau_cases hH
  obtain ⟨b, hb⟩ := hH.inv_tau1
  have hb' : b⁻¹ * tau1⁻¹ * b = tau1 := by
    calc b⁻¹ * tau1⁻¹ * b = b⁻¹ * (b * tau1 * b⁻¹) * b := by rw [hb]
      _ = tau1 := by group
  have hk : ∃ k : H11, k * (C.Ψh Y.h1) (conjCentEquiv Y.y1 h ⟨C.s, hsw⟩) * k⁻¹ =
      (C.Ψh Y.h1) ⟨C.s, Y.mem_cent_y1⟩ := by
    rcases hτ with h1 | h1 <;> rcases hτ1 with h2 | h2 <;> rw [h1, h2]
    · exact ⟨1, by simp⟩
    · exact ⟨b, hb⟩
    · exact ⟨b⁻¹, by simpa using hb'⟩
    · exact ⟨1, by simp⟩
  obtain ⟨k, hk⟩ := hk
  exact exists_cent_conj (e := C.Ψh Y.h1) (a := Y.y1) Y.mem_cent_y1 hsw k hk

theorem cc3_cases [Finite G] (hF : FFacts) (hH : HFacts) (w : G) (hw : orderOf w = 2)
    (hws : w * C.s = C.s * w) :
    cc3 w C.s C.s = 288 ∨ cc3 w C.s C.s = 72 ∨ cc3 w C.s C.s = 576 ∨
      (0 < cc3 w C.s C.s ∧ cc3 w C.s C.s ≤ 36) := by
  rcases C.hcl w hw with hx | hy
  · obtain ⟨h, rfl⟩ := isConj_iff.1 hx
    have hsw : C.s ∈ centralizer ({h * C.x * h⁻¹} : Set G) :=
      mem_centralizer_singleton_iff.2 hws.symm
    set f' := C.ιh h ⟨C.s, hsw⟩ with hf'
    have hc : cc3 (h * C.x * h⁻¹) C.s C.s = ccard F7 f' f' :=
      cc3_eq_ccard (a := h * C.x * h⁻¹) (u := C.s) (v := C.s) (C.ιh h) hsw hsw
    have h3 : f' ^ 3 = 1 := by
      have : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using C.s_pow_three)
      rw [hf', ← map_pow, this, map_one]
    have h1 : f' ≠ 1 := by
      intro h'
      have h'' : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) = 1 :=
        (C.ιh h).injective (by rw [← hf', h', map_one])
      exact C.s_ne_one (congrArg Subtype.val h'')
    rcases hF.ord3 f' h3 h1 with hty | hty
    · obtain ⟨k, hk⟩ := hF.conj3 f' hty
      have : ccard F7 f' f' = 288 := by
        rw [← hF.card_f0, ← hk, ccard_conj]
      exact Or.inl (by rw [hc]; exact this)
    · exact Or.inr (Or.inl (by rw [hc]; exact hF.card_ty33 f' hty))
  · obtain ⟨h, rfl⟩ := isConj_iff.1 hy
    have hsw : C.s ∈ centralizer ({h * C.y0 * h⁻¹} : Set G) :=
      mem_centralizer_singleton_iff.2 hws.symm
    set τ := C.Ψh h ⟨C.s, hsw⟩ with hτ
    have hc : cc3 (h * C.y0 * h⁻¹) C.s C.s = ccard H11 τ τ :=
      cc3_eq_ccard (a := h * C.y0 * h⁻¹) (u := C.s) (v := C.s) (C.Ψh h) hsw hsw
    have h3 : τ ^ 3 = 1 := by
      have : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.y0 * h⁻¹} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using C.s_pow_three)
      rw [hτ, ← map_pow, this, map_one]
    have h1 : τ ≠ 1 := by
      intro h'
      have h'' : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.y0 * h⁻¹} : Set G))) = 1 :=
        (C.Ψh h).injective (by rw [← hτ, h', map_one])
      exact C.s_ne_one (congrArg Subtype.val h'')
    rcases hH.ord3 τ h3 h1 with ⟨-, h576⟩ | hle
    · exact Or.inr (Or.inr (Or.inl (by rw [hc]; exact h576)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hc]; exact ⟨ccard_pos _ _ _, hle⟩)))

theorem card_inf_centralizer (a u : G) :
    Nat.card ↥(centralizer ({a} : Set G) ⊓ centralizer ({u} : Set G)) = cc3 a u u := by
  unfold cc3
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun c => ?_))
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  tauto

theorem pgroup_le_64 [Finite G] (hF : FFacts) (hH : HFacts) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPs : ∀ p ∈ P, p * C.s = C.s * p) : Nat.card P ≤ 64 := by
  by_cases hP1 : Nat.card P = 1
  · omega
  obtain ⟨w, hwP, hw2, hwc⟩ := exists_central_involution_of_pgroup P hP hP1
  have hws : w * C.s = C.s * w := hPs w hwP
  have hle : P ≤ centralizer ({w} : Set G) ⊓ centralizer ({C.s} : Set G) := by
    intro p hp
    exact ⟨mem_centralizer_singleton_iff.2 (hwc p hp), mem_centralizer_singleton_iff.2 (hPs p hp)⟩
  have hdvd : Nat.card P ∣ cc3 w C.s C.s := by
    rw [← card_inf_centralizer]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  rw [hm] at hdvd ⊢
  have hcases := C.cc3_cases hF hH w hw2 hws
  have : 2 ^ m ≤ 64 := two_pow_le_64 (by tauto) hdvd
  exact this

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
