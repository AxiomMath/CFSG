module

public import CFSG.LargeExtraspecial.AS62Frame
public import CFSG.LargeExtraspecial.AS62W6
public import CFSG.LargeExtraspecial.AS62Sem2
public import CFSG.LargeExtraspecial.AS62Sem3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions AS62.Sem

namespace AS62

theorem Frame.exists_A_eq_of_rep_vec_zero {G : Type*} [Group G] (F : Frame G) {h : G} {q : ℕ}
    (hd : F.Rep h (0, q)) : ∃ a : F.A, (a : G) = h ∧ permCode (F.σ a) = q := by
  obtain ⟨-, a, ha, rfl⟩ := hd
  exact ⟨a, by rw [F.vOf_zero, one_mul], ha⟩

variable {G : Type} [Group G] [Finite G]

structure IsFrameOf (S : Setting G) (H : Subgroup G) (F : Frame G) : Prop where
  H_eq : F.H = H
  V_eq : F.V = closure (S.zConj H)
  label : ∃ L : Label S H, F.zz = L.zz

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem exists_isFrameOf (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    ∃ F : Frame G, IsFrameOf S H F ∧ F.zz 1 = p := by
  obtain ⟨L, hL⟩ := hc.exists_label hp hpz
  obtain ⟨F, hFH, hFV, hFz⟩ := hc.exists_frame L
  exact ⟨F, ⟨hFH, hFV, L, hFz⟩, by rw [hFz, hL]⟩

end ConfHyp

namespace IsFrameOf

variable {S : Setting G} {H : Subgroup G} {F : Frame G}

omit [Finite G] in
theorem zz_zero (hF : IsFrameOf S H F) : F.zz 0 = S.z := by
  obtain ⟨L, hL⟩ := hF.label
  rw [hL, L.zz_zero]

omit [Finite G] in
theorem zz_mem (hF : IsFrameOf S H F) (i : Fin 5) : F.zz i ∈ S.zConj H := by
  obtain ⟨L, hL⟩ := hF.label
  rw [hL]
  exact L.zz_mem i

omit [Finite G] in
theorem rep_z (hF : IsFrameOf S H F) : F.Rep S.z zD := hF.zz_zero ▸ F.rep_zD

omit [Finite G] in
theorem A_le (hF : IsFrameOf S H F) : F.A ≤ H := hF.H_eq ▸ F.A_le_H

omit [Finite G] in
theorem σ_eq (hF : IsFrameOf S H F) {L : Label S H} (hL : F.zz = L.zz) (a : F.A) :
    F.σ a = L.σ ⟨a, hF.A_le a.2⟩ := by
  refine Equiv.ext fun i => L.zz_injective ?_
  rw [← L.conj_zz, ← hL, ← F.σ_spec]

theorem permCode_σ_of_rep (hF : IsFrameOf S H F) (hc : ConfHyp S H) {L : Label S H}
    (hL : F.zz = L.zz) {h : G} (hh : h ∈ H) {d : ℕ × ℕ} (hd : F.Rep h d) :
    permCode (L.σ ⟨h, hh⟩) = d.2 := by
  obtain ⟨-, a, ha, rfl⟩ := hd
  have hv : F.vOf d.1 ∈ closure (S.zConj H) := hF.V_eq ▸ F.vOf_mem d.1
  have e : (⟨F.vOf d.1 * a, hh⟩ : H) = ⟨F.vOf d.1, hc.V_le hv⟩ * ⟨a, hF.A_le a.2⟩ := rfl
  rw [e, map_mul, (L.σ_eq_one_iff hc _).mpr hv, one_mul, ← hF.σ_eq hL, ha]

theorem mem_k1Codes (hF : IsFrameOf S H F) (hc : ConfHyp S H) {q : G} (hq : q ∈ S.QG)
    {d : ℕ × ℕ} (hd : F.Rep q d) : d.2 ∈ k1Codes := by
  obtain ⟨L, hL⟩ := hF.label
  rw [← hF.permCode_σ_of_rep hc hL (hc.QG_le hq) hd]
  exact Frame.permCode_mem_k1Codes (L.σ_mem_klein hc (q := ⟨q, hc.QG_le hq⟩) hq)

omit [Finite G] in
theorem mem_M_of_rep_xD (hF : IsFrameOf S H F) {x : G} (hx : F.Rep x xD) : x ∈ S.M := by
  obtain ⟨a, rfl, ha⟩ := F.exists_A_eq_of_rep_vec_zero hx
  have hσ : F.σ a = Equiv.swap 2 3 * Equiv.swap 3 4 := permCode_injective (ha.trans (by decide))
  have e := F.σ_spec a 0
  rw [hσ, show (Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5)) 0 = 0 by
    decide, hF.zz_zero] at e
  rw [S.mem_M_iff]
  calc (a : G) * S.z = a * S.z * (a : G)⁻¹ * a := by group
    _ = S.z * a := by rw [e]

omit [Finite G] in
theorem conj_z_of_rep_sD (hF : IsFrameOf S H F) {s : G} (hs : F.Rep s sD) :
    s * S.z * s⁻¹ = F.zz 1 := by
  obtain ⟨a, rfl, ha⟩ := F.exists_A_eq_of_rep_vec_zero hs
  have hσ : F.σ a = Equiv.swap 0 1 * Equiv.swap 2 3 := permCode_injective (ha.trans (by decide))
  have e := F.σ_spec a 0
  rw [hσ, show (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5)) 0 = 1 by
    decide, hF.zz_zero] at e
  exact e

omit [Finite G] in
theorem not_mem_M_of_rep_sD (hF : IsFrameOf S H F) {s : G} (hs : F.Rep s sD) : s ∉ S.M := by
  intro hsM
  obtain ⟨L, hL⟩ := hF.label
  have h1 := hF.conj_z_of_rep_sD hs
  rw [S.conj_z_of_mem_M hsM, hL] at h1
  exact L.zz_ne_z (i := 1) (by decide) h1.symm

end IsFrameOf

theorem klein_conj_eq : ∀ p : Equiv.Perm (Fin 5),
    (p = 1 ∨ p = Equiv.swap 1 2 * Equiv.swap 3 4 ∨ p = Equiv.swap 1 3 * Equiv.swap 2 4 ∨
      p = Equiv.swap 1 4 * Equiv.swap 2 3) → p ≠ 1 →
    p = Equiv.swap 1 2 * Equiv.swap 3 4 ∨
      (Equiv.swap 2 3 * Equiv.swap 3 4) * p * (Equiv.swap 2 3 * Equiv.swap 3 4)⁻¹ =
        Equiv.swap 1 2 * Equiv.swap 3 4 ∨
      (Equiv.swap 2 3 * Equiv.swap 3 4)⁻¹ * p * (Equiv.swap 2 3 * Equiv.swap 3 4) =
        Equiv.swap 1 2 * Equiv.swap 3 4 := by
  decide +kernel

theorem exists_sign_eq_one_apply_zero : ∀ i : Fin 5,
    ∃ p : Equiv.Perm (Fin 5), Equiv.Perm.sign p = 1 ∧ p 0 = i := by
  decide +kernel

namespace IsFrameOf

variable {S : Setting G} {H : Subgroup G} {F : Frame G}

theorem card_A_inf_M (hF : IsFrameOf S H F) (hc : ConfHyp S H) :
    Nat.card ↥(F.A ⊓ S.M) = 12 := by
  obtain ⟨L, hL⟩ := hF.label
  have hA60 : Nat.card F.A = 60 := by
    rw [Nat.card_congr (MonoidHom.ofInjective F.σ_injective).toEquiv, F.σ_range,
      card_alternatingGroup_five]
  have horb : {x | ∃ a ∈ F.A, a * S.z * a⁻¹ = x} = S.zConj H := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact conj_mem_conjIn (hF.A_le ha)
    · intro hy
      obtain ⟨i, rfl⟩ := L.exists_zz_eq hy
      obtain ⟨p, hp, hp0⟩ := exists_sign_eq_one_apply_zero i
      obtain ⟨a, ha⟩ := F.exists_σ_eq (Equiv.Perm.mem_alternatingGroup.mpr hp)
      refine ⟨a, a.2, ?_⟩
      rw [← hF.zz_zero, F.σ_spec, ha, hp0, hL]
  have h1 := Setting.card_eq_relIndex_mul F.A S.M
  rw [Setting.relIndex_centralizer_eq_ncard] at h1
  change Nat.card F.A = {x | ∃ a ∈ F.A, a * S.z * a⁻¹ = x}.ncard * _ at h1
  rw [horb, hc.ncard_zConj, hA60] at h1
  omega

theorem mem_QG_of_rep_eD (hF : IsFrameOf S H F) (hc : ConfHyp S H) {e : G}
    (he : F.Rep e eD) : e ∈ S.QG := by
  obtain ⟨L, hL⟩ := hF.label
  obtain ⟨e', rfl, he'⟩ := F.exists_A_eq_of_rep_vec_zero he
  have hσe : F.σ e' = Equiv.swap 1 2 * Equiv.swap 3 4 :=
    permCode_injective (he'.trans (by decide))
  obtain ⟨x, -, hx⟩ := F.exists_rep_xD
  have hxM := hF.mem_M_of_rep_xD hx
  obtain ⟨x', rfl, hx'⟩ := F.exists_A_eq_of_rep_vec_zero hx
  have hσx : F.σ x' = Equiv.swap 2 3 * Equiv.swap 3 4 :=
    permCode_injective (hx'.trans (by decide))
  set B := F.A.subgroupOf S.M with hBdef
  have hB : Nat.card B = 12 := by
    rw [hBdef, ← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hF.card_A_inf_M hc]
  have hBle : B.map S.ρ ≤ (H.subgroupOf S.M).map S.ρ :=
    map_mono fun b hb => mem_subgroupOf.mpr (hF.A_le (mem_subgroupOf.mp hb))
  have hdvd : Nat.card (B.map S.ρ) ∣ 6 := hc.card_map_ρ ▸ card_dvd_of_le hBle
  have hle6 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 := Setting.card_eq_relIndex_mul B S.ρ.ker
  rw [Subgroup.relIndex_ker, hB] at h1
  have hgt : 1 < Nat.card ↥(B ⊓ S.ρ.ker) := by
    by_contra hcon
    have := Nat.mul_le_mul hle6 (not_lt.mp hcon)
    omega
  obtain ⟨⟨b, hbBK⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((one_lt_card_iff_ne_bot _).mp hgt)
  have hbA : (b : G) ∈ F.A := mem_subgroupOf.mp (mem_inf.mp hbBK).1
  have hbQ : (b : G) ∈ S.QG := ⟨b, S.ker_ρ ▸ (mem_inf.mp hbBK).2, rfl⟩
  have ha1 : F.σ ⟨b, hbA⟩ ≠ 1 := by
    intro h
    apply hb1
    have h2 : (⟨b, hbA⟩ : F.A) = 1 := F.σ_injective (h.trans (map_one _).symm)
    have h3 : (b : G) = 1 := by simpa using congrArg Subtype.val h2
    exact Subtype.ext (Subtype.ext h3)
  have hK : F.σ ⟨b, hbA⟩ = 1 ∨ F.σ ⟨b, hbA⟩ = Equiv.swap 1 2 * Equiv.swap 3 4 ∨
      F.σ ⟨b, hbA⟩ = Equiv.swap 1 3 * Equiv.swap 2 4 ∨
      F.σ ⟨b, hbA⟩ = Equiv.swap 1 4 * Equiv.swap 2 3 := by
    rw [hF.σ_eq hL]
    exact L.σ_mem_klein hc (q := ⟨b, hF.A_le hbA⟩) hbQ
  rcases klein_conj_eq _ hK ha1 with h | h | h
  · rw [← hσe] at h
    rw [← F.σ_injective h]
    exact hbQ
  · rw [← hσx, ← hσe, ← map_inv, ← map_mul, ← map_mul] at h
    rw [← F.σ_injective h]
    exact S.conj_mem_QG hxM hbQ
  · rw [← hσx, ← hσe, ← map_inv, ← map_mul, ← map_mul] at h
    rw [← F.σ_injective h]
    have := S.conj_mem_QG (S.M.inv_mem hxM) hbQ
    rwa [inv_inv] at this

theorem qProd_mem_QG (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x : G} (ht : F.Rep t tD)
    (he : F.Rep e eD) (hx : F.Rep x xD) (c : ℕ) : Frame.qProd S.z t e x c ∈ S.QG := by
  have heQ := hF.mem_QG_of_rep_eD hc he
  have hxM := hF.mem_M_of_rep_xD hx
  have htt : t = F.zz 1 := F.eq_of_rep ht F.rep_tD
  have htM : t ∈ S.M := by
    rw [htt]
    exact hc.mem_M_of_mem (hF.zz_mem 1)
  have htinv : t⁻¹ = t := by
    rw [htt]
    exact F.zz_inv 1
  have hb₁ : t * e * t * e ∈ S.QG := by
    have := S.QG.mul_mem (S.conj_mem_QG htM heQ) heQ
    rwa [htinv] at this
  have hbit : ∀ {g : G}, g ∈ S.QG → ∀ b : Bool, Frame.bitPow g b ∈ S.QG := by
    intro g hg b
    cases b
    · exact one_mem _
    · exact hg
  unfold Frame.qProd
  exact S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (hbit hb₁ _)
    (hbit (S.conj_mem_QG hxM hb₁) _)) (hbit heQ _)) (hbit (S.conj_mem_QG hxM heQ) _))
    (hbit S.z_mem_QG _)

theorem exists_qProd_eq (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x : G}
    (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) {q : G} (hq : q ∈ S.QG) :
    ∃ c < 32, Frame.qProd S.z t e x c = q := by
  classical
  set T := (Finset.range 32).image fun c => Frame.qProd S.z t e x c with hT
  have hsub : (T : Set G) ⊆ S.QG := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hF.qProd_mem_QG hc ht he hx c
  have hTcard : T.card = 32 := by
    rw [hT, Finset.card_image_of_injOn, Finset.card_range]
    intro c hc' d hd' hcd
    exact F.qProd_injective hF.rep_z ht he hx (Finset.mem_range.mp (Finset.mem_coe.mp hc'))
      (Finset.mem_range.mp (Finset.mem_coe.mp hd')) hcd
  have heq : (T : Set G) = S.QG := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      hc.card_QG]) (Set.toFinite _)
  have hqT : q ∈ (T : Set G) := by
    rw [heq]
    exact hq
  obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hqT)
  exact ⟨c, Finset.mem_range.mp hc', rfl⟩

theorem commute_QG_of_commute (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x g : G}
    (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) (h₁ : g * (t * e * t * e) =
      t * e * t * e * g) (h₂ : g * e = e * g) (h₃ : g * x = x * g) (h₄ : g * S.z = S.z * g)
    {q : G} (hq : q ∈ S.QG) : g * q = q * g := by
  have hconj : ∀ {u : G}, g * u = u * g → g * (x * u * x⁻¹) = x * u * x⁻¹ * g := by
    intro u hu
    have hxi : g * x⁻¹ = x⁻¹ * g := by
      calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
        _ = x⁻¹ * (g * x) * x⁻¹ := by rw [h₃]
        _ = x⁻¹ * g := by group
    calc g * (x * u * x⁻¹) = (g * x) * u * x⁻¹ := by group
      _ = x * (g * u) * x⁻¹ := by rw [h₃]; group
      _ = x * u * (g * x⁻¹) := by rw [hu]; group
      _ = x * u * x⁻¹ * g := by rw [hxi]; group
  have hbit : ∀ {u : G}, g * u = u * g → ∀ b : Bool, g * Frame.bitPow u b =
      Frame.bitPow u b * g := by
    intro u hu b
    cases b
    · change g * 1 = 1 * g
      group
    · exact hu
  have hmul : ∀ {u v : G}, g * u = u * g → g * v = v * g → g * (u * v) = u * v * g := by
    intro u v hu hv
    calc g * (u * v) = g * u * v := by group
      _ = u * (g * v) := by rw [hu]; group
      _ = u * v * g := by rw [hv]; group
  obtain ⟨c, -, rfl⟩ := hF.exists_qProd_eq hc ht he hx hq
  unfold Frame.qProd
  exact hmul (hmul (hmul (hmul (hbit h₁ _) (hbit (hconj h₁) _)) (hbit h₂ _))
    (hbit (hconj h₂) _)) (hbit h₄ _)

end IsFrameOf

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem exists_frame_gens (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    ∃ (F : Frame G) (e x s : G), IsFrameOf S H F ∧ F.zz 1 = p ∧ F.Rep S.z zD ∧ F.Rep p tD ∧
      F.Rep e eD ∧ F.Rep x xD ∧ F.Rep s sD ∧ e ∈ F.A ∧ x ∈ F.A ∧ s ∈ F.A ∧ e ∈ S.QG ∧
      x ∈ S.M ∧ s ∉ S.M := by
  obtain ⟨F, hF, hF1⟩ := hc.exists_isFrameOf hp hpz
  obtain ⟨e, heA, he⟩ := F.exists_rep_eD
  obtain ⟨x, hxA, hx⟩ := F.exists_rep_xD
  obtain ⟨s, hsA, hs⟩ := F.exists_rep_sD
  exact ⟨F, e, x, s, hF, hF1, hF.rep_z, hF1 ▸ F.rep_tD, he, hx, hs, heA, hxA, hsA,
    hF.mem_QG_of_rep_eD hc he, hF.mem_M_of_rep_xD hx, hF.not_mem_M_of_rep_sD hs⟩

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
