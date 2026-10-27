module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ1A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

private def z4i_conjHom (ρ : H) : H →* H where
  toFun x := ρ * x * ρ⁻¹
  map_one' := by simp
  map_mul' x y := by group

private lemma z4i_commute_three_mul {G : Type*} [Group G] {a b c d e f : G}
    (h1 : Commute a d) (h2 : Commute a e) (h3 : Commute a f)
    (h4 : Commute b d) (h5 : Commute b e) (h6 : Commute b f)
    (h7 : Commute c d) (h8 : Commute c e) (h9 : Commute c f) :
    Commute (a * b * c) (d * e * f) :=
  (((h1.mul_right h2).mul_right h3).mul_left ((h4.mul_right h5).mul_right h6)).mul_left
    ((h7.mul_right h8).mul_right h9)

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

theorem card_mod_three_of_inv (h : ZEData Q Y V V' B K ρ t τ l) {R : Subgroup H} (hRQ : R ≤ Q)
    (hR : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R) : Nat.card R % 3 = 1 := by
  let ρQ : MulAut Q := z4i_conjAut ρ Q h.rho_norm_Q
  have hρQ3 : ρQ ^ 3 = 1 := z4i_conjAut_pow_three ρ Q h.rho_norm_Q h.rho_pow_three
  have hfpfQ : ∀ x : Q, ρQ x = x → x = 1 :=
    z4i_conjAut_fpf ρ Q h.rho_norm_Q (fun x hxQ hfix => h.rho_fpf_Q x hxQ hfix)
  have hCinv : ∀ x ∈ R.subgroupOf Q, ρQ x ∈ R.subgroupOf Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [show ((ρQ x : Q) : H) = ρ * (x : H) * ρ⁻¹ from z4i_conjAut_apply ρ Q h.rho_norm_Q x]
    exact hR x hx
  have h1 := z4i_card_mod_three_of_fpf ρQ hρQ3 hfpfQ (R.subgroupOf Q) hCinv
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv] at h1

theorem rho_norm_F (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ z4iF K t τ, ρ * x * ρ⁻¹ ∈ z4iF K t τ := by
  have ht : Commute ρ t := h.t_rho.symm
  have hτ : Commute ρ τ := h.tau_rho.symm
  intro x hx
  obtain ⟨k, hk, a, b, rfl⟩ := (mem_F_iff h).mp hx
  rw [mem_F_iff h]
  refine ⟨ρ * k * ρ⁻¹, h.rho_norm_K k hk, a, b, ?_⟩
  have hta : ρ * t ^ (a : ℕ) * ρ⁻¹ = t ^ (a : ℕ) := by
    rw [(ht.pow_right (a : ℕ)).eq]; group
  have hτb : ρ * τ ^ (b : ℕ) * ρ⁻¹ = τ ^ (b : ℕ) := by
    rw [(hτ.pow_right (b : ℕ)).eq]; group
  calc ρ * (k * t ^ (a : ℕ) * τ ^ (b : ℕ)) * ρ⁻¹
      = (ρ * k * ρ⁻¹) * (ρ * t ^ (a : ℕ) * ρ⁻¹) * (ρ * τ ^ (b : ℕ) * ρ⁻¹) := by group
    _ = (ρ * k * ρ⁻¹) * t ^ (a : ℕ) * τ ^ (b : ℕ) := by rw [hta, hτb]

theorem F_comm_le_Q (h : ZEData Q Y V V' B K ρ t τ l) :
    ⁅z4iF K t τ, z4iF K t τ⁆ ≤ Q := by
  haveI : Q.Normal := ⟨fun n hn g => h.normal_Q g n hn⟩
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨k, hk, a, b, rfl⟩ := (mem_F_iff h).mp hx
  obtain ⟨k', hk', a', b', rfl⟩ := (mem_F_iff h).mp hy
  have hkk : Commute ((QuotientGroup.mk' Q) k) ((QuotientGroup.mk' Q) k') := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.V_le_Q (h.comm_mem_V k hk k' hk')
  have btk : Commute ((QuotientGroup.mk' Q) t) ((QuotientGroup.mk' Q) k) := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.comm_t_K k hk
  have btk' : Commute ((QuotientGroup.mk' Q) t) ((QuotientGroup.mk' Q) k') := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.comm_t_K k' hk'
  have bτk : Commute ((QuotientGroup.mk' Q) τ) ((QuotientGroup.mk' Q) k) := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.tau_comm_K_mod_Q k hk
  have bτk' : Commute ((QuotientGroup.mk' Q) τ) ((QuotientGroup.mk' Q) k') := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.tau_comm_K_mod_Q k' hk'
  have btτ : Commute ((QuotientGroup.mk' Q) t) ((QuotientGroup.mk' Q) τ) := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q)]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Commute.commutator_eq h.t_tau]
    exact Q.one_mem
  have hcomm : Commute ((QuotientGroup.mk' Q) (k * t ^ (a : ℕ) * τ ^ (b : ℕ)))
      ((QuotientGroup.mk' Q) (k' * t ^ (a' : ℕ) * τ ^ (b' : ℕ))) := by
    have h1 : Commute ((QuotientGroup.mk' Q) k) ((QuotientGroup.mk' Q) k') := hkk
    have h2 : Commute ((QuotientGroup.mk' Q) k) (((QuotientGroup.mk' Q) t) ^ (a' : ℕ)) :=
      btk.symm.pow_right (a' : ℕ)
    have h3 : Commute ((QuotientGroup.mk' Q) k) (((QuotientGroup.mk' Q) τ) ^ (b' : ℕ)) :=
      bτk.symm.pow_right (b' : ℕ)
    have h4 : Commute (((QuotientGroup.mk' Q) t) ^ (a : ℕ)) ((QuotientGroup.mk' Q) k') :=
      btk'.pow_left (a : ℕ)
    have h5 : Commute (((QuotientGroup.mk' Q) t) ^ (a : ℕ))
        (((QuotientGroup.mk' Q) t) ^ (a' : ℕ)) :=
      ((Commute.refl ((QuotientGroup.mk' Q) t)).pow_left (a : ℕ)).pow_right (a' : ℕ)
    have h6 : Commute (((QuotientGroup.mk' Q) t) ^ (a : ℕ))
        (((QuotientGroup.mk' Q) τ) ^ (b' : ℕ)) :=
      (btτ.pow_left (a : ℕ)).pow_right (b' : ℕ)
    have h7 : Commute (((QuotientGroup.mk' Q) τ) ^ (b : ℕ)) ((QuotientGroup.mk' Q) k') :=
      bτk'.pow_left (b : ℕ)
    have h8 : Commute (((QuotientGroup.mk' Q) τ) ^ (b : ℕ))
        (((QuotientGroup.mk' Q) t) ^ (a' : ℕ)) :=
      (btτ.symm.pow_left (b : ℕ)).pow_right (a' : ℕ)
    have h9 : Commute (((QuotientGroup.mk' Q) τ) ^ (b : ℕ))
        (((QuotientGroup.mk' Q) τ) ^ (b' : ℕ)) :=
      ((Commute.refl ((QuotientGroup.mk' Q) τ)).pow_left (b : ℕ)).pow_right (b' : ℕ)
    simp only [map_mul, map_pow]
    exact z4i_commute_three_mul h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [← QuotientGroup.eq_one_iff (N := Q)]
  rw [← QuotientGroup.mk'_apply]
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact hcomm

theorem rho_norm_F_comm (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ ⁅z4iF K t τ, z4iF K t τ⁆, ρ * x * ρ⁻¹ ∈ ⁅z4iF K t τ, z4iF K t τ⁆ := by
  intro x hx
  have hle : (z4iF K t τ).map (z4i_conjHom ρ) ≤ z4iF K t τ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact rho_norm_F h z hz
  have hmap : (⁅z4iF K t τ, z4iF K t τ⁆).map (z4i_conjHom ρ) ≤
      ⁅z4iF K t τ, z4iF K t τ⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem exists_F_comm_not_Y (h : ZEData Q Y V V' B K ρ t τ l) :
    ∃ f ∈ ⁅z4iF K t τ, z4iF K t τ⁆, f ∉ Y := by
  have hQK : Q < K := by
    refine lt_of_le_of_ne h.Q_le_K ?_
    intro heq
    have hcard : Nat.card Q = Nat.card K := by rw [heq]
    rw [h.card_Q, h.card_K] at hcard
    norm_num at hcard
  obtain ⟨x, hxK, hxQ⟩ := SetLike.exists_of_lt hQK
  refine ⟨⁅t, x⁆, ?_, ?_⟩
  · exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      (Subgroup.mem_sup_left hxK)
  · exact fun hY => hxQ ((h.comm_t_mem_Y_iff hxK).mp hY)

theorem F_comm_sup_Y (h : ZEData Q Y V V' B K ρ t τ l) :
    ⁅z4iF K t τ, z4iF K t τ⁆ ⊔ Y = Q := by
  let R : Subgroup H := ⁅z4iF K t τ, z4iF K t τ⁆ ⊔ Y
  change R = Q
  have hYR : Y ≤ R := le_sup_right
  have hRQ : R ≤ Q := sup_le (F_comm_le_Q h) h.Y_le_Q
  have hRinv : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R := by
    intro x hx
    have h1 : (⁅z4iF K t τ, z4iF K t τ⁆).map (z4i_conjHom ρ) ≤
        ⁅z4iF K t τ, z4iF K t τ⁆ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact rho_norm_F_comm h z hz
    have h2 : Y.map (z4i_conjHom ρ) ≤ Y := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact h.rho_norm_Y z hz
    have hmap : R.map (z4i_conjHom ρ) ≤ R := by
      change (⁅z4iF K t τ, z4iF K t τ⁆ ⊔ Y).map (z4i_conjHom ρ) ≤
        ⁅z4iF K t τ, z4iF K t τ⁆ ⊔ Y
      rw [Subgroup.map_sup]
      exact sup_le (h1.trans le_sup_left) (h2.trans le_sup_right)
    exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hmod := card_mod_three_of_inv h hRQ hRinv
  have hYdvd : 16 ∣ Nat.card R := by
    have h1 := Subgroup.card_dvd_of_le hYR
    rwa [h.card_Y] at h1
  have hRdvd : Nat.card R ∣ 64 := by
    have h1 := Subgroup.card_dvd_of_le hRQ
    rwa [h.card_Q] at h1
  by_cases h64 : Nat.card R = 64
  · exact Subgroup.eq_of_le_of_card_ge hRQ (by rw [h64, h.card_Q])
  · exfalso
    have h16 : Nat.card R = 16 := z4i_card_eq_sixteen_of hYdvd hRdvd hmod h64
    have hRY : R = Y :=
      (Subgroup.eq_of_le_of_card_ge hYR (by rw [h16, h.card_Y])).symm
    obtain ⟨f, hf, hfY⟩ := exists_F_comm_not_Y h
    have hfR : f ∈ R := Subgroup.mem_sup_left hf
    exact hfY (hRY ▸ hfR)

theorem mem_F_comm_mul_Y (h : ZEData Q Y V V' B K ρ t τ l) {q : H} (hq : q ∈ Q) :
    ∃ f ∈ ⁅z4iF K t τ, z4iF K t τ⁆, ∃ y ∈ Y, q = f * y := by
  have hq' : q ∈ ⁅z4iF K t τ, z4iF K t τ⁆ ⊔ Y := by
    rw [F_comm_sup_Y h]; exact hq
  refine (mem_sup_iff_of_normalizes (H := ⁅z4iF K t τ, z4iF K t τ⁆) (K := Y) ?_).mp hq'
  intro y hy f hf
  have hyQ : y ∈ Q := h.Y_le_Q hy
  have hfQ : f ∈ Q := F_comm_le_Q h hf
  have hconj : y * f * y⁻¹ = f := by
    rw [h.Q_comm y hyQ f hfQ]; group
  rw [hconj]
  exact hf

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
