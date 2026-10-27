module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs
public import CFSG.GH74.GLS.Stage4.T2NegConj
public import CFSG.GH74.GLS.Stage4.T2NegFour
public import CFSG.GH74.GLS.Stage4.T2NumGtMixDefs
public import CFSG.GH74.GLS.Stage4.T2P51

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.T2
open scoped Pointwise commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

theorem loc5M_of_cfg {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z u w₁ w₂ : G} {K₁ K₂ H : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (cfg : Ch6MixCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q₁ q₂ z u K₁ K₂ H w₁ w₂)
    (φ₁ : SL2 F₁ →* G) (hrange₁ : φ₁.range = K₁)
    (φ₂ : SL2 F₂ →* G) (hc₂ : MixCoord2 φ₂ z u w₂ K₂ H) :
    ∃ N : T2N1 G, N.z = z ∧ N.K₁ = K₁ ∧ N.K₂ = K₂ ∧ N.q₁ = q₁ ∧ N.q₂ = q₂ ∧ Ch6Loc5M N u ∧
      Ch6Coord2 N := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hw₂ := hc₂.w
  have hw₁z : w₁ * z = z * w₁ := cfg.w₁_z
  have hw₂z : w₂ * z = z * w₂ := cfg.w₂_z
  have hAp : IsPGroup 2 ↥(Subgroup.closure ({z, u, w₁, w₂} : Set G)) :=
    isPGroup_closure_zuw cfg.zz cfg.uu cfg.zu_comm hw₁z hw₂z cfg.w₁_sq cfg.w₂_sq cfg.w₁_u cfg.w₂_u
      cfg.w₁w₂_comm
  have hAz : ∀ a ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G), a * z = z * a := by
    have hle : Subgroup.closure ({z, u, w₁, w₂} : Set G) ≤ centralizer ({z} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with rfl | rfl | rfl | rfl
      · rfl
      · exact cfg.zu_comm.symm
      · exact hw₁z
      · exact hw₂z
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  obtain ⟨S, hSp, hSidx, hAS, hSz⟩ := exists_sylow_two_contains hSet.central _ hAp hAz
  have hzS : z ∈ S := hAS (Subgroup.subset_closure (by simp))
  have huS : u ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hw₁S : w₁ ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hw₂S : w₂ ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hSC : S ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    le_oPrimeResidualOf_centralizer hSp hSz
  have hSidx2 : (S ⊓ (K₁ ⊔ K₂)).relIndex S = 2 :=
    relIndex_inf_sylow_of_index_two hSet.le_residual hSet.index_two hSC hSidx
  have hKS : K₁ ⊔ K₂ ⊔ S = oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    refine sup_eq_of_relIndex_two le_sup_left (sup_le hSet.le_residual hSC) hSet.index_two ?_
    intro hle
    have hSK : S ≤ K₁ ⊔ K₂ := le_trans le_sup_right hle
    have h1 : (S ⊓ (K₁ ⊔ K₂)).relIndex S = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact fun x hx => ⟨hx, hSK hx⟩
    rw [h1] at hSidx2
    exact absurd hSidx2 (by norm_num)
  have hwconj₂ : ∀ x : SL2 F₂, w₂ * φ₂ x * w₂⁻¹ = φ₂ (sl2W F₂ * x * (sl2W F₂)⁻¹) := fun x => by
    rw [hw₂]; simp [map_mul, map_inv]
  have hKcomm := hSet.comm
  have hq₂3 : 3 ≤ q₂ := by
    have h1 : 1 < Nat.card F₂ := Finite.one_lt_card
    rw [hSet.card₂] at h1
    obtain ⟨k, hk⟩ := hSet.odd₂
    omega
  refine ⟨⟨q₁, q₂, z, S, K₁, K₂, H, (uSub F₁).map φ₁, (lSub F₁).map φ₁, (uSub F₂).map φ₂,
    (lSub F₂).map φ₂, w₁, w₂⟩, rfl, rfl, rfl, rfl, rfl, ?loc, ?coord⟩
  case coord =>
    exact
      { coord₂ := ⟨F₂, inferInstance, hSet.finite₂, φ₂, hSet.card₂, hc₂.inj, hc₂.range, hc₂.neg,
          rfl, rfl, hw₂, hc₂.H_inf⟩ }
  exact
    { q₁_odd := hSet.odd₁
      q₂_odd := hSet.odd₂
      q₂_le := hSet.le
      q₁_ge := hSet.five
      q₂_ge := hq₂3
      q₁_pp := by
        have : Fintype F₁ := Fintype.ofFinite F₁
        obtain ⟨n, hp, hn⟩ := FiniteField.card F₁ (ringChar F₁)
        exact ⟨ringChar F₁, n, hp, by rw [← hSet.card₁, Nat.card_eq_fintype_card, hn]⟩
      q₂_pp := by
        have : Fintype F₂ := Fintype.ofFinite F₂
        obtain ⟨n, hp, hn⟩ := FiniteField.card F₂ (ringChar F₂)
        exact ⟨ringChar F₂, n, hp, by rw [← hSet.card₂, Nat.card_eq_fintype_card, hn]⟩
      z_ord := hSet.central.1
      one_class := hSet.one_class
      O2prime := hSet.O2prime
      K_comm := hSet.comm
      iso₁ := ⟨F₁, inferInstance, hSet.finite₁, hSet.card₁, hSet.iso₁⟩
      iso₂ := ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂, hSet.iso₂⟩
      z_mem_K₁ := hSet.z_mem₁
      z_mem_K₂ := hSet.z_mem₂
      K_inter := hSet.inter_eq.le
      u_ord := orderOf_eq_prime (by rw [sq]; exact cfg.uu) cfg.u_ne
      u_ne := fun h => cfg.zu_ne h.symm
      u_comm := cfg.zu_comm.symm
      S_pGroup := hSp
      S_sylow := hSidx
      z_mem_S := hzS
      z_cent_S := hSz
      u_mem_S := huS
      S_idx := hSidx2
      w₁_memS := hw₁S
      w₂_memS := hw₂S
      K₁_eq := by
        show K₁ = (uSub F₁).map φ₁ ⊔ (lSub F₁).map φ₁
        rw [← hrange₁, MonoidHom.range_eq_map, ← Subgroup.map_sup, uSub_sup_lSub]
      K₂_eq := by
        show K₂ = (uSub F₂).map φ₂ ⊔ (lSub F₂).map φ₂
        rw [← hc₂.range, MonoidHom.range_eq_map, ← Subgroup.map_sup, uSub_sup_lSub]
      card_X₂ := (card_map_eq _ φ₂ hc₂.inj).trans (card_uSub.trans hSet.card₂)
      card_X₂' := (card_map_eq _ φ₂ hc₂.inj).trans (card_lSub.trans hSet.card₂)
      X₂_comm := map_comm_of φ₂ uSub_comm
      X₂'_comm := map_comm_of φ₂ lSub_comm
      X₁_exp := by
        have hp : q₁.minFac = ringChar F₁ := by rw [← hSet.card₁]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₁ _ (fun a ha => by rw [hp]; exact pow_char_uSub _ a ha)
      X₁'_exp := by
        have hp : q₁.minFac = ringChar F₁ := by rw [← hSet.card₁]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₁ _ (fun a ha => by rw [hp]; exact pow_char_lSub _ a ha)
      X₂_exp := by
        have hp : q₂.minFac = ringChar F₂ := by rw [← hSet.card₂]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₂ _ (fun a ha => by rw [hp]; exact pow_char_uSub _ a ha)
      X₂'_exp := by
        have hp : q₂.minFac = ringChar F₂ := by rw [← hSet.card₂]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₂ _ (fun a ha => by rw [hp]; exact pow_char_lSub _ a ha)
      X₂_ne := fun h => uSub_ne_lSub (Subgroup.map_injective hc₂.inj h)
      H_comm := cfg.H_comm
      z_mem_H := cfg.z_mem_H
      u_mem_H := cfg.u_mem_H
      H₁_eq := by
        ext x
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨hxH, hxK⟩
          exact ⟨(cfg.H₁_iff x hxK).1 hxH, hxK⟩
        · rintro ⟨hxc, hxK⟩
          exact ⟨(cfg.H₁_iff x hxK).2 hxc, hxK⟩
      H₂_eq := by
        ext x
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨hxH, hxK⟩
          exact ⟨(cfg.H₂_iff x hxK).1 hxH, hxK⟩
        · rintro ⟨hxc, hxK⟩
          exact ⟨(cfg.H₂_iff x hxK).2 hxc, hxK⟩
      H₁_cyc := cfg.H₁_cyc
      H₂_cyc := cfg.H₂_cyc
      card_H_K₂ := cfg.H₂_card
      H_idx := cfg.H_idx
      H_le := by
        rw [hKS]
        exact cfg.H_le_C
      H_not_le_K := cfg.H_not_le_K
      H_norm_X₂ := hc₂.H_norm_u
      H_norm_X₂' := hc₂.H_norm_l
      H_fpf₂ := by
        intro h hh hgz x hx hfix
        have hh' : h ∈ (tSub F₂).map φ₂ := by rw [← hc₂.H_inf]; exact hh
        obtain ⟨a, ha, rfl⟩ := hh'
        obtain ⟨ξ, hξ, rfl⟩ := hx
        have h1 : a ≠ 1 := by
          rintro rfl
          exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
        have h2 : a ≠ negOne F₂ := by
          rintro rfl
          exact hgz (by rw [hc₂.neg]; exact Subgroup.mem_zpowers _)
        have : a * ξ * a⁻¹ = ξ := by
          apply hc₂.inj
          rw [map_mul, map_mul, map_inv]
          exact hfix
        rw [tSub_fpf_uSub a ha h1 h2 ξ hξ this, map_one]
      H_fpf₂' := by
        intro h hh hgz x hx hfix
        have hh' : h ∈ (tSub F₂).map φ₂ := by rw [← hc₂.H_inf]; exact hh
        obtain ⟨a, ha, rfl⟩ := hh'
        obtain ⟨ξ, hξ, rfl⟩ := hx
        have h1 : a ≠ 1 := by
          rintro rfl
          exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
        have h2 : a ≠ negOne F₂ := by
          rintro rfl
          exact hgz (by rw [hc₂.neg]; exact Subgroup.mem_zpowers _)
        have : a * ξ * a⁻¹ = ξ := by
          apply hc₂.inj
          rw [map_mul, map_mul, map_inv]
          exact hfix
        rw [tSub_fpf_lSub a ha h1 h2 ξ hξ this, map_one]
      w₁_mem := cfg.w₁_mem
      w₂_mem := cfg.w₂_mem
      w₁_sq := cfg.w₁_sq
      w₂_sq := cfg.w₂_sq
      w₂_swap := map_conj_mem φ₂ _ _ hwconj₂ (fun x hx => sl2W_conj_uSub x hx)
      w₂_swap' := map_conj_mem φ₂ _ _ hwconj₂ (fun x hx => sl2W_conj_lSub x hx)
      w₁_inv := by
        intro h hh
        have hc : w₂ * h * w₂⁻¹ = h := by
          rw [← hKcomm h hh.2 _ cfg.w₂_mem]; group
        have h0 := cfg.w₀_inv h hh.1
        calc w₁ * h * w₁⁻¹ = w₁ * (w₂ * h * w₂⁻¹) * w₁⁻¹ := by rw [hc]
          _ = (w₁ * w₂) * h * (w₁ * w₂)⁻¹ := by group
          _ = h⁻¹ := h0
      w₂_inv := by
        intro h hh
        have hh' : h ∈ (tSub F₂).map φ₂ := by rw [← hc₂.H_inf]; exact hh
        exact map_conj_inv φ₂ w₂ (fun x => sl2W F₂ * x * (sl2W F₂)⁻¹) hwconj₂ sl2W_inv_tSub h hh'
      w₁_u := cfg.w₁_u
      w₂_u := cfg.w₂_u
      w₁_normH := Subgroup.mem_normalizer_fintype (fun n hn => cfg.w₁_normH n hn)
      w₂_normH := Subgroup.mem_normalizer_fintype (fun n hn => cfg.w₂_normH n hn)
      w₀_inv := cfg.w₀_inv
      w₀_cent := cfg.w₀_u
      u_inv_X₂ := map_conj_inv φ₂ u _ hc₂.hu slConj_dNeg_uSub
      u_inv_X₂' := map_conj_inv φ₂ u _ hc₂.hu slConj_dNeg_lSub
      card_H_K₁ := cfg.H₁_card
      H₁_cent := cfg.H₁_cent }

end Core

end CFSG.GH74.GLS.Stage4.Rest
