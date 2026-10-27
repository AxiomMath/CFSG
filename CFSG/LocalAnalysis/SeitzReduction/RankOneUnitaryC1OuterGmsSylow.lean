module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

@[expose] def U3C1GmsCharInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P →
      ∀ z ∈ normalizer ((swapS₂ P U T : Subgroup G) : Set G),
        (∃ P' : Subgroup G, IsPGroup 2 P' ∧ swapS₂ P U T ≤ P' ∧ z ∈ P') →
          z ∈ normalizer (U₁ : Set G)

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem exists_sylow_of_char
    (hchar : ∀ z ∈ normalizer ((swapS₂ P U T : Subgroup G) : Set G),
      (∃ P' : Subgroup G, IsPGroup 2 P' ∧ swapS₂ P U T ≤ P' ∧ z ∈ P') →
        z ∈ normalizer (U₁ : Set G)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T := by
  by_contra hns
  obtain ⟨z, hzN, hzS, P', hP'2, hSP', hzP'⟩ :=
    exists_normalizer_not_mem_of_not_isSylow hW.isPGroup_S₂ hns
  have hzU := hchar z hzN ⟨P', hP'2, hSP', hzP'⟩
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨hT₁card, -, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hcT : ∀ τ ∈ T, z * τ * z⁻¹ ∈ swapS₂ P U T := fun τ hτ =>
    (mem_normalizer_iff.mp hzN τ).mp (hW.le_S₂ (mem_sup_right hτ))
  have hSUP' : U ⊔ T ≤ P' := hW.le_S₂.trans hSP'
  have hmapT : ∀ τ ∈ T, z * τ * z⁻¹ ∈ T.map (MulAut.conj z).toMonoidHom := fun τ hτ =>
    ⟨τ, hτ, by simp⟩
  by_cases hxS : z * t * z⁻¹ ∈ U ⊔ T
  swap
  · exact hW.false_of_conj_not_mem hcT hxS
  have hx2 : (z * t * z⁻¹) ^ 2 = 1 := by
    rw [show (z * t * z⁻¹) ^ 2 = z * t ^ 2 * z⁻¹ by rw [sq, sq]; group, h.sq_eq_one]; group
  rcases hW.mem_cases hxS with h1 | h1 | h1 | ⟨n, h1⟩
  ·
    exact hL.t_not_mem ((mem_normalizer_iff.mp hzU t).mpr h1)
  ·
    exact hzS (hW.le_S₂ (hL.muOne_mem_sup_of_conj hS hc hW.mu hK hμ hP'2 hSUP' hzP' h1))
  ·
    have hzTS : ∀ τ ∈ T, z * τ * z⁻¹ ∈ U ⊔ T := by
      intro τ hτ
      by_contra hh
      have hhS₂ := hcT τ hτ
      obtain ⟨-, hhw⟩ := hW.conj_of_not_mem hhS₂ hh
      have hhx : (z * τ * z⁻¹) * (z * t * z⁻¹) = (z * t * z⁻¹) * (z * τ * z⁻¹) :=
        hW.commute_of_mem_map (hmapT τ hτ)
      have h2 : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ ∈ U₁ := by
        rw [show (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ =
          ((z * τ * z⁻¹) * (z * t * z⁻¹ * w⁻¹) * (z * τ * z⁻¹)⁻¹) *
            ((z * τ * z⁻¹) * w * (z * τ * z⁻¹)⁻¹ * t⁻¹) by group]
        exact mul_mem (hW.conj_U₁ hhS₂ h1) hhw
      have hconj : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ = z * t * z⁻¹ := by
        rw [hhx]; group
      rw [hconj] at h2
      have htw : t * w⁻¹ ∉ U₁ := fun h' => hW.w_not_mem (by
        have h3 := hL.muOne_mem_T₁_of_mem_T hS h' (mul_mem hW.t_mem (inv_mem hW.w_mem))
        rw [show w = (t * w⁻¹)⁻¹ * t by group]
        exact mul_mem (inv_mem (mem_sup_left h3)) (mem_sup_right (mem_zpowers t)))
      apply htw
      rw [show t * w⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ * (z * t * z⁻¹ * w⁻¹) by group]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨c₁, hc₁T, hc₁⟩ := hL.muOneCent_exists_conj_eq hS hc hW.mu hK hμ hW.w_mem hW.w_sq
      hW.w_not_mem hW.w_cent hzTS h1
    have hc₁S : c₁ ∈ swapS₂ P U T := hW.le_S₂ (mem_sup_left (hL.U₁_le (hW.T₁_le_U₁ hc₁T)))
    have hy : s⁻¹ * c₁ * z ∈ T := by
      refine U3C1OuterLevelData.norm_mem_T_of_commute hS hP'2
        ((le_sup_right : T ≤ U ⊔ T).trans hSUP')
        (mul_mem (mul_mem (inv_mem (hSP' hW.s_mem_S₂)) (hSP' hc₁S)) hzP') ?_
      have e : (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ = t := by
        rw [show (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ =
          s⁻¹ * (c₁ * (z * t * z⁻¹) * c₁⁻¹) * s by group, hc₁, ← hW.conj_t]
        group
      calc (s⁻¹ * c₁ * z) * t =
            (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ * (s⁻¹ * c₁ * z) := by group
        _ = t * (s⁻¹ * c₁ * z) := by rw [e]
    apply hzS
    rw [show z = c₁⁻¹ * s * (s⁻¹ * c₁ * z) by group]
    exact mul_mem (mul_mem (inv_mem hc₁S) hW.s_mem_S₂) (hW.le_S₂ (mem_sup_right hy))
  ·
    have hxv : z * t * z⁻¹ * (t * w)⁻¹ ∈ U₁ := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exfalso
        rw [← two_mul, pow_mul, hx2, one_pow, one_mul] at h1
        have h1' : t * w ∈ U₁ := by simpa using inv_mem h1
        exact hW.tw_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS h1' hW.tw_mem))
      · rwa [pow_succ, pow_mul, hx2, one_pow, one_mul] at h1
    obtain ⟨W', hW'T₁, -, -, hW'ab, -, -, hW'iff⟩ :=
      h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
    have hmem : ∀ y ∈ szT₁ L T, z * y * z⁻¹ ∈ W' ⊔ V := by
      intro y hy
      have hyU : z * y * z⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hzU y).mp (hW.T₁_le_U₁ hy)
      have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
      refine hL.muOne_mem_sup_of_commute_inv hS hc hW.mu hK hμ hW.tw_mem
        (fun r hr => hW.tw_inv hr) hW'iff hxv hyU ?_
      calc z * y * z⁻¹ * (z * t * z⁻¹) = z * (y * t) * z⁻¹ := by group
        _ = z * (t * y) * z⁻¹ := by rw [hyt]
        _ = z * t * z⁻¹ * (z * y * z⁻¹) := by group
    have hW'VN : W' ≤ normalizer (V : Set G) := fun y hy =>
      hL.muOne_T₁_le_normalizer hS (hW'T₁ hy)
    have hab : ∀ a ∈ W' ⊔ V, ∀ b ∈ W' ⊔ V, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hW'VN ha
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hW'VN hb
      have c1 : a₁ * b₂ = b₂ * a₁ := hL.muOne_T₁_comm hS (hW'T₁ ha₁) hb₂
      have c2 : a₂ * b₁ = b₁ * a₂ := (hL.muOne_T₁_comm hS (hW'T₁ hb₁) ha₂).symm
      have c3 : a₁ * b₁ = b₁ * a₁ := hW'ab a₁ ha₁ b₁ hb₁
      have c4 : a₂ * b₂ = b₂ * a₂ := hS.conf.comm a₂ ha₂ b₂ hb₂
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [c2]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
        _ = (b₁ * a₁) * (b₂ * a₂) := by rw [c3, c4]
        _ = b₁ * (a₁ * b₂) * a₂ := by group
        _ = b₁ * (b₂ * a₁) * a₂ := by rw [c1]
        _ = b₁ * b₂ * (a₁ * a₂) := by group
    have hT₁ab : ∀ a ∈ szT₁ L T, ∀ b ∈ szT₁ L T, a * b = b * a := by
      intro a ha b hb
      have e := hab _ (hmem a ha) _ (hmem b hb)
      have e' : z * (a * b) * z⁻¹ = z * (b * a) * z⁻¹ := by
        calc z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
          _ = (z * b * z⁻¹) * (z * a * z⁻¹) := e
          _ = z * (b * a) * z⁻¹ := by group
      simpa using e'
    have hle := h.card_le_of_comm_of_card_sylow hS2 (le_refl (szT₁ L T)) hT₁ab
    rw [hT₁card] at hle
    have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
    have hq4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    have : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end U3C1OuterSwapHigh

theorem u3C1GmsSylowInput_of_char (hC : U3C1GmsCharInput) :
    U3C1GmsSylowInput :=
  fun G _ _ L f t T R₂ D d V U U₁ w s P hW _ =>
    hW.exists_sylow_of_char (hC G L f t T R₂ D d V U U₁ w s P hW)

end CFSG.SeitzReduction.RankOne
