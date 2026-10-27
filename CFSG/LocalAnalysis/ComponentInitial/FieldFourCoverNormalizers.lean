module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverLift
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Subgroup LinearFlag CFSG.LieType.Chevalley
open scoped IsMulCommutative Pointwise

theorem commute_of_sq_eq_one {X : Type*} [Group X] {H : Subgroup X}
    (h : ∀ x ∈ H, x ^ 2 = 1) {a b : X} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have hinv : ∀ x ∈ H, x⁻¹ = x := fun x hx => by
    rw [inv_eq_iff_mul_eq_one, ← sq, h x hx]
  calc a * b = (a * b)⁻¹ := (hinv _ (mul_mem ha hb)).symm
    _ = b * a := by rw [mul_inv_rev, hinv a ha, hinv b hb]

theorem card_SL2_of_card {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) :
    Nat.card (SL2 k) = 60 := by
  have := charP_two_of_card hk
  obtain ⟨-, h, -⟩ := linear_order (K := k) 2 4 hk (n := 2) le_rfl
  rw [h]
  simp

theorem parabolic_part {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {X : Type} [Group X] [Finite X] {π : X →* projectiveSL 3 k} (hπ : Function.Surjective π)
    (hCZ : π.ker ≤ center X) (hC : CFSG.IsElementaryAbelian 2 π.ker)
    (hHsq : ∀ j : Fin 2, ∀ x ∈ (projRad k j).comap π, x ^ 2 = 1) (i : Fin 2) :
    let Q := (leviProj k i).range.comap π
    let Ti := ((sl2Unip k).map (leviProj k i)).comap π
    let Perm : (SL2 k →* X) → Prop := fun σ => Function.Injective σ ∧
      (∀ B, σ B ∈ normalizer ((projRad k i).comap π : Set X)) ∧
      (∀ B, π (σ B) = leviProj k i B) ∧
      (projRad k i).comap π ⊔ σ.range = normalizer ((projRad k i).comap π : Set X) ∧
      (projRad k i).comap π ⊓ σ.range = ⊥
    (∃ σ, Perm σ) ∧
      Nat.card (normalizer ((projRad k i).comap π : Set X)) = 960 * Nat.card π.ker ∧
      CFSG.IsElementaryAbelian 2 Ti ∧ π.ker ≤ Ti ∧
      (∃ S : Sylow 2 Q, (S : Subgroup Q) = Ti.subgroupOf Q) ∧
      ∀ lam : Ti →* π.ker, (∀ c : π.ker, lam (Subgroup.inclusion (π.ker_le_comap _) c) = c) →
        let τ : Q →* π.ker := (lam.comp (Subgroup.subgroupOfEquivOfLe
          (Subgroup.comap_mono (Subgroup.map_le_range _ _))).toMonoidHom).transfer
        (∀ c : π.ker, τ (Subgroup.inclusion (π.ker_le_comap _) c) = c) ∧
        ∃ e : τ.ker ≃* (leviProj k i).range,
          (∀ x, (e x : projectiveSL 3 k) = π ((x : Q) : X)) ∧
          Perm (Q.subtype.comp (τ.ker.subtype.comp
            (e.symm.toMonoidHom.comp (leviProj k i).rangeRestrict))) := by
  intro Q Ti Perm
  have hC2 : ∀ c ∈ π.ker, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := π.ker) c hc
  have hδ : Function.Injective (leviProj k i) := leviProj_injective i
  have hN := normalizer_projRad hk i
  have hRL := projRad_inf_range (k := k) i
  have hTQ : Ti ≤ Q := Subgroup.comap_mono (Subgroup.map_le_range _ _)
  have hCT : π.ker ≤ Ti := π.ker_le_comap _
  have hTsq : ∀ x ∈ Ti, x ^ 2 = 1 := by
    have hj := exists_map_sl2Unip_le (k := k) i
    obtain ⟨j, hj⟩ := hj
    exact fun x hx => hHsq j x (Subgroup.comap_mono hj hx)
  have hTel : CFSG.IsElementaryAbelian 2 Ti := isElementaryAbelian_of_sq_eq_one hTsq
  have hcardL : Nat.card (leviProj k i).range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hδ).toEquiv, card_SL2_of_card hk]
  have hcardQ : Nat.card Q = 60 * Nat.card π.ker := by
    rw [card_comap_of_surjective hπ, hcardL]
  have hcardT : Nat.card Ti = 4 * Nat.card π.ker := by
    rw [card_comap_of_surjective hπ, Subgroup.card_map_of_injective hδ, card_sl2Unip, hk]
  have hCpos : 0 < Nat.card π.ker := Nat.card_pos
  have hidx : (Ti.subgroupOf Q).index = 15 := by
    have h := (Ti.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, hcardT, hcardQ] at h
    have h' : 4 * Nat.card π.ker * (Ti.subgroupOf Q).index = 4 * Nat.card π.ker * 15 := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have hodd : Odd (Ti.subgroupOf Q).index := by
    rw [hidx]
    decide
  have hsection : ∀ lam : Ti →* π.ker, (∀ c : π.ker, lam (Subgroup.inclusion hCT c) = c) →
      (∀ c : π.ker, (lam.comp (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer
          (Subgroup.inclusion (π.ker_le_comap _) c) = c) ∧
        ∃ e : ((lam.comp (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer).ker ≃*
            (leviProj k i).range,
          (∀ x, (e x : projectiveSL 3 k) = π ((x : Q) : X)) ∧
          Perm (Q.subtype.comp (((lam.comp
            (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer).ker.subtype.comp
              (e.symm.toMonoidHom.comp (leviProj k i).rangeRestrict))) := by
    intro lam hlam
    have hdata := transfer_retraction hπ hCZ hC2 (leviProj k i).range hTQ hCT hodd lam hlam
    obtain ⟨hτC, e, he⟩ := hdata
    refine ⟨hτC, e, he, ?_⟩
    have hs : ∀ B, π ((Q.subtype.comp (((lam.comp
        (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer).ker.subtype.comp
          (e.symm.toMonoidHom.comp (leviProj k i).rangeRestrict))) B) = leviProj k i B := by
      intro B
      have h := he (e.symm ((leviProj k i).rangeRestrict B))
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    have hlift := lift_complement hπ hδ hN hRL _ hs
    exact ⟨hlift.1, hlift.2.1, hs, hlift.2.2.1, hlift.2.2.2⟩
  have hex : ∃ σ, Perm σ := by
    have hret := exists_retraction hCT hTel
    obtain ⟨lam, hlam⟩ := hret
    have h := hsection lam hlam
    obtain ⟨-, e, -, hPerm⟩ := h
    exact ⟨_, hPerm⟩
  have hcardN : Nat.card (normalizer ((projRad k i).comap π : Set X)) =
      960 * Nat.card π.ker := by
    obtain ⟨σ, hinj, hsN, -, hsup, hinf⟩ := hex
    rw [card_normalizer_of_lift σ hinj hsN hsup hinf, card_comap_of_surjective hπ, card_projRad,
      hk, card_SL2_of_card hk]
    ring
  have hP : IsPGroup 2 (Ti.subgroupOf Q) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 Ti).of_equiv (Subgroup.subgroupOfEquivOfLe hTQ).symm
  have hnd : ¬ 2 ∣ (Ti.subgroupOf Q).index := by
    rw [hidx]
    decide
  exact ⟨hex, hcardN, hTel, hCT, ⟨hP.toSylow hnd, IsPGroup.toSylow_coe hP hnd⟩,
    fun lam hlam => hsection lam hlam⟩

theorem field_four_central_two_cover_parabolic_normalizers
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {X : Type} [Group X] [Finite X] (π : X →* projectiveSL 3 k) (hπ : Function.Surjective π)
    (hCZ : π.ker ≤ center X) (hC : CFSG.IsElementaryAbelian 2 π.ker) :
    let T := (projUnip k).comap π
    let H : Fin 2 → Subgroup X := fun i => (projRad k i).comap π
    (∀ i, CFSG.IsElementaryAbelian 2 (H i) ∧ Nat.card (H i) = 16 * Nat.card π.ker) ∧
    (H 0 : Set X) * (H 1 : Set X) = T ∧ (∃ S : Sylow 2 X, (S : Subgroup X) = T) ∧
    Nat.card T = 64 * Nat.card π.ker ∧
    H 0 ⊓ H 1 = (center T).map T.subtype ∧
    (center T).map T.subtype = (projCenterW k).comap π ∧
    Nat.card ((projCenterW k).comap π) = 4 * Nat.card π.ker ∧
    ∀ i : Fin 2,
      let Q := (leviProj k i).range.comap π
      let Ti := ((sl2Unip k).map (leviProj k i)).comap π
      let Perm : (SL2 k →* X) → Prop := fun σ => Function.Injective σ ∧
        (∀ B, σ B ∈ normalizer (H i : Set X)) ∧ (∀ B, π (σ B) = leviProj k i B) ∧
        H i ⊔ σ.range = normalizer (H i : Set X) ∧ H i ⊓ σ.range = ⊥
      (∃ σ, Perm σ) ∧ Nat.card (normalizer (H i : Set X)) = 960 * Nat.card π.ker ∧
      CFSG.IsElementaryAbelian 2 Ti ∧ π.ker ≤ Ti ∧
      (∃ S : Sylow 2 Q, (S : Subgroup Q) = Ti.subgroupOf Q) ∧
      ∀ lam : Ti →* π.ker, (∀ c : π.ker, lam (Subgroup.inclusion (π.ker_le_comap _) c) = c) →
        let τ : Q →* π.ker := (lam.comp (Subgroup.subgroupOfEquivOfLe
          (Subgroup.comap_mono (Subgroup.map_le_range _ _))).toMonoidHom).transfer
        (∀ c : π.ker, τ (Subgroup.inclusion (π.ker_le_comap _) c) = c) ∧
        ∃ e : τ.ker ≃* (leviProj k i).range,
          (∀ x, (e x : projectiveSL 3 k) = π ((x : Q) : X)) ∧
          Perm (Q.subtype.comp (τ.ker.subtype.comp
            (e.symm.toMonoidHom.comp (leviProj k i).rangeRestrict))) := by
  classical
  intro T H
  have hC2 : ∀ c ∈ π.ker, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := π.ker) c hc
  have hHsq : ∀ j : Fin 2, ∀ x ∈ (projRad k j).comap π, x ^ 2 = 1 := fun j =>
    sq_eq_one_of_comap hπ hCZ hC2 (fun r hr => sq_eq_one_of_mem_projRad hk j hr)
      (fun r hr s hs => commute_of_mem_projRad j hr hs)
      (fun r hr s hs hr1 hs1 => projRad_transitive j hr hs hr1 hs1)
      (exists_independent_projRad hk j)
  have hHcard : ∀ j : Fin 2, Nat.card (H j) = 16 * Nat.card π.ker := fun j => by
    change Nat.card ((projRad k j).comap π) = _
    rw [card_comap_of_surjective hπ, card_projRad, hk]
  have hHT : ∀ j : Fin 2, H j ≤ T := fun j => Subgroup.comap_mono (projRad_le_projUnip j)
  have hTmul : (H 0 : Set X) * (H 1 : Set X) = T := by
    ext x
    constructor
    · rintro ⟨h₀, hh₀, h₁, hh₁, rfl⟩
      exact mul_mem (hHT 0 hh₀) (hHT 1 hh₁)
    · intro hx
      have hdec := exists_mul_eq_of_mem_projUnip (k := k) hx
      obtain ⟨r₁, hr₁, r₂, hr₂, hr⟩ := hdec
      obtain ⟨h₀, rfl⟩ := hπ r₁
      refine ⟨h₀, hr₁, h₀⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
      change π (h₀⁻¹ * x) ∈ projRad k 1
      rw [map_mul, map_inv, ← hr, inv_mul_cancel_left]
      exact hr₂
  have hSyl : ∃ S : Sylow 2 X, (S : Subgroup X) = T := by
    have := charP_two_of_card hk
    have hlin := linear_order (K := k) 2 4 hk (n := 3) (by norm_num)
    obtain ⟨-, -, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hlin
    have hCp : IsPGroup 2 π.ker := CFSG.IsElementaryAbelian.isPGroup 2 π.ker
    refine ⟨S.comapOfKerIsPGroup π hCp (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top), ?_⟩
    rw [Sylow.coe_comapOfKerIsPGroup, hS, ← projUnip_eq_projUnitriangular]
  have hTcard : Nat.card T = 64 * Nat.card π.ker := by
    change Nat.card ((projUnip k).comap π) = _
    rw [card_comap_of_surjective hπ, card_projUnip, hk]
  have hinf : H 0 ⊓ H 1 = (projCenterW k).comap π := by
    change (projRad k 0).comap π ⊓ (projRad k 1).comap π = _
    rw [← Subgroup.comap_inf, projRad_inf_eq]
  have hcenter : (center T).map T.subtype = (projCenterW k).comap π := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzc := mem_center_iff.1 hz
      have hcomm : ∀ a b c : k, π z * proj 3 k (unipU k a b c) =
          proj 3 k (unipU k a b c) * π z := by
        intro a b c
        obtain ⟨t, ht⟩ := hπ (proj 3 k (unipU k a b c))
        have htT : t ∈ T := by
          change π t ∈ projUnip k
          rw [ht]
          exact mem_projUnip.2 ⟨a, b, c, rfl⟩
        have h := congrArg (fun y : T => π (y : X)) (hzc ⟨t, htT⟩)
        simp only [Subgroup.coe_mul, map_mul, ht] at h
        exact h.symm
      exact mem_projCenterW_of_commute z.2 (hcomm 1 0 0) (hcomm 0 1 0)
    · intro hx
      rw [← hinf] at hx
      have hxT : x ∈ T := hHT 0 hx.1
      refine ⟨⟨x, hxT⟩, mem_center_iff.2 fun g => ?_, rfl⟩
      have hg : (g : X) ∈ (H 0 : Set X) * (H 1 : Set X) := by
        rw [hTmul]
        exact g.2
      obtain ⟨h₀, hh₀, h₁, hh₁, hgh⟩ := hg
      apply Subtype.ext
      change (g : X) * x = x * g
      rw [← hgh, mul_assoc, commute_of_sq_eq_one (hHsq 1) hh₁ hx.2, ← mul_assoc,
        commute_of_sq_eq_one (hHsq 0) hh₀ hx.1, mul_assoc]
  have hWcard : Nat.card ((projCenterW k).comap π) = 4 * Nat.card π.ker := by
    rw [card_comap_of_surjective hπ, card_projCenterW, hk]
  exact ⟨fun j => ⟨isElementaryAbelian_of_sq_eq_one (hHsq j), hHcard j⟩, hTmul, hSyl, hTcard,
    hinf.trans hcenter.symm, hcenter, hWcard,
    fun i => parabolic_part hk hπ hCZ hC hHsq i⟩

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
