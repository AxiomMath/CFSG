module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocFac
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocSkel
public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeMat

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Norm

theorem mixLoc_norm_of_gens {G : Type} [Group G] [Finite G] (X T₁ T₂ : Subgroup G) (s : G)
    (h₁ : ∀ a ∈ T₁, ∀ x ∈ X, a * x * a⁻¹ ∈ X) (h₂ : ∀ a ∈ T₂, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (h₃ : ∀ x ∈ X, s * x * s⁻¹ ∈ X) :
    ∀ h ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
  have hle : T₁ ⊔ T₂ ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le (sup_le (fun a ha => Subgroup.mem_normalizer_fintype (fun n hn => h₁ a ha n hn))
      (fun a ha => Subgroup.mem_normalizer_fintype (fun n hn => h₂ a ha n hn))) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype (fun n hn => h₃ n hn)
  intro h hh x hx
  exact (Subgroup.mem_normalizer_iff.1 (hle hh) x).1 hx

end Norm

section CaseB

variable {G : Type} [Group G] [Finite G]

theorem mixCfg_b {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (h3 : q₁ % 4 = 3) (h1 : q₂ % 4 = 1) :
    ∃ (u : G) (H : Subgroup G) (w₁ w₂ : G) (φ₁ : SL2 F₁ →* G) (φ₂ : SL2 F₂ →* G),
      Ch6MixCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q₁ q₂ z u K₁ K₂ H w₁ w₂ ∧
        Function.Injective φ₁ ∧ φ₁.range = K₁ ∧ MixCoord2 φ₂ z u w₂ K₂ H := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card hodd₁
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card hodd₂
  have hzord : orderOf z = 2 := hSet.central.1
  have htt : t * t = 1 := hRem.sq
  have hzz : z * z = 1 := t2C_zz hSet
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨φ₁, hinj₁, hrange₁, hneg₁, hτ₁, hsq₁⟩ :=
    exists_coords0 h2₁ hzord hSet.z_mem₁ htt e₁ g₁ hact₁
  obtain ⟨φ₂, hinj₂, hrange₂, hneg₂, hτ₂, hsq₂⟩ :=
    exists_coords0 h2₂ hzord hSet.z_mem₂ htt e₂ g₂ hact₂
  have hg2₁ := sq_eq_neg_det_of_slConj_sq g₁ hns₁ hsq₁
  have hg2₂ := sq_eq_neg_det_of_slConj_sq g₂ hns₂ hsq₂
  obtain ⟨W₁, V₁, A₁, hN₁⟩ := negFactor_exists hSet.card₁ h3 g₁ hg2₁
  have hq₂F : Nat.card F₂ % 4 = 1 := by rw [hSet.card₂]; exact h1
  obtain ⟨ι, hι⟩ := exists_unit_sqrt_negOne hq₂F
  have hN₂ : MixFactor (q₂ - 1) g₂ (sl2D ι) (sl2W F₂) (adjSL g₂) := by
    have := mixFactor_split h2₂ hι g₂ hg2₂
    rwa [hSet.card₂] at this
  have sk := mixSkel_of_coords hSet hRem hinj₁ hrange₁ hneg₁ hτ₁ hinj₂ hrange₂ hneg₂ hτ₂
    hN₁.toMix hN₂
  have hq₂ : 4 ≤ q₂ := by
    have h1' : 1 < Nat.card F₂ := Finite.one_lt_card
    rw [hSet.card₂] at h1'
    omega
  have hC₁le : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ centralizer ({z} : Set G) :=
    Subgroup.map_subtype_le _
  have hcfg := sk.toCh6MixCfg hSet.five hq₂ hzz (t2C_z_ne hSet) hSet.comm hSet.inter_eq.le
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hC₁le hx)) hSet.le_residual
    (fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c hc)
    (fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c hc) hSet.index_two
  have hcent := centralizer_sl2D_eq h2₂ hι
  have hmem₁ : ∀ M : SL2 F₁, φ₁ M ∈ K₁ := fun M => hrange₁ ▸ ⟨M, rfl⟩
  have hmem₂ : ∀ M : SL2 F₂, φ₂ M ∈ K₂ := fun M => hrange₂ ▸ ⟨M, rfl⟩
  have hc12 : ∀ (a : SL2 F₁) (b : SL2 F₂), φ₁ a * φ₂ b = φ₂ b * φ₁ a := fun a b =>
    hSet.comm _ (hmem₁ a) _ (hmem₂ b)
  have hs : ∀ x : SL2 F₂, (φ₁ A₁ * φ₂ (adjSL g₂) * t) * φ₂ x * (φ₁ A₁ * φ₂ (adjSL g₂) * t)⁻¹ =
      φ₂ (slConj (diagGL 1 (Matrix.GeneralLinearGroup.det g₂)) x) := by
    intro x
    have e : (φ₁ A₁ * φ₂ (adjSL g₂) * t) * φ₂ x * (φ₁ A₁ * φ₂ (adjSL g₂) * t)⁻¹ =
        φ₁ A₁ * (φ₂ (adjSL g₂) * (t * φ₂ x * t⁻¹) * (φ₂ (adjSL g₂))⁻¹) * (φ₁ A₁)⁻¹ := by group
    rw [e, hτ₂]
    have e2 : φ₂ (adjSL g₂) * φ₂ (slConj g₂ x) * (φ₂ (adjSL g₂))⁻¹ =
        φ₂ (slConj (diagGL 1 (Matrix.GeneralLinearGroup.det g₂)) x) := by
      rw [← adjSL_conj g₂ x, map_mul, map_mul, map_inv]
    rw [e2, hc12 A₁, mul_inv_cancel_right]
  have hxW : ∀ x : SL2 F₂, (φ₁ W₁ * φ₂ (sl2D ι)) * φ₂ x * (φ₁ W₁ * φ₂ (sl2D ι))⁻¹ =
      φ₂ (slConj (dNeg F₂) x) := by
    intro x
    have e : (φ₁ W₁ * φ₂ (sl2D ι)) * φ₂ x * (φ₁ W₁ * φ₂ (sl2D ι))⁻¹ =
        φ₁ W₁ * (φ₂ (sl2D ι) * φ₂ x * (φ₂ (sl2D ι))⁻¹) * (φ₁ W₁)⁻¹ := by group
    rw [e, ← map_mul, ← map_inv, ← map_mul, slConj_sqrt_negOne ι hι x, hc12 W₁,
      mul_inv_cancel_right]
  have hnorm : ∀ (A : Subgroup (SL2 F₂)), (∀ x ∈ A, slConj (diagGL 1 (Matrix.GeneralLinearGroup.det g₂)) x ∈ A) →
      (∀ b ∈ tSub F₂, ∀ x ∈ A, b * x * b⁻¹ ∈ A) →
      ∀ h ∈ (Subgroup.centralizer ({W₁} : Set (SL2 F₁))).map φ₁ ⊔
          (Subgroup.centralizer ({sl2D ι} : Set (SL2 F₂))).map φ₂ ⊔
          Subgroup.zpowers (φ₁ A₁ * φ₂ (adjSL g₂) * t), ∀ x ∈ A.map φ₂, h * x * h⁻¹ ∈ A.map φ₂ := by
    intro A hD hT
    refine mixLoc_norm_of_gens (A.map φ₂) _ _ _ ?_ ?_ ?_
    · rintro a ⟨b, -, rfl⟩ x hx
      have hxK : x ∈ K₂ := hrange₂ ▸ Subgroup.map_le_range _ _ hx
      rw [hSet.comm _ (hmem₁ b) x hxK, mul_inv_cancel_right]
      exact hx
    · rintro a ⟨b, hb, rfl⟩ x ⟨ξ, hξ, rfl⟩
      rw [hcent] at hb
      refine ⟨b * ξ * b⁻¹, hT b hb ξ hξ, ?_⟩
      simp [map_mul, map_inv]
    · rintro x ⟨ξ, hξ, rfl⟩
      rw [hs]
      exact ⟨_, hD ξ hξ, rfl⟩
  refine ⟨φ₁ W₁ * φ₂ (sl2D ι), _, φ₁ V₁, φ₂ (sl2W F₂), φ₁, φ₂, hcfg, hinj₁, hrange₁, ?_⟩
  exact
    { inj := hinj₂
      range := hrange₂
      neg := hneg₂
      w := rfl
      H_inf := by rw [sk.H_inf_K₂ hSet.comm, hcent]
      H_norm_u := hnorm (uSub F₂) (slConj_diag_uSub _ _) tSub_normalizes_uSub
      H_norm_l := hnorm (lSub F₂) (slConj_diag_lSub _ _) tSub_normalizes_lSub
      hu := hxW }

end CaseB

end CFSG.GH74.GLS.Stage4.Rest
