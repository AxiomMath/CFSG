module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6B
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6PC
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6SP
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Spl

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer L44Sylow
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (pstd sigmaSL msigma rootSL map_sigmaSL_rootSL
  map_sigmaSL_range_zero rootSL_le_pstd)
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G]

@[expose] def gam (φ : SL(4, F4) →* G) (k : Fin 3) : Subgroup G := (blockSL2 F4 3 k).range.map φ

theorem mem_gam {φ : SL(4, F4) →* G} {k : Fin 3} {x : G} :
    x ∈ gam φ k ↔ ∃ A : SL(2, F4), φ (blockSL2 F4 3 k A) = x := by
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, rfl⟩

@[expose] noncomputable def gamEquiv {φ : SL(4, F4) →* G} (hφ : Function.Injective φ)
    (k : Fin 3) : gam φ k ≃* SL(2, F4) :=
  ((Subgroup.equivMapOfInjective (blockSL2 F4 3 k).range φ hφ).symm).trans
    (MonoidHom.ofInjective (blockSL2_injective k)).symm

theorem gamEquiv_apply_mk {φ : SL(4, F4) →* G} (hφ : Function.Injective φ) (k : Fin 3)
    (A : SL(2, F4)) (h : φ (blockSL2 F4 3 k A) ∈ gam φ k) :
    gamEquiv hφ k ⟨φ (blockSL2 F4 3 k A), h⟩ = A := by
  have e : (gamEquiv hφ k).symm A = ⟨φ (blockSL2 F4 3 k A), h⟩ := rfl
  rw [← e, MulEquiv.apply_symm_apply]


theorem map_map_conj {H : Type} [Group H] (f : G →* H) (U : Subgroup G) (w : G) :
    (U.map (MulAut.conj w).toMonoidHom).map f =
      (U.map f).map (MulAut.conj (f w)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, by simp [MulAut.conj_apply]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨w * u * w⁻¹, ⟨u, hu, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem le_of_gen_conj {N Γ U : Subgroup G} {w v₁ : G} (hU : U ≤ N) (hv : v₁ ∈ N)
    (hgen : Γ ≤ U ⊔ U.map (MulAut.conj w).toMonoidHom)
    (hconj : ∀ u ∈ U, w * u * w⁻¹ = v₁⁻¹ * u * v₁) : Γ ≤ N := by
  refine hgen.trans (sup_le hU ?_)
  rintro _ ⟨u, hu, rfl⟩
  show w * u * w⁻¹ ∈ N
  rw [hconj u hu]
  exact N.mul_mem (N.mul_mem (N.inv_mem hv) (hU hu)) hv

end Transport

section C7


structure StdLin {G : Type} [Group G] (d : Data G) (φ : SL(4, F4) →* G) : Prop where
  inj : Function.Injective φ
  range : φ.range = d.K
  equiv : ∀ A, d.t * φ A * d.t⁻¹ = φ (sigmaSL F4 A)
  pstd : (pstd F4).map φ = d.M ⊔ d.Y

namespace StdLin

variable {G : Type} [Group G] [Finite G] {d : Data G} {φ : SL(4, F4) →* G}

theorem MY_eq (hs : StdLin d φ) : d.M ⊔ d.Y = PK.map φ := by
  rw [← hs.pstd, pstd_eq_PK]

theorem Y_eq (h : d.Hyp) (hs : StdLin d φ) : d.Y = YK.map φ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_map_YK hs.inj ?_ (fun x hx y hy => h.Y_comm hx hy) (fun x hx => h.Y_sq hx)
    h.card_Y
  rw [← hs.MY_eq]
  exact le_sup_right

theorem mem_YK_iff (h : d.Hyp) (hs : StdLin d φ) {x : SL(4, F4)} : φ x ∈ d.Y ↔ x ∈ YK := by
  rw [hs.Y_eq h]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hs.inj hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_MY_decomp (hs : StdLin d φ) {x : G} (hx : x ∈ d.M ⊔ d.Y) :
    ∃ u₁ ∈ rootSL F4 1 0, ∃ u₂ ∈ rootSL F4 3 2, ∃ y ∈ YK, x = φ u₁ * φ u₂ * φ y := by
  rw [hs.MY_eq] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨u₁, hu₁, u₂, hu₂, y, hy, rfl⟩ := exists_decomp_PK hp
  exact ⟨u₁, hu₁, u₂, hu₂, y, hy, by simp⟩

theorem map_conj_t (hs : StdLin d φ) (h : d.Hyp) (X : Subgroup SL(4, F4)) :
    (X.map φ).map (MulAut.conj d.t).toMonoidHom = (X.map (sigmaSL F4).toMonoidHom).map φ := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨sigmaSL F4 a, ⟨a, ha, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hs.equiv]
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨φ a, ⟨a, ha, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hs.equiv]

theorem Y_le_K_aux (h : d.Hyp) (hK : d.KLinear) : d.K₃ ≤ d.K := by
  rw [← hK.centralizer_eq]
  exact inf_le_left

theorem t_conj_v (h : d.Hyp) : d.t * d.v * d.t⁻¹ = d.v := by
  have hv : d.v ∈ d.H := h.L_le_H (d.ι_mem vSU)
  have := mem_centralizer_singleton_iff.1 hv
  calc d.t * d.v * d.t⁻¹ = d.v * d.t * d.t⁻¹ := by rw [← this]
    _ = d.v := by group

theorem v_mul_v (h : d.Hyp) : d.v * d.v = 1 := by
  show d.ι vSU * d.ι vSU = 1
  rw [← map_mul]
  have : vSU * vSU = 1 := by
    have := mul_inv_cancel vSU
    rwa [vSU_inv] at this
  rw [this, map_one]

theorem exists_weyl (h : d.Hyp) (hK : d.KLinear) (hs : StdLin d φ) :
    ∃ (A : SL(2, F4)) (y : SL(4, F4)), A 0 1 ≠ 0 ∧ A * A = 1 ∧ y ∈ YK ∧
      d.v = φ y * (φ (blockSL2 F4 3 0 A) * φ (sigmaSL F4 (blockSL2 F4 3 0 A))) := by
  have hK₁ := h.comm_M_V₂_mem_W_linear hK
  have hKY := h.M_le_normalizer_Y_linear hK
  have hK₃ : d.K₃ ≤ d.K := Y_le_K_aux h hK
  have hvK : d.v ∈ d.K := hK₃ (Data.K₂_le_K₃ Data.v_mem_K₂)
  rw [← hs.range] at hvK
  obtain ⟨g, hg⟩ := hvK
  have hg2 : g * g = 1 := by
    apply hs.inj
    rw [map_mul, hg, v_mul_v h, map_one]
  have hσ : sigmaSL F4 g = g := by
    apply hs.inj
    rw [← hs.equiv, hg, t_conj_v h]
  have hvY : d.v ∈ normalizer (d.Y : Set G) := h.NHA₂_le_normalizer_Y h.v_mem_NHA₂
  have hN : ∀ y ∈ YK, g * y * g⁻¹ ∈ YK := by
    intro y hy
    rw [← hs.mem_YK_iff h]
    have hy' : φ y ∈ d.Y := (hs.mem_YK_iff h).2 hy
    have := (mem_normalizer_iff.1 hvY _).1 hy'
    rwa [← hg, ← map_inv, ← map_mul, ← map_mul] at this
  have hgP : g ∉ PK := by
    intro hgPK
    have hvMY : d.v ∈ d.M ⊔ d.Y := by
      rw [hs.MY_eq]
      exact ⟨g, hgPK, hg⟩
    have hsub : d.V₃ ≤ d.V₃.map (MulAut.conj d.v).toMonoidHom := fun x hx => by
      rw [mem_map_conj_iff]
      have := h.V₃_cen_MY_lin hK₁ hKY x hx d.v⁻¹ (inv_mem hvMY)
      have h2 : d.v⁻¹ * x * d.v = (d.v⁻¹ * x * d.v⁻¹⁻¹ * x⁻¹) * x := by group
      rw [h2]
      exact d.V₃.mul_mem (h.Y_le_V₃ this) hx
    have h3 := h.V₃_inf_conj_V₃ hK₁
    rw [inf_eq_left.mpr hsub] at h3
    have hc := h.card_V₃ hK₁
    rw [h3, h.card_Y] at hc
    norm_num at hc
  obtain ⟨A, hA01, hAA, y, hy, hgy⟩ := exists_weyl_of_involution hN hg2 hσ hgP
  refine ⟨A, y, hA01, hAA, hy, ?_⟩
  rw [← hg, hgy, map_mul, map_mul]

theorem X₂_le_M' (h : d.Hyp) : d.X₂ ≤ d.M := fun z hz =>
  Subgroup.mem_inf.2 ⟨h.A₁_le_D₁ (Data.Hyp.X₂_le_A₁ hz),
    mem_centralizer_singleton_iff.2 (Data.Hyp.X₂_comm_e₂ hz)⟩

end StdLin

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem exists_B_lin (h : d.Hyp) (hK : d.KLinear) (hD : d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    ∃ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ (∀ x ∈ B, x * x = 1) ∧
      Nat.card B = 2 ^ 12 ∧ ∀ p ∈ d.D₁ ⊔ d.D₂, ∀ b ∈ B, p * b * p⁻¹ ∈ B := by
  have hK₁ := h.comm_M_V₂_mem_W_linear hK
  have hKY := h.M_le_normalizer_Y_linear hK
  obtain ⟨φ, hinj, hrange, hequiv, hpstd⟩ := h.exists_standard_position hK
  have hs : StdLin d φ := ⟨hinj, hrange, hequiv, hpstd⟩
  obtain ⟨A, y, hA01, hAA, hy, hv⟩ := hs.exists_weyl h hK
  obtain ⟨A', hA'⟩ : ∃ A' : SL(2, F4), blockSL2 F4 3 2 A' = sigmaSL F4 (blockSL2 F4 3 0 A) := by
    have : sigmaSL F4 (blockSL2 F4 3 0 A) ∈ (blockSL2 F4 3 2).range := by
      rw [← map_sigmaSL_range_zero F4]
      exact Subgroup.mem_map_of_mem (sigmaSL F4).toMonoidHom (MonoidHom.mem_range.2 ⟨A, rfl⟩)
    exact MonoidHom.mem_range.1 this
  set w₁ : G := φ (blockSL2 F4 3 0 A) with hw₁def
  set w₂ : G := φ (sigmaSL F4 (blockSL2 F4 3 0 A)) with hw₂def
  set y₀ : G := φ y with hy₀def
  have hy₀Y : y₀ ∈ d.Y := (hs.mem_YK_iff h).2 hy
  have hv' : d.v = y₀ * (w₁ * w₂) := hv
  set Γ₁ : Subgroup G := gam φ 0 with hΓ₁def
  set Γ₂ : Subgroup G := gam φ 2 with hΓ₂def
  set U₁ : Subgroup G := (rootSL F4 1 0).map φ with hU₁def
  set U₂ : Subgroup G := (rootSL F4 3 2).map φ with hU₂def
  have hw₁Γ : w₁ ∈ Γ₁ := mem_gam.2 ⟨A, rfl⟩
  have hw₂Γ : w₂ ∈ Γ₂ := mem_gam.2 ⟨A', by rw [hA']⟩
  have hw₁sq : w₁ * w₁ = 1 := by
    rw [hw₁def, ← map_mul, ← map_mul, hAA, map_one, map_one]
  have hw₂sq : w₂ * w₂ = 1 := by
    rw [hw₂def, ← map_mul, ← map_mul, ← map_mul, hAA, map_one, map_one, map_one]
  have hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨A₁, rfl⟩ := mem_gam.1 ha
    obtain ⟨B₂, rfl⟩ := mem_gam.1 hb
    rw [← map_mul, ← map_mul, blockSL2_comm]
  have hU₁Γ : U₁ ≤ Γ₁ := Subgroup.map_mono rootSL_le_range₀
  have hU₂Γ : U₂ ≤ Γ₂ := Subgroup.map_mono rootSL_le_range₂
  have hU₁MY : U₁ ≤ d.M ⊔ d.Y := by
    rw [← hs.pstd]
    exact Subgroup.map_mono (rootSL_le_pstd F4 (by decide))
  have hU₂MY : U₂ ≤ d.M ⊔ d.Y := by
    rw [← hs.pstd]
    exact Subgroup.map_mono (rootSL_le_pstd F4 (by decide))
  have hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom := by
    have := Subgroup.map_mono (f := φ) (range₀_le_sup hA01)
    rw [Subgroup.map_sup, map_map_conj] at this
    exact this
  have hconjU : U₁.map (MulAut.conj d.t).toMonoidHom = U₂ := by
    rw [hU₁def, hs.map_conj_t h, map_sigmaSL_rootSL]
    rfl
  have hconjΓ : Γ₁.map (MulAut.conj d.t).toMonoidHom = Γ₂ := by
    rw [hΓ₁def, gam, hs.map_conj_t h, map_sigmaSL_range_zero]
    rfl
  have hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj d.t).toMonoidHom) hgen₁
    rw [Subgroup.map_sup, map_map_conj, hconjU, hconjΓ] at h1
    have hw : (MulAut.conj d.t).toMonoidHom w₁ = w₂ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hw₁def, hs.equiv]
    rw [hw] at h1
    exact h1
  have hΓ₁Y : Γ₁ ≤ normalizer (d.Y : Set G) := by
    intro g hg
    obtain ⟨B, rfl⟩ := mem_gam.1 hg
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ YK, φ x' = x := by
      rw [hs.Y_eq h] at hx
      exact hx
    have e : φ (blockSL2 F4 3 0 B) * φ x' * (φ (blockSL2 F4 3 0 B))⁻¹ =
        φ (blockSL2 F4 3 0 B * x' * (blockSL2 F4 3 0 B)⁻¹) := by simp
    rw [e]
    exact (hs.mem_YK_iff h).2 (blockSL2_conj_YK₀ B hx')
  have hΓ₂Y : Γ₂ ≤ normalizer (d.Y : Set G) := by
    intro g hg
    obtain ⟨B, rfl⟩ := mem_gam.1 hg
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ YK, φ x' = x := by
      rw [hs.Y_eq h] at hx
      exact hx
    have e : φ (blockSL2 F4 3 2 B) * φ x' * (φ (blockSL2 F4 3 2 B))⁻¹ =
        φ (blockSL2 F4 3 2 B * x' * (blockSL2 F4 3 2 B)⁻¹) := by simp
    rw [e]
    exact (hs.mem_YK_iff h).2 (blockSL2_conj_YK₂ B hx')
  set N : Subgroup G := normalizer (d.D₂ : Set G) with hNdef
  have hMY_N : d.M ⊔ d.Y ≤ N := (h.MY_le_normDY_lin hKY hD).trans inf_le_left
  have hvN : d.v ∈ N := h.v_mem_normalizer_D₂
  have hv₁N : w₁ * w₂ ∈ N := by
    have : w₁ * w₂ = y₀⁻¹ * d.v := by rw [hv']; group
    rw [this]
    exact N.mul_mem (N.inv_mem (d.D₂.le_normalizer (h.Y_le_D₂ hy₀Y))) hvN
  have hconj₁ : ∀ u ∈ U₁, w₁ * u * w₁⁻¹ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by
    intro u hu
    have hu' : w₁⁻¹ * u * w₁ ∈ Γ₁ :=
      Γ₁.mul_mem (Γ₁.mul_mem (Γ₁.inv_mem hw₁Γ) (hU₁Γ hu)) hw₁Γ
    have hc := hcomm _ hu' _ hw₂Γ
    have hinv₁ : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁sq
    calc w₁ * u * w₁⁻¹ = w₁⁻¹ * u * w₁ := by rw [hinv₁]
      _ = w₂⁻¹ * (w₁⁻¹ * u * w₁ * w₂) := by rw [hc]; group
      _ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by group
  have hconj₂ : ∀ u ∈ U₂, w₂ * u * w₂⁻¹ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by
    intro u hu
    have hc : w₁ * u = u * w₁ := hcomm _ hw₁Γ _ (hU₂Γ hu)
    have hinv₂ : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw₂sq
    calc w₂ * u * w₂⁻¹ = w₂⁻¹ * u * w₂ := by rw [hinv₂]
      _ = w₂⁻¹ * (w₁⁻¹ * u * w₁) * w₂ := by
        rw [show w₁⁻¹ * u * w₁ = u by rw [mul_assoc, ← hc]; group]
      _ = (w₁ * w₂)⁻¹ * u * (w₁ * w₂) := by group
  have hΓ₁N : Γ₁ ≤ N := le_of_gen_conj (hU₁MY.trans hMY_N) hv₁N hgen₁ hconj₁
  have hΓ₂N : Γ₂ ≤ N := le_of_gen_conj (hU₂MY.trans hMY_N) hv₁N hgen₂ hconj₂
  have hΓ₁' : Γ₁ ≤ ModSplit.normDY d.D₂ d.Y := le_inf hΓ₁N hΓ₁Y
  have hΓ₂' : Γ₂ ≤ ModSplit.normDY d.D₂ d.Y := le_inf hΓ₂N hΓ₂Y
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY2 : IsPGroup 2 ↥(d.M ⊔ d.Y) := IsPGroup.of_card (n := 12) (h.card_M_sup_Y hK)
  have hp₁ : IsPGroup 2 ↥U₁ := hMY2.to_le hU₁MY
  have hp₂ : IsPGroup 2 ↥U₂ := hMY2.to_le hU₂MY
  have hfix : ∀ x ∈ d.D₂, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ d.Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ d.Y) → x ∈ d.Y := by
    intro x hx h₁ h₂
    refine h.fixed_D₂_Y hx (fun k hk => ?_)
    have hΓ₁C : Γ₁ ≤ centModSub d.Y x := fun g hg => ⟨hΓ₁Y hg, h₁ g hg⟩
    have hΓ₂C : Γ₂ ≤ centModSub d.Y x := fun g hg => ⟨hΓ₂Y hg, h₂ g hg⟩
    have hYC : d.Y ≤ centModSub d.Y x := fun z hz => by
      refine ⟨d.Y.le_normalizer hz, ?_⟩
      have hc : x * z = z * x := Data.Hyp.D₂_comm_Y' hx hz
      have : z * x * z⁻¹ * x⁻¹ = 1 := by
        rw [← hc]
        group
      rw [this]
      exact d.Y.one_mem
    have hMYC : d.M ⊔ d.Y ≤ centModSub d.Y x := by
      intro z hz
      obtain ⟨u₁, hu₁, u₂, hu₂, y', hy', rfl⟩ := hs.mem_MY_decomp hz
      exact mul_mem (mul_mem (hΓ₁C (hU₁Γ ⟨u₁, hu₁, rfl⟩)) (hΓ₂C (hU₂Γ ⟨u₂, hu₂, rfl⟩)))
        (hYC ((hs.mem_YK_iff h).2 hy'))
    have hvC : d.v ∈ centModSub d.Y x := by
      rw [hv']
      exact mul_mem (hYC hy₀Y) (mul_mem (hΓ₁C hw₁Γ) (hΓ₂C hw₂Γ))
    have hK₂C : d.K₂ ≤ centModSub d.Y x := by
      rw [Data.K₂_eq_sup_conj]
      refine sup_le (fun z hz => hMYC (mem_sup_left (StdLin.X₂_le_M' h hz))) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hvC (hMYC (mem_sup_left (StdLin.X₂_le_M' h hz)))) (inv_mem hvC)
    have hkC := (hK₂C hk).2
    have e : x⁻¹ * (k * x * k⁻¹) = x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x := by group
    rw [e]
    have hcc : x * (k * x * k⁻¹ * x⁻¹) = (k * x * k⁻¹ * x⁻¹) * x :=
      Data.Hyp.D₂_comm_Y' hx hkC
    have e2 : x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x = k * x * k⁻¹ * x⁻¹ := by
      calc x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x = x⁻¹ * ((k * x * k⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (k * x * k⁻¹ * x⁻¹)) := by rw [hcc]
        _ = k * x * k⁻¹ * x⁻¹ := by group
    rw [e2]
    exact hkC
  obtain ⟨c1, c2, c3, c4⟩ := h.splitting_D₂_lin hK₁ hKY hD (gamEquiv hinj 0) (gamEquiv hinj 2)
    hconjU hp₁ hp₂ hΓ₁' hΓ₂' hU₁MY hU₂MY hw₁Γ hw₂Γ hw₁sq hw₂sq hcomm hU₁Γ hU₂Γ hgen₁ hgen₂ hfix
    hy₀Y hv'
  obtain ⟨η, hη1, hη3, hηfix⟩ := exists_eta
  have hηΓ : φ (blockSL2 F4 3 2 η) ∈ Γ₂ := mem_gam.2 ⟨η, rfl⟩
  have hηfixG : ∀ z ∈ d.Y, φ (blockSL2 F4 3 2 η) * z * (φ (blockSL2 F4 3 2 η))⁻¹ = z →
      z = 1 := by
    intro z hz hfz
    obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ YK, φ z' = z := by
      rw [hs.Y_eq h] at hz
      exact hz
    have e : φ (blockSL2 F4 3 2 η) * φ z' * (φ (blockSL2 F4 3 2 η))⁻¹ =
        φ (blockSL2 F4 3 2 η * z' * (blockSL2 F4 3 2 η)⁻¹) := by simp
    rw [e] at hfz
    rw [hηfix z' hz' (hs.inj hfz), map_one]
  obtain ⟨hcommB, hsqB⟩ := h.B_elemAb hK₁ hηΓ hΓ₂' hηfixG
  refine ⟨ModSplit.liftFixG d.D₂ d.Y Γ₂, hcommB, hsqB, c2, ?_⟩
  have hD₂B := h.D₂_le_normalizer_B hK₁ hΓ₂'
  have hΓ₂B := h.le_normalizer_liftFixG hΓ₂'
  have hΓ₁B := h.Γ_le_normalizer_liftFixG_of_comm hΓ₁' hΓ₂' hcomm
  have hMYB : d.M ⊔ d.Y ≤ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ₂ : Set G) := by
    intro z hz
    obtain ⟨u₁, hu₁, u₂, hu₂, y', hy', rfl⟩ := hs.mem_MY_decomp hz
    exact mul_mem (mul_mem (hΓ₁B (hU₁Γ ⟨u₁, hu₁, rfl⟩)) (hΓ₂B (hU₂Γ ⟨u₂, hu₂, rfl⟩)))
      (hD₂B (h.Y_le_D₂ ((hs.mem_YK_iff h).2 hy')))
  have hD₁B : d.D₁ ≤ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ₂ : Set G) := by
    rw [h.D₁_eq_D₃e₂_sup_M]
    exact sup_le ((h.D₃e₂_le_D₂).trans hD₂B) (le_sup_left.trans hMYB)
  intro p hp b hb
  have hpN : p ∈ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ₂ : Set G) := (sup_le hD₁B hD₂B) hp
  exact (mem_normalizer_iff.1 hpN b).1 hb

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
