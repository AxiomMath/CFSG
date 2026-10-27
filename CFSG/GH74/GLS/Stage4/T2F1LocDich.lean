module

public import CFSG.GH74.GLS.Stage4.T2F1LocCoord
public import CFSG.GH74.GLS.Stage4.T2F1LocNS
public import CFSG.GH74.GLS.Stage4.T2F1LocTor
public import CFSG.GH74.GLS.Stage4.T2F1LocComm

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.Assembly.LowTwoRank

theorem comm_a_mod_H_of_sec {G : Type} [Group G] {N : T2N3 G} {u : G} (hSec : Ch6Sec5 N u) {f : G}
    (hf : f ∈ N.F) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1) (hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁) :
    ∃ h ∈ N.H, f * N.a * f⁻¹ = N.a * h := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hW := hSec.weyl
  have hz : N.z ∈ N.H := hLoc.z_mem_H
  refine comm_a_mod_H (H := N.H) (a := N.a) (w₁ := N.w₁) (w₂ := N.w₂) (f := f) (r := r)
    (fun x hx => (Subgroup.mem_normalizer_iff.1 hW.a_normH x).1 hx) hW.a_cube
    (fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₁_normH x).1 hx)
    (fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₂_normH x).1 hx)
    (by rw [hLoc.w₁_sq]; exact hz) (by rw [hLoc.w₂_sq]; exact hz) hw₁w₂ hW.w₁_a hW.w₂_a
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx) hfr hr ?_
  exact (Subgroup.mem_normalizer_iff.1 (hW.F_normN hf) N.a).1 hW.a_mem_N

theorem sigma₂_eq_one_of_sigma₁_eq_one {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs]
    {z t : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n) (hStd : Std G)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hab : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {f : G} (hf : f ∈ N.F) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1)
    {φ₁ : Hex.SL2 F₁ →* G} {σ₁ : F₁ ≃+* F₁} (hHK₁ : N.H ⊓ N.K₁ = (tSub F₁).map φ₁)
    (hσ₁ : ∀ M : Hex.SL2 F₁, f * φ₁ M * f⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M))
    {φ₂ : Hex.SL2 F₂ →* G} {σ₂ : F₂ ≃+* F₂} (hφ₂ : Function.Injective φ₂)
    (hHK₂ : N.H ⊓ N.K₂ = (tSub F₂).map φ₂)
    (hσ₂ : ∀ M : Hex.SL2 F₂, f * φ₂ M * f⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M))
    (h1 : σ₁ = 1) : σ₂ = 1 := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hW := hSec.weyl
  have hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁ := by
    have := hSet.comm N.w₁ (hK₁ ▸ hLoc.w₁_mem) N.w₂ (hK₂ ▸ hLoc.w₂_mem)
    exact this
  obtain ⟨h₀, hh₀, hfa⟩ := comm_a_mod_H_of_sec hSec hf hr hfr hw₁w₂
  have hfH : ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx
  have hfK₂ : ∀ x ∈ N.K₂, f * x * f⁻¹ ∈ N.K₂ := by
    have := conj_mem_sup (hF5.F_normX₂ f hf) (hF5.F_normX₂' f hf)
    rw [← hLoc.K₂_eq] at this
    exact this
  have hfH₂ : ∀ x ∈ N.H ⊓ N.K₂, f * x * f⁻¹ ∈ N.H ⊓ N.K₂ := fun x hx =>
    ⟨hfH x hx.1, hfK₂ x hx.2⟩
  have hf₁ : ∀ x ∈ N.H ⊓ N.K₁, f * x * f⁻¹ = x := by
    intro x hx
    rw [hHK₁] at hx
    obtain ⟨M, -, rfl⟩ := hx
    exact centralizes_of_eq_one φ₁ f σ₁ hσ₁ h1 M
  have hns := no_fixed_odd_K₂ hL hL3 hIVK hn hStd hSet hRem hab hz hK₁ hK₂ hq₁ hq₂ hSec
  have hodd : ∀ x ∈ N.H ⊓ N.K₂, Odd (orderOf x) → f * x * f⁻¹ = x := fun x hx hxo =>
    torus_fixed_of_nonsingular (H := N.H) (H₁ := N.H ⊓ N.K₁) (H₂ := N.H ⊓ N.K₂) (a := N.a)
      (f := f) (w := N.w₂) hLoc.H_comm inf_le_left inf_le_left hLoc.H_idx
      (fun y hy => (Subgroup.mem_normalizer_iff.1 hW.a_normH y).1 hy) hW.a_cube hfH₂ ⟨h₀, hh₀, hfa⟩
      hf₁ hW.w₂_a hLoc.w₂_inv hns hx hxo
  have hall := cyclic_odd_conj_trivial hLoc.H₂_cyc hfH₂ hr hfr hodd
  refine eq_one_of_centralizes_torus φ₂ f σ₂ hφ₂ hσ₂ ?_
  intro s
  apply hall
  rw [hHK₂]
  exact ⟨sl2D s, sl2D_mem_tSub s, rfl⟩

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
