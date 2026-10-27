module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM31
public import CFSG.ClassicalInvolution.Asc77.AscC5OM25
public import CFSG.ClassicalInvolution.Asc77.AscC5OM30

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Asc77.C5O.M
open scoped Matrix MatrixGroups

namespace M

variable {F : Type} [Field F]

theorem coe_scl_mul (r : Fˣ) (X : GL (Fin 2) F) :
    ((scl r * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (r : F) • (X : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_eq_diagonal_mul]

theorem conj_smul_eq {θ : MulAut SL(2, F)} {d : GL (Fin 2) F}
    (hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹)
    {c : GL (Fin 2) F} {s : F} {w : SL(2, F)}
    (hc : (c : Matrix (Fin 2) (Fin 2) F) = s • (w : Matrix (Fin 2) (Fin 2) F)) (r : Fˣ) :
    ((scl r * (d * c * d⁻¹) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((r : F) * s) • ((θ w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hθ w)
  change ((θ w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _ at h
  rw [coe_scl_mul, h, Units.val_mul, Units.val_mul, hc, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rfl

end M

section Main

variable {p f : ℕ} [Fact p.Prime]


variable (p f) in
theorem om5TwinComm_proved : Om5TwinComm p f := by
  intro Y₁ Y₂ _ _ _ _ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ Mg _ _ π₁ π₂ L L' hT γ₁ δ₁ γ₂ δ₂
    hγ₁A _ hγ₂A _ hδ₁A _ hδ₂A _ hγ hδ
  obtain ⟨fr₁, Φ₂', fr₂, θ, d, -, hθ, hrel⟩ := M.exists_setup hT
  have hp := hT.data₁.odd
  have h2 := M.two_ne_zero_gf (p := p) f hp
  have h5 := M.five_le_card_gf (p := p) (f := f) hT.data₁.five
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hF : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  have hsurj : ∀ (k : Fin 2) (b : SL(2, GaloisField p f)),
      ∃ m : Mg, π₁ m = fr₁.ψ (longBlock (GaloisField p f) 2 k b) := by
    intro k b
    have hb : fr₁.ψ (longBlock (GaloisField p f) 2 k b) ∈
        (longRootSp2 (GaloisField p f) 2 k).map fr₁.ψ := ⟨_, ⟨b, rfl⟩, rfl⟩
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · have e : (longRootSp2 (GaloisField p f) 2 0).map fr₁.ψ = L.map π₁ :=
        fr₁.hA.symm.trans hT.map₁.1.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
    · have e : (longRootSp2 (GaloisField p f) 2 1).map fr₁.ψ = L'.map π₁ :=
        fr₁.hA'.symm.trans hT.map₁.2.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
  obtain ⟨G₁, σ₁, hG₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ γ₁
  obtain ⟨N₁, τ₁, hN₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨G₂, σ₂, hG₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ γ₂
  obtain ⟨N₂, τ₂, hN₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨g₁, hg₁, hdg₁⟩ := M.exists_gl_blocks G₁ (M.isBD_gm_of_conjSp_longInv h2 G₁ σ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ γ₁ G₁ σ₁ hG₁ hγ₁A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := M.exists_gl_blocks N₁ (M.isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨g₂, hg₂, hdg₂⟩ := M.exists_gl_blocks G₂ (M.isBD_gm_of_conjSp_longInv h2 G₂ σ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ γ₂ G₂ σ₂ hG₂ hγ₂A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := M.exists_gl_blocks N₂ (M.isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rγ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    γ₁ γ₂ G₁ G₂ σ₁ σ₂ hG₁ hG₂ hg₁ hg₂ hγ
  have rδ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hσ, -⟩ := rγ 0
  obtain ⟨hτ, -⟩ := rδ 0
  subst hσ hτ
  choose ℓ hℓ using fun k => (rγ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField p f) := G₁ * gspFieldMap σ₁ N₁ * gspFieldMap τ₁ G₁⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField p f) :=
    fun k => g₁ k * glm σ₁ (n₁ k) * (glm τ₁ (g₁ k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField p f))) := by
    rw [hC₁def, gm_comm_bd G₁ N₁ N₁ σ₁ τ₁ hg₁ hn₁ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, γ₁ (δ₁ (γ₁.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift fr₁.ψ γ₁ δ₁ (conjSp 2 _ G₁ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hG₁ hN₁ x, comm_conjSp_fieldSp]
  set C₂ : gsp 2 (GaloisField p f) := G₂ * gspFieldMap σ₁ N₂ * gspFieldMap τ₁ G₂⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField p f) :=
    fun k => g₂ k * glm σ₁ (n₂ k) * (glm τ₁ (g₂ k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField p f))) := by
    rw [hC₂def, gm_comm_bd G₂ N₂ N₂ σ₁ τ₁ hg₂ hn₂ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, γ₂ (δ₂ (γ₂.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift fr₂.ψ γ₂ δ₂ (conjSp 2 _ G₂ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hG₂ hN₂ x, comm_conjSp_fieldSp]
  have hμG₁ : mu G₁ ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  obtain ⟨s, hs⟩ := isSquare_comm_det hF σ₁ τ₁ hμG₁ hμN₁
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    have h1 : τ₁ (mu G₁) ≠ 0 := (map_ne_zero τ₁).mpr hμG₁
    have h2 : σ₁ (mu N₁) ≠ 0 := (map_ne_zero σ₁).mpr hμN₁
    simp_all
  have hdc : ∀ k, ((c₁ k : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)).det =
      mu G₁ * σ₁ (mu N₁) * (τ₁ (mu G₁))⁻¹ * (mu N₁)⁻¹ := fun k => by
    simp only [hc₁def, det_gl_mul, det_gl_inv, det_glm, hdg₁, hdn₁]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hg₂' : ∀ k, g₂ k = scl (ℓ k) * (d k * g₁ k * (glm σ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hℓ k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₂ k = scl (ℓ k * Units.map (σ₁ : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (ℓ k))⁻¹ * (κ k)⁻¹) * (d k * c₁ k * (d k)⁻¹) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hg₂' k, hn₂' k]
    exact fix_transport (d k) (g₁ k) (n₁ k) σ₁ τ₁ (ℓ k) (κ k)
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hr := fix_ratio hp σ₁ τ₁ (hν 0) (hν 1) hμG₁ hμN₁ (ℓ 0) (ℓ 1) (κ 0) (κ 1)
    (det_rel (hdg₁ 0) (hdg₂ 0) (hℓ 0)) (det_rel (hdg₁ 1) (hdg₂ 1) (hℓ 1))
    (det_rel (hdn₁ 0) (hdn₂ 0) (hκ 0)) (det_rel (hdn₁ 1) (hdn₂ 1) (hκ 1))
  set r := ℓ 0 * Units.map (σ₁ : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (ℓ 0))⁻¹ * (κ 0)⁻¹
    with hrdef
  have hw'₀ : ((c₂ 0 : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)) = ((r : GaloisField p f) * s) •
      ((θ 0 w₀ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    rw [htr 0]
    exact conj_smul_eq (hθ 0) hw₀ _
  have hw'₁ : ((c₂ 1 : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)) = ((r : GaloisField p f) * s) •
      ((θ 1 w₁ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq (hθ 1) hw₁ _
  obtain ⟨m₀, hm₀⟩ := hsurj 0 w₀
  obtain ⟨m₁, hm₁⟩ := hsurj 1 w₁
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [fr₁.inner_of_lift (fun y => γ₁ (δ₁ (γ₁.symm (δ₁.symm y)))) C₁ hc1 hC₁ hs0 w₀ w₁ hw₀ hw₁
      y, map_mul π₁, hm₀, hm₁, ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => γ₂ (δ₂ (γ₂.symm (δ₂.symm y)))) C₂ hc2 hC₂
      (mul_ne_zero r.ne_zero hs0) (θ 0 w₀) (θ 1 w₁) hw'₀ hw'₁ y, map_mul π₂, hrel 0 m₀ w₀ hm₀,
      hrel 1 m₁ w₁ hm₁, ← map_mul]

end Main

end CFSG.ClassicalInvolution.Asc77.C5O
