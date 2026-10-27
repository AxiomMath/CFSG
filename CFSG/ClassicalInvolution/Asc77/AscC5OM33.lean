module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM32

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

theorem isSquare_swap_det [Finite F] (hF : ringChar F ≠ 2) (π τ : F ≃+* F) {μ η η' ν : F}
    (hμ : μ ≠ 0) (hη : η ≠ 0) (hν : ν ≠ 0) (κ : Fˣ) (h : η' * τ ν = (κ : F) ^ 2 * ν * η) :
    IsSquare (μ * π η * (τ μ)⁻¹ * η'⁻¹) := by
  have h1 := isSquare_comm_det hF π τ hμ hη
  have h2 := CFSG.ComponentClassification.RankTwoOddLie.isSquare_ringEquiv_mul_inv hF τ hν
  have h3 : IsSquare (((κ : F)⁻¹) ^ 2) := ⟨(κ : F)⁻¹, sq _⟩
  have hτν : τ ν ≠ 0 := (map_ne_zero τ).mpr hν
  have hκ : (κ : F) ≠ 0 := κ.ne_zero
  have hη' : η' = (κ : F) ^ 2 * ν * η / τ ν := by
    rw [eq_div_iff hτν, h]
  have e : μ * π η * (τ μ)⁻¹ * η'⁻¹ =
      μ * π η * (τ μ)⁻¹ * η⁻¹ * (τ ν * ν⁻¹) * ((κ : F)⁻¹) ^ 2 := by
    rw [hη']
    have : τ μ ≠ 0 := (map_ne_zero τ).mpr hμ
    field_simp
  rw [e]
  exact (h1.mul h2).mul h3

theorem conj_smul_eq_inv {θ : MulAut SL(2, F)} {d : GL (Fin 2) F}
    (hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹)
    {c : GL (Fin 2) F} {s : F} {w : SL(2, F)}
    (hc : (c : Matrix (Fin 2) (Fin 2) F) = s • (w : Matrix (Fin 2) (Fin 2) F)) (r : Fˣ) :
    ((scl r * (d⁻¹ * c * d) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((r : F) * s) • ((θ⁻¹ w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  have hθ' : ∀ b, Matrix.SpecialLinearGroup.toGL (θ⁻¹ b) =
      d⁻¹ * Matrix.SpecialLinearGroup.toGL b * d⁻¹⁻¹ := fun b => by
    rw [slg_inv_apply hθ, inv_inv]
  have h := conj_smul_eq hθ' hc r
  rwa [inv_inv] at h

end M

section Main

variable {p f : ℕ} [Fact p.Prime]


variable (p f) in
theorem om5TwinCommSwap_proved : Om5TwinCommSwap p f := by
  intro Y₁ Y₂ _ _ _ _ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ Mg _ _ π₁ π₂ L L' hT ψ ψ' δ₁ δ₂
    hψA _ hψ'A _ hδ₁A _ hδ₂A _ hψ hδ
  obtain ⟨fr₁, Φ₂', fr₂, θ, d, hker, hθ, hrel⟩ := M.exists_setup hT
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
  obtain ⟨P, π, hP⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₂ ψ
  obtain ⟨P', π', hP'⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₁ ψ'
  obtain ⟨N₁, τ₁, hN₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨N₂, τ₂, hN₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨pb, hpb, hdpb⟩ := M.exists_gl_blocks P (M.isBD_gm_of_conjSp_longInv h2 P π
    (M.Frame.lift_longInv h2 h4 fr₁ fr₂ ψ P π hP hψA.le))
  obtain ⟨pb', hpb', hdpb'⟩ := M.exists_gl_blocks P' (M.isBD_gm_of_conjSp_longInv h2 P' π'
    (M.Frame.lift_longInv h2 h4 fr₂ fr₁ ψ' P' π' hP' hψ'A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := M.exists_gl_blocks N₁ (M.isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := M.exists_gl_blocks N₂ (M.isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rψ := fun k => M.swap_block_rel h2 fr₁ fr₂ π₁ π₂ hker (θ k) (d k) k (hθ k) (hrel k)
    (hsurj k) ψ ψ' P P' π π' hP hP' hpb hpb' hψ
  have rδ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hπ, -⟩ := rψ 0
  obtain ⟨hτ, -⟩ := rδ 0
  have hπ' := hπ.symm
  subst hπ' hτ
  choose lam hlam using fun k => (rψ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField p f) := P' * gspFieldMap π N₂ * gspFieldMap τ₁ P'⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField p f) :=
    fun k => pb' k * glm π (n₂ k) * (glm τ₁ (pb' k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField p f))) := by
    rw [hC₁def, gm_comm_bd P' N₂ N₁ π τ₁ hpb' hn₂ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, ψ' (δ₂ (ψ'.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₁.ψ fr₂.ψ ψ' δ₁ δ₂ (conjSp 2 _ P' * fieldSp 2 _ π)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hP' hN₁ hN₂ x,
      comm_conjSp_fieldSp_gen]
  set C₂ : gsp 2 (GaloisField p f) := P * gspFieldMap π N₁ * gspFieldMap τ₁ P⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField p f) :=
    fun k => pb k * glm π (n₁ k) * (glm τ₁ (pb k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField p f))) := by
    rw [hC₂def, gm_comm_bd P N₁ N₂ π τ₁ hpb hn₁ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, ψ (δ₁ (ψ.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₂.ψ fr₁.ψ ψ δ₂ δ₁ (conjSp 2 _ P * fieldSp 2 _ π)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hP hN₂ hN₁ x,
      comm_conjSp_fieldSp_gen]
  have hμP : mu P ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  have hμN₂ : mu N₂ ≠ 0 := Units.ne_zero _
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hκrel := fun k => det_rel (hdn₁ k) (hdn₂ k) (hκ k)
  obtain ⟨s, hs⟩ := isSquare_swap_det hF π τ₁ hμP hμN₁ (hν 0) (κ 0) (hκrel 0)
  have hne : mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hμP ((map_ne_zero π).mpr hμN₁))
      (inv_ne_zero ((map_ne_zero τ₁).mpr hμP))) (inv_ne_zero hμN₂)
  have hs0 : s ≠ 0 := fun h => hne (by rw [hs, h, mul_zero])
  have hdc : ∀ k, ((c₂ k : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)).det =
      mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ := fun k => by
    simp only [hc₂def, det_gl_mul, det_gl_inv, det_glm, hdpb, hdn₁, hdn₂]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hp' : ∀ k, pb' k = scl (lam k) * ((d k)⁻¹ * pb k * (glm π (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hlam k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₁ k = scl (lam k * Units.map (π : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (lam k))⁻¹ * κ k) * ((d k)⁻¹ * c₂ k * d k) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hp' k, hn₂' k]
    exact swap_transport (d k) (pb k) (n₁ k) π τ₁ (lam k) (κ k)
  have hr := swap_ratio hp π τ₁ (hν 0) (hν 1) hμP hμN₁ (lam 0) (lam 1) (κ 0) (κ 1)
    (det_rel_swap (hdpb 0) (hdpb' 0) (hlam 0)) (det_rel_swap (hdpb 1) (hdpb' 1) (hlam 1))
    (hκrel 0) (hκrel 1)
  set r := lam 0 * Units.map (π : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (lam 0))⁻¹ * κ 0
    with hrdef
  have hw'₀ : ((c₁ 0 : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)) = ((r : GaloisField p f) * s) •
      (((θ 0)⁻¹ w₀ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    rw [htr 0]
    exact conj_smul_eq_inv (hθ 0) hw₀ _
  have hw'₁ : ((c₁ 1 : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)) = ((r : GaloisField p f) * s) •
      (((θ 1)⁻¹ w₁ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq_inv (hθ 1) hw₁ _
  obtain ⟨m₀, hm₀⟩ := hsurj 0 ((θ 0)⁻¹ w₀)
  obtain ⟨m₁, hm₁⟩ := hsurj 1 ((θ 1)⁻¹ w₁)
  have e₀ : π₂ m₀ = fr₂.ψ (longBlock (GaloisField p f) 2 0 w₀) := by
    rw [hrel 0 m₀ _ hm₀, show (θ 0) ((θ 0)⁻¹ w₀) = w₀ from by simp]
  have e₁ : π₂ m₁ = fr₂.ψ (longBlock (GaloisField p f) 2 1 w₁) := by
    rw [hrel 1 m₁ _ hm₁, show (θ 1) ((θ 1)⁻¹ w₁) = w₁ from by simp]
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [fr₁.inner_of_lift (fun y => ψ' (δ₂ (ψ'.symm (δ₁.symm y)))) C₁ hc1 hC₁
      (mul_ne_zero r.ne_zero hs0) ((θ 0)⁻¹ w₀) ((θ 1)⁻¹ w₁) hw'₀ hw'₁ y, map_mul π₁, hm₀, hm₁,
      ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => ψ (δ₁ (ψ.symm (δ₂.symm y)))) C₂ hc2 hC₂ hs0 w₀ w₁ hw₀ hw₁ y,
      map_mul π₂, e₀, e₁, ← map_mul]

variable (p f) in
theorem m8gFacts_proved : M8GFacts p f where
  comm := om5TwinComm_proved p f
  commSwap := om5TwinCommSwap_proved p f

end Main

end CFSG.ClassicalInvolution.Asc77.C5O
