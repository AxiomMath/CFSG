module

public import CFSG.CGT.PushingUpLit.A78S4.Nat
public import CFSG.CGT.PushingUpLit.A78G0.Basic
public import CFSG.CGT.PushingUpLit.T2K.Nat

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78S4 Matrix

variable {G : Type} [Group G] {L V K : Subgroup G} {e : ℕ}

theorem act_smul_of_fixed_line (D : NatCoordK G L V K (GaloisField 2 e)) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    {w₀ : Fin 2 → GaloisField 2 e} (hw₀ : w₀ ≠ 0)
    (hfix : ∀ c : GaloisField 2 e, D.act x (c • w₀) = c • w₀) :
    ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act x (c • w) = c • D.act x w := by
  obtain ⟨σ, hσ⟩ := D.exists_semilinear hxL hx
  have hσ' : ∀ c w, D.act x (c • w) = σ c • D.act x w := fun c w => hσ c w
  have hσ1 : ∀ c, σ c = c := by
    intro c
    have h0 : D.act x w₀ = w₀ := by simpa using hfix 1
    have h1 := hσ' c w₀
    rw [hfix c, h0] at h1
    exact (smul_left_injective (GaloisField 2 e) hw₀ h1).symm
  intro c w
  rw [hσ', hσ1]

theorem exists_matrix_of_smul (D : NatCoordK G L V K (GaloisField 2 e)) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (hlin : ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act x (c • w) = c • D.act x w) :
    ∃ M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e), ∀ w, D.act x w = M *ᵥ w := by
  refine ⟨Matrix.of fun i j => D.act x (Pi.single j 1) i, fun w => ?_⟩
  have hw : w = w 0 • (Pi.single 0 1 : Fin 2 → GaloisField 2 e) +
      w 1 • (Pi.single 1 1 : Fin 2 → GaloisField 2 e) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hw]
  rw [NatCoordK.act_add hx, hlin, hlin]
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem exists_scalar_elem (D : NatCoordK G L V K (GaloisField 2 e)) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (hlin : ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act x (c • w) = c • D.act x w) :
    ∃ l₀ ∈ L, ∃ lam : GaloisField 2 e, lam ≠ 0 ∧ ∀ w, D.act (x * l₀⁻¹) w = lam • w := by
  obtain ⟨M, hM⟩ := exists_matrix_of_smul D hx hlin
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    have h1 : D.act x v = D.act x 0 := by
      rw [hM, hMv, hM]
      simp
    exact (D.actPerm x hx).injective h1
  obtain ⟨lam, hlam⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (GaloisField 2 e) 2) M.det
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    apply hdet
    rw [hlam]
    ring
  set S : Matrix (Fin 2) (Fin 2) (GaloisField 2 e) := lam⁻¹ • M with hS
  have hSdet : S.det = 1 := by
    rw [hS, Matrix.det_smul, Fintype.card_fin, hlam]
    field_simp
  set Sg : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) := ⟨S, hSdet⟩ with hSg
  have hSgc : (Sg : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = S := rfl
  obtain ⟨l₀, hl₀, hl₀S⟩ := D.ρ_surj Sg
  refine ⟨l₀, hl₀, lam, hlam0, fun w => ?_⟩
  rw [NatCoordK.act_mul hx (D.le_normVK (inv_mem hl₀)), NatCoordK.act_of_mem_L (inv_mem hl₀), hM,
    D.ρ_inv hl₀, hl₀S]
  have hMS : M = lam • S := by rw [hS, smul_inv_smul₀ hlam0]
  rw [Matrix.mulVec_mulVec]
  have h1 : M * ((Sg⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = lam • (1 : Matrix (Fin 2) (Fin 2)
        (GaloisField 2 e)) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hSgc, hMS, Matrix.smul_mul, Matrix.mul_adjugate,
      hSdet, one_smul]
  rw [h1]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem comm_mem_V_of_scalar (D : NatCoordK G L V K (GaloisField 2 e)) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    {lam : GaloisField 2 e} (hlam : lam ≠ 0) (hact : ∀ w, D.act y w = lam • w)
    {l : G} (hl : l ∈ L) : y * l * y⁻¹ * l⁻¹ ∈ V := by
  have hl' : y * l * y⁻¹ ∈ L := conj_mem_of_mem_normalizer' hyL hl
  have h1 : ∀ w, (D.ρ (y * l * y⁻¹) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w =
      (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w := by
    intro w
    have h2 := NatCoordK.act_twist (D := D) hyL hy hl w
    rw [hact, hact, mulVec_smul] at h2
    exact (smul_right_injective (Fin 2 → GaloisField 2 e) hlam h2).symm
  have h3 : D.ρ (y * l * y⁻¹) = D.ρ l := CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec h1
  have h4 : D.ρ (y * l * y⁻¹ * l⁻¹) = 1 := by
    rw [D.ρ_mul _ hl' _ (inv_mem hl), D.ρ_inv hl, h3, mul_inv_cancel]
  exact (D.ρ_eq_one _ (mul_mem hl' (inv_mem hl))).1 h4

theorem mem_K_of_centralizes (D : NatCoordK G L V K (GaloisField 2 e)) {y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    {lam : GaloisField 2 e} (hlam1 : lam ≠ 1) (hact : ∀ w, D.act y w = lam • w) {v : G}
    (hv : v ∈ V) (hyv : y * v * y⁻¹ = v) : v ∈ K := by
  have h1 := NatCoordK.act_κ (D := D) hy hv
  rw [hyv, hact] at h1
  have h2 : (lam - 1) • D.κ v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hlam1
  · exact (D.κ_eq_zero v hv).1 h3

theorem comm_mem_K_of_one (D : NatCoordK G L V K (GaloisField 2 e)) {y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (hact : ∀ w, D.act y w = (1 : GaloisField 2 e) • w) {v : G} (hv : v ∈ V) :
    y * v * y⁻¹ * v⁻¹ ∈ K :=
  NatCoordK.comm_mem_of_act (D := D) hy (fun w => by rw [hact, one_smul]) hv

end CFSG.CGT.PushingUpLit.A78G0
