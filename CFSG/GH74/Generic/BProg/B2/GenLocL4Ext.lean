module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtBasis
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtClass
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix

namespace GenLocL4Ext

variable {F : Type} [Field F]

theorem isSquare_mul_of_not_isSquare [Finite F] {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by simp [h]⟩
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have h3 : quadraticChar F (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 h3

section Lift

variable {A : Type} [Group A]
  (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (ρ : A → GL (Fin 4) F)

theorem alpha_eq (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((ρ a)⁻¹ : GL (Fin 4) F)) (a : A) :
    α a = CatalogueBHigherLinearAction.slConjugation 4 F (ρ a) := by
  ext g : 1
  apply Subtype.ext
  rw [hρ, LinearFlag.coe_slConjugation]

theorem rho_sq_scalar (hA : CFSG.IsElementaryAbelian 2 A)
    (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((ρ a)⁻¹ : GL (Fin 4) F)) (a : A) :
    ∃ l : F, l ≠ 0 ∧ (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F) =
      l • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have h1 : α a * α a = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  obtain ⟨l, hl⟩ := exists_scalar_of_commute_sl (n := 4)
    (M := (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F)) (fun g => by
      have h2 := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) =>
        ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h1
      simp only [MulAut.mul_apply, MulAut.one_apply, hρ] at h2
      have h3 : (g : Matrix (Fin 4) (Fin 4) F) * ((ρ a : Matrix (Fin 4) (Fin 4) F) *
            (ρ a : Matrix (Fin 4) (Fin 4) F)) =
          ((ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F)) *
            (g : Matrix (Fin 4) (Fin 4) F) := by
        conv_lhs => rw [← h2]
        simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
      exact h3)
  refine ⟨l, fun h0 => ?_, hl⟩
  have hu := (ρ a * ρ a).mul_inv
  rw [Units.val_mul, hl, h0, zero_smul, zero_mul] at hu
  exact zero_ne_one hu

theorem mem_gammaAct_of_fix [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (x : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hidx : ((Subgroup.zpowers x).comap α).index ≤ 2) (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hg : x g = g) : g ∈ gammaAct α := by
  refine le_gammaAct α ((GenLocBasic.adm_iff_index hA _).2 hidx)
    ((GenLocBasic.mem_fixedIn_map α _ g).2 fun e he => ?_)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show α e ∈ Subgroup.zpowers x from he)
  have hx : x ∈ MulAction.stabilizer (MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) g := by
    rw [MulAction.mem_stabilizer_iff]
    exact hg
  have h1 := (MulAction.stabilizer (MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) g).zpow_mem hx k
  rw [MulAction.mem_stabilizer_iff] at h1
  rw [← hk]
  exact h1

theorem slConjugation_fix (u : GL (Fin 4) F) (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) :
    CatalogueBHigherLinearAction.slConjugation 4 F u g = g := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, ← hg, Units.mul_inv_cancel_right]

theorem gammaAct_eq_top_of_split [Finite F] (h2 : (2 : F) ≠ 0) [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A)
    (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((ρ a)⁻¹ : GL (Fin 4) F))
    (a₀ : A) {c : F} (hc : ¬ IsSquare c)
    (hsq : (ρ a₀ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F) =
      c • (1 : Matrix (Fin 4) (Fin 4) F))
    (Ng : GL (Fin 4) F) (b₀ : A) (hb₀ : α b₀ = CatalogueBHigherLinearAction.slConjugation 4 F Ng)
    {s : F} (hs : s ≠ 0)
    (hN2 : (Ng : Matrix (Fin 4) (Fin 4) F) * (Ng : Matrix (Fin 4) (Fin 4) F) =
      (s * s) • (1 : Matrix (Fin 4) (Fin 4) F))
    (hcomm : ∀ b, (ρ b : Matrix (Fin 4) (Fin 4) F) * (Ng : Matrix (Fin 4) (Fin 4) F) =
      (Ng : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F))
    (hab : ∀ a b, (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F) =
      (ρ b : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F))
    (hN1 : (Ng : Matrix (Fin 4) (Fin 4) F) ≠ s • (1 : Matrix (Fin 4) (Fin 4) F))
    (hN3 : (Ng : Matrix (Fin 4) (Fin 4) F) ≠ -(s • (1 : Matrix (Fin 4) (Fin 4) F))) :
    gammaAct α = ⊤ := by
  have := hA
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by simp [h]⟩
  have hPP : α a₀ * α a₀ = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA, map_one]
  have hQQ : α b₀ * α b₀ = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA, map_one]
  have hPQ : α a₀ * α b₀ = α b₀ * α a₀ := by
    rw [← map_mul, ← map_mul, mul_comm' a₀ b₀]
  have hiN := hcomm a₀
  obtain ⟨B, hB1, hB2⟩ := exists_split_basis hc h2 (ρ a₀ : Matrix (Fin 4) (Fin 4) F)
    (Ng : Matrix (Fin 4) (Fin 4) F) hs hsq hN2 hiN hN1 hN3
  have four : ∀ b, α b = 1 ∨ α b = α a₀ ∨ α b = α b₀ ∨ α b = α a₀ * α b₀ := by
    intro b
    obtain ⟨l, hl, hl2⟩ := rho_sq_scalar α ρ hA hρ b
    obtain ⟨μ, hμ, h | h | h | h⟩ := four_class hc h2 B (ρ a₀ : Matrix (Fin 4) (Fin 4) F)
      (Ng : Matrix (Fin 4) (Fin 4) F) hs hB1 hB2 (ρ b : Matrix (Fin 4) (Fin 4) F) (hab b a₀)
      (hcomm b) hl hl2
    · left
      rw [alpha_eq α ρ hρ b, slConjugation_congr (ρ b) 1 hμ (by simpa using h), map_one]
    · right; right; left
      rw [alpha_eq α ρ hρ b, hb₀]
      exact slConjugation_congr (ρ b) Ng hμ h
    · right; left
      rw [alpha_eq α ρ hρ b, alpha_eq α ρ hρ a₀]
      exact slConjugation_congr (ρ b) (ρ a₀) hμ h
    · right; right; right
      rw [alpha_eq α ρ hρ b, hb₀, alpha_eq α ρ hρ a₀, ← map_mul]
      exact slConjugation_congr (ρ b) (ρ a₀ * Ng) hμ (by rw [h, Units.val_mul])
  have hHP : ((Subgroup.zpowers (α a₀)).comap α).index ≤ 2 := by
    refine index_le_two_of_cover _ b₀ (fun b => ?_)
    rcases four b with h | h | h | h
    · left; show α b ∈ Subgroup.zpowers (α a₀); rw [h]; exact one_mem _
    · left; show α b ∈ Subgroup.zpowers (α a₀); rw [h]; exact Subgroup.mem_zpowers _
    · right; show α (b * b₀) ∈ Subgroup.zpowers (α a₀); rw [map_mul, h, hQQ]; exact one_mem _
    · right; show α (b * b₀) ∈ Subgroup.zpowers (α a₀)
      rw [map_mul, h, mul_assoc, hQQ, mul_one]; exact Subgroup.mem_zpowers _
  have hHQ : ((Subgroup.zpowers (α b₀)).comap α).index ≤ 2 := by
    refine index_le_two_of_cover _ a₀ (fun b => ?_)
    rcases four b with h | h | h | h
    · left; show α b ∈ Subgroup.zpowers (α b₀); rw [h]; exact one_mem _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α b₀); rw [map_mul, h, hPP]; exact one_mem _
    · left; show α b ∈ Subgroup.zpowers (α b₀); rw [h]; exact Subgroup.mem_zpowers _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α b₀)
      rw [map_mul, h, hPQ, mul_assoc, hPP, mul_one]; exact Subgroup.mem_zpowers _
  refine eq_top_of_centralizers (c := c) hc0 B (ρ a₀ : Matrix (Fin 4) (Fin 4) F)
    (s⁻¹ • (Ng : Matrix (Fin 4) (Fin 4) F)) hB1 hB2 (gammaAct α) (fun g hg => ?_) (fun g hg => ?_)
  · refine mem_gammaAct_of_fix α hA (α a₀) hHP g ?_
    rw [alpha_eq α ρ hρ a₀]
    exact slConjugation_fix (ρ a₀) g hg
  · refine mem_gammaAct_of_fix α hA (α b₀) hHQ g ?_
    rw [hb₀]
    refine slConjugation_fix Ng g ?_
    rw [Matrix.mul_smul, Matrix.smul_mul] at hg
    exact smul_right_injective _ (inv_ne_zero hs) hg

end Lift

end GenLocL4Ext

section L4

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl4_ext_odd {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (ρ : A → GL (Fin 4) F) (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) * ((ρ a)⁻¹ : GL (Fin 4) F))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a) (a₀ : A) (c : F) (hc : ¬ IsSquare c)
    (hsq : ((ρ a₀ * ρ a₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.scalar (Fin 4) c) :
    gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hA' := hA.1
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by simp [h]⟩
  have hsq' : (ρ a₀ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F) =
      c • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [Units.val_mul, Matrix.scalar_apply] at hsq
    rw [hsq, Matrix.smul_one_eq_diagonal]
  have hab' : ∀ a b, (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F) =
      (ρ b : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F) := fun a b => by
    simpa [Units.val_mul] using congrArg Units.val (hab a b)
  by_cases hall : ∀ a, ∃ l : F, l ≠ 0 ∧
      ((ρ a : Matrix (Fin 4) (Fin 4) F) = l • (1 : Matrix (Fin 4) (Fin 4) F) ∨
        (ρ a : Matrix (Fin 4) (Fin 4) F) = l • (ρ a₀ : Matrix (Fin 4) (Fin 4) F))
  · have hPP : α a₀ * α a₀ = 1 := by
      rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA', map_one]
    have hcls : ∀ b, α b = 1 ∨ α b = α a₀ := by
      intro b
      obtain ⟨l, hl, h | h⟩ := hall b
      · left
        rw [GenLocL4Ext.alpha_eq α ρ hρ b,
          GenLocL4Ext.slConjugation_congr (ρ b) 1 hl (by simpa using h), map_one]
      · right
        rw [GenLocL4Ext.alpha_eq α ρ hρ b, GenLocL4Ext.alpha_eq α ρ hρ a₀]
        exact GenLocL4Ext.slConjugation_congr (ρ b) (ρ a₀) hl h
    have hidx : α.ker.index ≤ 2 := by
      refine GenLocL4Ext.index_le_two_of_cover _ a₀ (fun b => ?_)
      rcases hcls b with h | h
      · left; exact MonoidHom.mem_ker.2 h
      · right; rw [MonoidHom.mem_ker, map_mul, h, hPP]
    exact gammaAct_eq_top_of_le_ker α (E := α.ker) ((GenLocBasic.adm_iff_index hA' _).2 hidx) le_rfl
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨d, hd0, hd⟩ := GenLocL4Ext.rho_sq_scalar α ρ hA' hρ a₁
    by_cases hdsq : IsSquare d
    · obtain ⟨s, hs⟩ := hdsq
      have hs0 : s ≠ 0 := fun h => hd0 (by rw [hs, h, mul_zero])
      refine GenLocL4Ext.gammaAct_eq_top_of_split α ρ h2 hA' hρ a₀ hc hsq' (ρ a₁) a₁
        (GenLocL4Ext.alpha_eq α ρ hρ a₁) hs0 (by rw [hd, hs]) (fun b => hab' b a₁) hab' ?_ ?_
      · intro h
        exact (ha₁ s hs0).1 h
      · intro h
        exact (ha₁ (-s) (neg_ne_zero.2 hs0)).1 (by rw [h, neg_smul])
    · obtain ⟨s, hs⟩ := GenLocL4Ext.isSquare_mul_of_not_isSquare hdsq hc
      have hs0 : s ≠ 0 := fun h => mul_ne_zero hd0 hc0 (by rw [hs, h, mul_zero])
      have key : ∀ t : F, ((ρ a₁ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) =
          t • (1 : Matrix (Fin 4) (Fin 4) F) →
          (ρ a₁ : Matrix (Fin 4) (Fin 4) F) = (c⁻¹ * t) • (ρ a₀ : Matrix (Fin 4) (Fin 4) F) := by
        intro t h
        have e1 : ((ρ a₁ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) *
            (ρ a₀ : Matrix (Fin 4) (Fin 4) F) = (t • (1 : Matrix (Fin 4) (Fin 4) F)) *
              (ρ a₀ : Matrix (Fin 4) (Fin 4) F) := by rw [h]
        rw [Matrix.mul_assoc, hsq', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.one_mul] at e1
        calc (ρ a₁ : Matrix (Fin 4) (Fin 4) F) = c⁻¹ • (c • (ρ a₁ : Matrix (Fin 4) (Fin 4) F)) := by
              rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
          _ = c⁻¹ • (t • (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) := by rw [e1]
          _ = (c⁻¹ * t) • (ρ a₀ : Matrix (Fin 4) (Fin 4) F) := by rw [smul_smul]
      refine GenLocL4Ext.gammaAct_eq_top_of_split α ρ h2 hA' hρ a₀ hc hsq' (ρ a₁ * ρ a₀) (a₁ * a₀)
        (by rw [map_mul, GenLocL4Ext.alpha_eq α ρ hρ a₁, GenLocL4Ext.alpha_eq α ρ hρ a₀, map_mul])
        hs0 ?_ ?_ hab' ?_ ?_
      · rw [Units.val_mul]
        calc ((ρ a₁ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) *
              ((ρ a₁ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) =
              ((ρ a₁ : Matrix (Fin 4) (Fin 4) F) * (ρ a₁ : Matrix (Fin 4) (Fin 4) F)) *
                ((ρ a₀ : Matrix (Fin 4) (Fin 4) F) * (ρ a₀ : Matrix (Fin 4) (Fin 4) F)) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (ρ a₀ : Matrix (Fin 4) (Fin 4) F), hab' a₀ a₁, Matrix.mul_assoc]
          _ = (s * s) • (1 : Matrix (Fin 4) (Fin 4) F) := by
              rw [hd, hsq', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, ← hs]
      · intro b
        rw [Units.val_mul, ← Matrix.mul_assoc, hab' b a₁, Matrix.mul_assoc, hab' b a₀,
          ← Matrix.mul_assoc]
      · intro h
        rw [Units.val_mul] at h
        exact (ha₁ (c⁻¹ * s) (mul_ne_zero (inv_ne_zero hc0) hs0)).2 (key s h)
      · intro h
        rw [Units.val_mul, ← neg_smul] at h
        exact (ha₁ (c⁻¹ * -s) (mul_ne_zero (inv_ne_zero hc0) (neg_ne_zero.2 hs0))).2
          (key (-s) (by rw [h, neg_smul]))

end L4

end CFSG.GH74.Generic.BProg.B2
