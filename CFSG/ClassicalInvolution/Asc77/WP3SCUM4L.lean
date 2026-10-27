module

public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix

section Dich

variable {F : Type} [Field F]

theorem blockSL2_two_comm_zero (A B : SL(2, F)) :
    blockSL2 F 3 ⟨2, by omega⟩ A * blockSL2 F 3 ⟨0, by omega⟩ B =
      blockSL2 F 3 ⟨0, by omega⟩ B * blockSL2 F 3 ⟨2, by omega⟩ A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show CFSG.ClassicalInvolution.Phan.blockMat 4 2 (A : Matrix (Fin 2) (Fin 2) F) *
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (B : Matrix (Fin 2) (Fin 2) F) =
    CFSG.ClassicalInvolution.Phan.blockMat 4 0 (B : Matrix (Fin 2) (Fin 2) F) *
      CFSG.ClassicalInvolution.Phan.blockMat 4 2 (A : Matrix (Fin 2) (Fin 2) F)
  exact CFSG.ClassicalInvolution.Phan.blockMat_comm (Or.inr (by omega)) _ _

theorem partnerDiag_three_mul_self :
    partnerDiag (F := F) 3 1 * partnerDiag 3 1 = 1 := by
  apply Units.ext
  rw [Units.val_mul, partnerDiag, coe_diagGL, Matrix.diagonal_mul_diagonal, Units.val_one,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [partnerEnt]
  split_ifs <;> simp

theorem psl4_dichotomy [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (3 + 1)) {H : Type} [Group H] (ψ : SL(3 + 1, F) →* H)
    (hker : ψ.ker ≤ Subgroup.center SL(3 + 1, F)) {R : Subgroup SL(3 + 1, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 3 + 1 by norm_num)) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∃ R'' ∈ longRootSet (K := F) (show 2 ≤ 3 + 1 by norm_num),
        (∀ r ∈ R, ∀ s ∈ R'', r * s = s * r) ∧ ∀ s ∈ R'', v * ψ s = ψ s * v) ∨
      ∃ Y₀ : GL (Fin (3 + 1)) F, Y₀ * Y₀ = 1 ∧
        (∀ r ∈ R, Matrix.SpecialLinearGroup.toGL r * Y₀ = Y₀ * Matrix.SpecialLinearGroup.toGL r) ∧
        ∀ y : SL(3 + 1, F), v * ψ y * v⁻¹ = ψ (slConjugation (3 + 1) F Y₀ y) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hn : 2 ≤ 3 + 1 := by norm_num
  set S₂ : Subgroup SL(3 + 1, F) := (blockSL2 F 3 ⟨2, by omega⟩).range with hS₂
  set S₀ : Subgroup SL(3 + 1, F) := (blockSL2 F 3 ⟨0, by omega⟩).range with hS₀
  obtain ⟨g₀, hg₀⟩ := (mem_longRootSet_iff hn).mp hR
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : SL(3 + 1, F),
      S₂ = (rootSL2 F hn).map (MulAut.conj P₀).toMonoidHom := by
    have h1 := Lc_mem_longRootSet h2 hn (CFSG.ClassicalInvolution.RouteD.nodePair 3 2 (by omega))
    rw [← blockSL2_range_eq_Lc h2 (m := 3) (a := 2) (by omega)] at h1
    exact (mem_longRootSet_iff hn).mp h1
  set g : SL(3 + 1, F) := g₀ * P₀⁻¹ with hg
  have hRg : R = S₂.map (MulAut.conj g).toMonoidHom := by
    rw [hg₀, hP₀, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    group
  set R'' : Subgroup SL(3 + 1, F) := S₀.map (MulAut.conj g).toMonoidHom with hR''
  have hR''mem : R'' ∈ longRootSet (K := F) hn := (mem_longRootSet_iff hn).mpr ⟨g, rfl⟩
  clear_value g
  have hψg : ψ g ∈ ψ.range := ⟨g, rfl⟩
  set w : H := (ψ g)⁻¹ * v * ψ g with hwdef
  have hw : w ∈ Subgroup.normalizer (ψ.range : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hψg)) hv)
      (Subgroup.le_normalizer hψg)
  have hw2 : w * w = 1 := by
    calc w * w = (ψ g)⁻¹ * (v * v) * ψ g := by rw [hwdef]; group
      _ = 1 := by rw [hv2]; group
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwS : ∀ r ∈ S₂, w * ψ r = ψ r * w := by
    intro r hr
    have hmem : g * r * g⁻¹ ∈ R := by rw [hRg]; exact ⟨r, hr, rfl⟩
    have h := hvR _ hmem
    rw [map_mul, map_mul, map_inv] at h
    calc w * ψ r = (ψ g)⁻¹ * (v * (ψ g * ψ r * (ψ g)⁻¹)) * ψ g := by rw [hwdef]; group
      _ = (ψ g)⁻¹ * ((ψ g * ψ r * (ψ g)⁻¹) * v) * ψ g := by rw [h]
      _ = ψ r * w := by rw [hwdef]; group
  let σ : H ≃* H := MulAut.conj w
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    show w * (w * y * w⁻¹) * w⁻¹ = y
    rw [hwinv]
    calc w * (w * y * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2]; group
  have hstab : ∀ x, σ (ψ x) ∈ ψ.range := fun x =>
    (Subgroup.mem_normalizer_iff.mp hw (ψ x)).mp ⟨x, rfl⟩
  have hfix : ∀ A : SL(2, F), σ (ψ (blockSL2 F 3 ⟨2, by omega⟩ A)) =
      ψ (blockSL2 F 3 ⟨2, by omega⟩ A) := by
    intro A
    show w * ψ _ * w⁻¹ = ψ _
    rw [hwS _ ⟨A, rfl⟩]
    group
  by_cases hmove : ∃ A : SL(2, F), σ (ψ (blockSL2 F 3 ⟨0, by omega⟩ A)) ≠
      ψ (blockSL2 F 3 ⟨0, by omega⟩ A)
  · right
    obtain ⟨h, -, hfixh, hact⟩ := partner_chart_three_amb hodd h5 hcl ψ hker σ hσ hstab hfix hmove
    let pd : GL (Fin (3 + 1)) F := partnerDiag 3 1
    let Y₁ : GL (Fin (3 + 1)) F := h * pd * h⁻¹
    have hY₁sq : Y₁ * Y₁ = 1 := by
      calc Y₁ * Y₁ = h * (pd * pd) * h⁻¹ := by simp only [Y₁]; group
        _ = 1 := by rw [partnerDiag_three_mul_self]; group
    have hact' : ∀ y, σ (ψ y) = ψ (slConjugation (3 + 1) F Y₁ y) := by
      intro y
      have h1 := hact (slConjugation (3 + 1) F h⁻¹ y)
      have e1 : slConjugation (3 + 1) F h (slConjugation (3 + 1) F h⁻¹ y) = y := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [e1] at h1
      rw [h1]
      congr 1
      simp only [Y₁, pd, map_mul, MulAut.mul_apply]
    have hcomY : ∀ A : SL(2, F),
        Y₁ * Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A) =
          Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A) * Y₁ := by
      intro A
      set T : GL (Fin (3 + 1)) F := Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A)
        with hT
      have e1 : h * T * h⁻¹ = T := by
        have := toGL_slConjugation (3 + 1) F h (blockSL2 F 3 ⟨2, by omega⟩ A)
        rw [hfixh A] at this
        exact this.symm
      have e2 : pd * T * pd⁻¹ = T := by
        have := toGL_slConjugation (3 + 1) F pd (blockSL2 F 3 ⟨2, by omega⟩ A)
        rw [show slConjugation (3 + 1) F pd (blockSL2 F 3 ⟨2, by omega⟩ A) =
          blockSL2 F 3 ⟨2, by omega⟩ A from slConjugation_diagGL_blockSL2 (partnerEnt 3 1)
            ⟨2, by omega⟩ (by simp [partnerEnt]) A] at this
        exact this.symm
      have c1 : Commute h T := mul_inv_eq_iff_eq_mul.mp e1
      have c2 : Commute pd T := mul_inv_eq_iff_eq_mul.mp e2
      exact ((c1.mul_left c2).mul_left c1.inv_left).eq
    set G : GL (Fin (3 + 1)) F := Matrix.SpecialLinearGroup.toGL g with hG
    refine ⟨G * Y₁ * G⁻¹, ?_, ?_, ?_⟩
    · calc G * Y₁ * G⁻¹ * (G * Y₁ * G⁻¹) = G * (Y₁ * Y₁) * G⁻¹ := by group
        _ = 1 := by rw [hY₁sq]; group
    · intro r hr
      rw [hRg] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      obtain ⟨A, rfl⟩ := ha
      have e : Matrix.SpecialLinearGroup.toGL
          ((MulAut.conj g).toMonoidHom (blockSL2 F 3 ⟨2, by omega⟩ A)) =
          G * Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A) * G⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hG]
      rw [e]
      calc G * Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A) * G⁻¹ *
            (G * Y₁ * G⁻¹)
          = G * (Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A) * Y₁) * G⁻¹ := by
            group
        _ = G * (Y₁ * Matrix.SpecialLinearGroup.toGL (blockSL2 F 3 ⟨2, by omega⟩ A)) * G⁻¹ := by
            rw [hcomY A]
        _ = _ := by group
    · intro y
      have hSL : slConjugation (3 + 1) F (G * Y₁ * G⁻¹) y =
          g * slConjugation (3 + 1) F Y₁ (g⁻¹ * y * g) * g⁻¹ := by
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [toGL_slConjugation (3 + 1) F (G * Y₁ * G⁻¹) y]
        simp only [map_mul, map_inv, toGL_slConjugation, hG]
        group
      rw [hSL, map_mul, map_mul, map_inv, ← hact' (g⁻¹ * y * g)]
      show v * ψ y * v⁻¹ = ψ g * (w * ψ (g⁻¹ * y * g) * w⁻¹) * (ψ g)⁻¹
      rw [map_mul, map_mul, map_inv, hwdef]
      group
  · left
    push Not at hmove
    have hwS₀ : ∀ r ∈ S₀, w * ψ r = ψ r * w := by
      rintro r ⟨A, rfl⟩
      have := hmove A
      have e : w * ψ (blockSL2 F 3 ⟨0, by omega⟩ A) * w⁻¹ =
          ψ (blockSL2 F 3 ⟨0, by omega⟩ A) := this
      calc w * ψ (blockSL2 F 3 ⟨0, by omega⟩ A)
          = w * ψ (blockSL2 F 3 ⟨0, by omega⟩ A) * w⁻¹ * w := by group
        _ = ψ (blockSL2 F 3 ⟨0, by omega⟩ A) * w := by rw [e]
    refine ⟨R'', hR''mem, ?_, ?_⟩
    · rintro r hr _ ⟨b, hb, rfl⟩
      rw [hRg] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      obtain ⟨A, rfl⟩ := ha
      obtain ⟨B, rfl⟩ := hb
      have hc := blockSL2_two_comm_zero A B
      show g * blockSL2 F 3 ⟨2, by omega⟩ A * g⁻¹ * (g * blockSL2 F 3 ⟨0, by omega⟩ B * g⁻¹) =
        g * blockSL2 F 3 ⟨0, by omega⟩ B * g⁻¹ * (g * blockSL2 F 3 ⟨2, by omega⟩ A * g⁻¹)
      calc g * blockSL2 F 3 ⟨2, by omega⟩ A * g⁻¹ * (g * blockSL2 F 3 ⟨0, by omega⟩ B * g⁻¹)
          = g * (blockSL2 F 3 ⟨2, by omega⟩ A * blockSL2 F 3 ⟨0, by omega⟩ B) * g⁻¹ := by group
        _ = g * (blockSL2 F 3 ⟨0, by omega⟩ B * blockSL2 F 3 ⟨2, by omega⟩ A) * g⁻¹ := by rw [hc]
        _ = _ := by group
    · rintro _ ⟨b, hb, rfl⟩
      have h1 := hwS₀ b hb
      show v * ψ (g * b * g⁻¹) = ψ (g * b * g⁻¹) * v
      rw [map_mul, map_mul, map_inv]
      calc v * (ψ g * ψ b * (ψ g)⁻¹) = ψ g * (w * ψ b) * (ψ g)⁻¹ := by rw [hwdef]; group
        _ = ψ g * (ψ b * w) * (ψ g)⁻¹ := by rw [h1]
        _ = (ψ g * ψ b * (ψ g)⁻¹) * v := by rw [hwdef]; group

end Dich

end CFSG.ClassicalInvolution.Asc77
