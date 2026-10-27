module

public import CFSG.ClassicalInvolution.Asc77.AscT8V12
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups commutatorElement

namespace T8V

section Sp

variable {F : Type} [Field F] [Finite F]

theorem e4_sp_sigma (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 2 F →* X) {R R' : Subgroup (StatedSp 2 F)} {y y' : StatedSp 2 F}
    (hP : E4Pair ψ R R' y y') (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) :
    ∀ σ : MulAut X, (∀ r ∈ R, σ (ψ r) = ψ r) → (∀ r ∈ R', σ (ψ r) = ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
  intro σ hσ hσ' hσ4
  refine sq_eq_one_of_autVac hP.perf ψ hP.surj hP.ker (proj 2 F) proj_surjective ?_ ?_ σ hσ hσ' hσ4
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro φ hφ hφ' _
    have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
      have := hP.cen
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
      rw [hyi, ← hP.comm y hP.hy y' hP.hy']
      exact this
    exact ModelFacts.Orth15.OuterSp4.psp4_autVac h2 h4 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy'
      hP.hy'2 hP.hy'1 hc φ hφ hφ'

omit [Finite F] in
theorem e4_sp_inner (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    (ψ : StatedSp 2 F →* X) {R R' : Subgroup (StatedSp 2 F)} {y y' : StatedSp 2 F}
    (hP : E4Pair ψ R R' y y') (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) :
    ∀ s : StatedSp 2 F, (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ ψ.ker, s * s ≠ y * y' * k := by
  intro s hs hs' k hk hsk
  have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, k₀, hRg, hR'g⟩ := ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hR hR' hP.ne hP.hy
    hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hc
  have hkk : ∀ k k₀ : Fin 2, k₀ = k ∨ k₀ = Fin.rev k := by decide
  have hcomm : ∀ (L S₁ : Subgroup (StatedSp 2 F)),
      S₁ = L.map (MulAut.conj g).toMonoidHom → (∀ r ∈ S₁, s * r = r * s) →
      ∀ r ∈ L, (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro L S₁ hS₁ hS r hr
    have hmem : g * r * g⁻¹ ∈ S₁ := by
      rw [hS₁]
      exact ⟨r, hr, rfl⟩
    have h := hS _ hmem
    calc (g⁻¹ * s * g) * r = g⁻¹ * (s * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * s) * g := by rw [h]
      _ = r * (g⁻¹ * s * g) := by group
  have hcommj : ∀ j : Fin 2, ∀ r ∈ (longBlock F 2 j).range,
      (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro j
    rcases hkk k₀ j with rfl | rfl
    · exact hcomm _ R hRg hs
    · exact hcomm _ R' hR'g hs'
  generalize hs₀ : g⁻¹ * s * g = s₀ at hcommj
  have hu : ∀ (j : Fin 2) (t : F),
      mat 2 F s₀ * Matrix.transvection (Sum.inl j) (Sum.inr j) t =
        Matrix.transvection (Sum.inl j) (Sum.inr j) t * mat 2 F s₀ := by
    intro j t
    have hg := hcommj j (longBlock F 2 j (sl2Upper t)) ⟨_, rfl⟩
    have := congrArg (mat 2 F) hg
    rwa [map_mul, map_mul, longBlock_sl2Upper, mat_elt_positiveLong] at this
  have hl : ∀ (j : Fin 2) (t : F),
      mat 2 F s₀ * Matrix.transvection (Sum.inr j) (Sum.inl j) t =
        Matrix.transvection (Sum.inr j) (Sum.inl j) t * mat 2 F s₀ := by
    intro j t
    have hg := hcommj j (longBlock F 2 j (sl2Lower t)) ⟨_, rfl⟩
    have := congrArg (mat 2 F) hg
    rwa [map_mul, map_mul, longBlock_sl2Lower, mat_elt_negativeLong] at this
  have hdet : (mat 2 F s₀).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (s₀ : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨-, a, b, ha, hb, hab⟩ := ModelFacts.Orth15.OuterSp4.sp4_shape (RingEquiv.refl F)
    (mat 2 F s₀) hdet (fun j t => by simpa using hu j t) (fun j t => by simpa using hl j t)
  have hsymp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp s₀.2
  have hsymp' : (mat 2 F s₀)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * mat 2 F s₀ =
      Matrix.fromBlocks 0 1 (-1) 0 := hsymp
  rw [hab, Matrix.diagonal_transpose] at hsymp'
  have e0 := congrFun (congrFun hsymp' (Sum.inl 0)) (Sum.inr 0)
  have e1 := congrFun (congrFun hsymp' (Sum.inl 1)) (Sum.inr 1)
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at e0 e1
  have hss : s₀ * s₀ = 1 := by
    apply mat_injective
    rw [map_mul, map_one, hab, ModelFacts.Orth15.OuterSp4.diag_sq a b (by rw [e0, e1]), e0,
      one_smul]
  have hs : s = g * s₀ * g⁻¹ := by rw [← hs₀]; group
  have hsq : s * s = 1 := by
    calc s * s = (g * s₀ * g⁻¹) * (g * s₀ * g⁻¹) := by rw [← hs]
      _ = g * (s₀ * s₀) * g⁻¹ := by group
      _ = 1 := by rw [hss]; group
  rw [hsq] at hsk
  exact hP.nontwin (by rw [eq_inv_of_mul_eq_one_left hsk.symm]; exact ψ.ker.inv_mem hk)

end Sp

end T8V
end CFSG.ClassicalInvolution.Asc77
