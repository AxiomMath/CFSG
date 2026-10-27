module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpZ
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpForms
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalance
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpRigid

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.ClassicalInvolution.Balance
open scoped Matrix MatrixGroups

variable {F : Type} [Field F] {X : Type} [Group X]

theorem zLemma_std [Finite F] [Finite X] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hodd : ringChar F ≠ 2) (ψ : StatedSp 2 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hnorm : ψ.range.Normal) {f : X}
    (hf : ∀ y, f * ψ y * f⁻¹ = ψ (longInv F 2 0 * y * (longInv F 2 0)⁻¹)) (hff : f * f = 1)
    (hfaith : ¬ ∀ y ∈ ψ.range, f * y = y * f) {d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) : ∀ y, d * ψ y * d⁻¹ = ψ y := by
  classical
  have hsub : CFSG.Open.IsSubnormal ψ.range ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hcomm : ∀ a : Fin 2, ∀ s ∈ longRootSp2 F 2 a, d * ψ s = ψ s * d := by
    intro a s hs
    have hQ := isComponentOf_longRootSp2 h2 h4 a
    have hmain := isComponentOf_map_centralizer hker 1 f (MulAut.conj (longInv F 2 0))
      (fun y => by simpa using hf y) hQ
    have e : (MulAut.conj (1 : StatedSp 2 F)).toMonoidHom = MonoidHom.id _ := by
      ext
      simp
    rw [e, MonoidHom.comp_id] at hmain
    have hle := le_centralizerLayer_of_isComponentOf hsub hmain
    exact commute_of_mem_involutionOddCore_of_mem_centralizerLayer hd (hle ⟨s, hs, rfl⟩)
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift_conj hodd h4 ψ hker hnorm d
  have hfix : ∀ a : Fin 2, ∀ s ∈ longRootSp2 F 2 a, conjSp 2 F A (fieldSp 2 F σ s) = s := by
    intro a s hs
    have : Group.IsPerfect (longRootSp2 F 2 a) := ⟨(isQuasisimple_longRootSp2 h4 a).1⟩
    have key := hom_eq_of_central_ker ψ hker
      (((conjSp 2 F A).toMonoidHom.comp (fieldSp 2 F σ).toMonoidHom).comp
        (longRootSp2 F 2 a).subtype)
      (longRootSp2 F 2 a).subtype (fun l => by
        have h1 := hAσ l
        have h2' : d * ψ l * d⁻¹ = ψ l := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hcomm a l l.2
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
        rw [← h1, h2'])
    have h := MonoidHom.ext_iff.mp key ⟨s, hs⟩
    exact h
  have hU : ∀ (a : Fin 2) (c : F), simMat A * (Matrix.transvection (Sum.inl a) (Sum.inr a) c).map σ
      = Matrix.transvection (Sum.inl a) (Sum.inr a) c * simMat A := by
    intro a c
    have := mul_eq_of_conjSp_eq A σ (hfix a _ ⟨CFSG.LieType.Steinberg.sl2Upper c, rfl⟩)
    rwa [mat_longBlock_upper] at this
  have hL : ∀ (a : Fin 2) (c : F), simMat A * (Matrix.transvection (Sum.inr a) (Sum.inl a) c).map σ
      = Matrix.transvection (Sum.inr a) (Sum.inl a) c * simMat A := by
    intro a c
    have := mul_eq_of_conjSp_eq A σ (hfix a _ ⟨CFSG.LieType.Steinberg.sl2Lower c, rfl⟩)
    rwa [mat_longBlock_lower] at this
  have hAB := simMat_mul A
  have hσ : ∀ c, σ c = c := (rigid_transvection σ hAB (Sum.inl 0) (Sum.inr 0) (hU 0)).1
  obtain ⟨u, hu⟩ := exists_diagonal_of_commute
    (fun a => (rigid_transvection σ hAB _ _ (hU a)).2)
    (fun a => (rigid_transvection σ hAB _ _ (hL a)).2)
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hsim : (Matrix.diagonal (Sum.elim u u))ᵀ * gram F 2 * Matrix.diagonal (Sum.elim u u) =
      (μ : F) • gram F 2 := by
    rw [← hu]
    exact hμ
  have hu0 := sq_eq_of_similitude hsim 0
  have hu1 := sq_eq_of_similitude hsim 1
  have hcase : u 1 = u 0 ∨ u 1 = -u 0 := mul_self_eq_mul_self_iff.mp (hu1.trans hu0.symm)
  intro y
  have hy := hAσ y
  rw [fieldSp_eq_self hσ] at hy
  rcases hcase with h | h
  · rw [hy]
    have hscalar : simMat A = u 0 • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      rw [hu]
      ext r t
      rcases r with a | a <;> rcases t with b | b <;> fin_cases a <;> fin_cases b <;>
        simp [h]
    have : conjSp 2 F A y = y := by
      refine conjSp_eq_of_mul_eq A ?_
      rw [hscalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [this]
  · exfalso
    have hcx : simMat A = (-u 0) • mat 2 F (longInv F 2 0) := by
      rw [hu, mat_longInv]
      ext r t
      rcases r with a | a <;> rcases t with b | b <;> fin_cases a <;> fin_cases b <;>
        simp [coords, h]
    have hinv : mat 2 F (longInv F 2 0)⁻¹ * mat 2 F (longInv F 2 0) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hconj : ∀ y, conjSp 2 F A y = longInv F 2 0 * y * (longInv F 2 0)⁻¹ := by
      intro y
      refine conjSp_eq_of_mul_eq A ?_
      rw [hcx, map_mul, map_mul, Matrix.smul_mul, Matrix.mul_smul]
      simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
    have hfd : f * d = d * f :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (involutionOddCore_le_centralizer f hd)).symm
    refine false_of_conj_eq (L := ψ.range) hfd hff (odd_orderOf_of_mem_involutionOddCore hd) ?_
      hfaith
    rintro _ ⟨z, rfl⟩
    rw [hAσ z, fieldSp_eq_self hσ, hconj, hf]


theorem zLemma [Finite F] [Finite X] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hodd : ringChar F ≠ 2) (ψ : StatedSp 2 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hnorm : ψ.range.Normal)
    {x : StatedSp 2 F} (hx : x * x = 1) (h1 : x ≠ 1) (hn : x ≠ negOne) {f : X}
    (hf : ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) (hff : f * f = 1)
    (hfaith : ¬ ∀ y ∈ ψ.range, f * y = y * f) {d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) : ∀ y, d * ψ y * d⁻¹ = ψ y := by
  obtain ⟨g, hg⟩ := exists_conj_longInv h2 hx h1 hn
  have hx' : x = g * longInv F 2 0 * g⁻¹ := by rw [← hg]; group
  set Ψ : StatedSp 2 F →* X := ψ.comp (MulAut.conj g).toMonoidHom with hΨdef
  have hΨ : ∀ y, Ψ y = ψ (g * y * g⁻¹) := fun y => rfl
  have hrange : Ψ.range = ψ.range := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨g⁻¹ * y * g, by rw [hΨ]; congr 1; group⟩
  have hkerΨ : Ψ.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ Subgroup.center (StatedSp 2 F) := hker (by simpa [hΨ] using hy)
    have h2 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center _).Normal) _ h1 g⁻¹
    have e1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e1] at h2
  have hnormΨ : Ψ.range.Normal := by rw [hrange]; exact hnorm
  have hfΨ : ∀ y, f * Ψ y * f⁻¹ = Ψ (longInv F 2 0 * y * (longInv F 2 0)⁻¹) := by
    intro y
    rw [hΨ, hΨ, hf, hx']
    congr 1
    group
  have key := zLemma_std h2 h4 hodd Ψ hkerΨ hnormΨ hfΨ hff (by rwa [hrange]) hd
  intro y
  have := key (g⁻¹ * y * g)
  rwa [hΨ, show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
