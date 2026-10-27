module

public import CFSG.GH74.GLS.IVK.Lifted.SLSign
public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)
open CFSG.GH74.GLS.IVK.Lifted (gammaOf slFieldAut)

section Compat

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem congr_sq {K : Subgroup H} (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) {x : H}
    (hx : x ∈ normalizer (K : Set H)) {p : H} (hp : p ∈ K)
    (hxp : ∀ y ∈ K, x * (x * y * x⁻¹) * x⁻¹ = p * y * p⁻¹) :
    (MulAut.congr ê (K.normalizerMonoidHom ⟨x, hx⟩)) * (MulAut.congr ê (K.normalizerMonoidHom ⟨x, hx⟩)) =
      MulAut.conj (ê ⟨p, hp⟩) := by
  apply MulEquiv.ext
  intro b
  rw [MulAut.mul_apply, congr_apply_eq, congr_apply_eq, MulEquiv.symm_apply_apply, MulAut.conj_apply]
  have h2 : K.normalizerMonoidHom ⟨x, hx⟩ (K.normalizerMonoidHom ⟨x, hx⟩ (ê.symm b)) =
      ⟨p, hp⟩ * ê.symm b * ⟨p, hp⟩⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact hxp _ (ê.symm b).2
  rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem fixes_of_fieldTriv {K : Subgroup H} (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    {x : H} (hx : x ∈ normalizer (K : Set H)) {p : H} (hp : p ∈ K)
    (hxp : ∀ y ∈ K, x * (x * y * x⁻¹) * x⁻¹ = p * y * p⁻¹)
    (hσ : (coordHom K ê hF ⟨x, hx⟩).2 = 1) : x * p * x⁻¹ = p := by
  set α : MulAut (SpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ê (K.normalizerMonoidHom ⟨x, hx⟩) with hα
  have hα2 : α * α = MulAut.conj (ê ⟨p, hp⟩) := congr_sq ê hx hp hxp
  have hcoord : coordHom K ê hF ⟨x, hx⟩ = outHom hF α := rfl
  rw [hcoord] at hσ
  obtain ⟨G, hG, -⟩ := exists_rep' hF α
  rw [hσ] at hG
  have hG1 : ∀ b : SpecialLinearGroup (Fin 2) F,
      SpecialLinearGroup.toGL (α b) = G * SpecialLinearGroup.toGL b * G⁻¹ := by
    intro b
    rw [hG b, CFSG.GH74.GLS.IVK.glMap_one]
  set P : GL (Fin 2) F := SpecialLinearGroup.toGL (ê ⟨p, hp⟩) with hP
  have hG2 : ∀ b : SpecialLinearGroup (Fin 2) F,
      G * G * SpecialLinearGroup.toGL b * (G * G)⁻¹ = P * SpecialLinearGroup.toGL b * P⁻¹ := by
    intro b
    have h1 := congrArg (fun f : MulAut (SpecialLinearGroup (Fin 2) F) => SpecialLinearGroup.toGL (f b)) hα2
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [hG1, hG1] at h1
    have h2 : SpecialLinearGroup.toGL (ê ⟨p, hp⟩ * b * (ê ⟨p, hp⟩)⁻¹) =
        P * SpecialLinearGroup.toGL b * P⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h2] at h1
    rw [← h1]; group
  have hcomm : ∀ b : SpecialLinearGroup (Fin 2) F,
      (((P⁻¹ * (G * G) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) =
        (b : Matrix (Fin 2) (Fin 2) F) * (((P⁻¹ * (G * G) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro b
    have h3 : P⁻¹ * (G * G) * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL b * (P⁻¹ * (G * G)) := by
      calc P⁻¹ * (G * G) * SpecialLinearGroup.toGL b
          = P⁻¹ * (G * G * SpecialLinearGroup.toGL b * (G * G)⁻¹) * (G * G) := by group
        _ = P⁻¹ * (P * SpecialLinearGroup.toGL b * P⁻¹) * (G * G) := by rw [hG2 b]
        _ = SpecialLinearGroup.toGL b * (P⁻¹ * (G * G)) := by group
    exact congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
  obtain ⟨μ, hμ⟩ := CFSG.GH74.GLS.IVK.exists_smul_one_of_commute_sl _ hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hdet : IsUnit (((P⁻¹ * (G * G) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) :=
      Units.isUnit _
    rw [hμ, h0, zero_smul, Matrix.isUnit_iff_isUnit_det] at hdet
    simp at hdet
  have hGG : ((G : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) =
      μ • (P : Matrix (Fin 2) (Fin 2) F) := by
    obtain ⟨N, hNdef⟩ : ∃ N : GL (Fin 2) F, N = P⁻¹ * (G * G) := ⟨_, rfl⟩
    rw [← hNdef] at hμ
    have h1 : G * G = P * N := by rw [hNdef]; group
    have h2 : ((G * G : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (P : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F) := by
      rw [h1]; rfl
    rw [hμ, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  have hGP' : (G : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) =
      (P : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    have h3 : (G : Matrix (Fin 2) (Fin 2) F) * ((G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) =
        ((G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.mul_assoc]
    rw [hGG, Matrix.mul_smul, Matrix.smul_mul] at h3
    exact smul_right_injective _ hμ0 h3
  have hGP : G * P * G⁻¹ = P := by
    have : G * P = P * G := Units.ext hGP'
    rw [this]; group
  have hα1 : SpecialLinearGroup.toGL (α (ê ⟨p, hp⟩)) = P := by
    rw [hG1]; exact hGP
  have hαp : α (ê ⟨p, hp⟩) = ê ⟨p, hp⟩ := SpecialLinearGroup.toGL_injective hα1
  have h4 : α (ê ⟨p, hp⟩) = ê ⟨x * p * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx p).mp hp⟩ := by
    rw [hα, congr_apply_eq, MulEquiv.symm_apply_apply]
    congr 1
  rw [h4] at hαp
  have := ê.injective hαp
  exact congrArg Subtype.val this

theorem not_fixes_of_bad {K : Subgroup H} (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    {x : H} (hx : x ∈ normalizer (K : Set H)) {p : H} (hp : p ∈ K)
    (hxp : ∀ y ∈ K, x * (x * y * x⁻¹) * x⁻¹ = p * y * p⁻¹)
    (hσ : (coordHom K ê hF ⟨x, hx⟩).2 ≠ 1) (hε : (coordHom K ê hF ⟨x, hx⟩).1 ≠ 1) :
    x * p * x⁻¹ ≠ p := by
  intro hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : MulAut (SpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ê (K.normalizerMonoidHom ⟨x, hx⟩) with hα
  have hα2 : α * α = MulAut.conj (ê ⟨p, hp⟩) := congr_sq ê hx hp hxp
  have hcoord : coordHom K ê hF ⟨x, hx⟩ = outHom hF α := rfl
  rw [hcoord] at hσ hε
  have hsq : (outHom hF α).2 ^ 2 = 1 := by
    have h1 : outHom hF (α * α) = 1 := by
      rw [hα2]; exact (outHom_eq_one_iff hF _).mpr ⟨_, rfl⟩
    rw [map_mul] at h1
    have := congrArg Prod.snd h1
    simpa [sq] using this
  have hord : orderOf (gammaOf hF.odd hF.gt3 α).right = 2 := by
    rw [← outHom_snd hF]
    exact orderOf_eq_prime hsq hσ
  have hk : α ^ orderOf (gammaOf hF.odd hF.gt3 α).right = MulAut.conj (ê ⟨p, hp⟩) := by
    rw [hord, sq]; exact hα2
  have hαk : α (ê ⟨p, hp⟩) = ê ⟨p, hp⟩ := by
    have h4 : α (ê ⟨p, hp⟩) = ê ⟨x * p * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx p).mp hp⟩ := by
      rw [hα, congr_apply_eq, MulEquiv.symm_apply_apply]
      congr 1
    rw [h4]
    congr 1
    exact Subtype.ext hfix
  have := CFSG.GH74.GLS.IVK.Lifted.sign_aut hF.odd hF.gt3 α (ê ⟨p, hp⟩) hk hαk
  exact hε this

omit [Group H] [Field F] [Finite F] in
theorem fix_iff_of_sq {x p₁ p₂ : H} [Group H] (hxx : x * x = p₁ * p₂) :
    x * p₁ * x⁻¹ = p₁ ↔ x * p₂ * x⁻¹ = p₂ := by
  have h : (x * p₁ * x⁻¹) * (x * p₂ * x⁻¹) = p₁ * p₂ := by
    calc (x * p₁ * x⁻¹) * (x * p₂ * x⁻¹) = x * (p₁ * p₂) * x⁻¹ := by group
      _ = x * (x * x) * x⁻¹ := by rw [hxx]
      _ = x * x := by group
      _ = p₁ * p₂ := hxx
  constructor
  · intro h1
    rw [h1] at h
    exact mul_left_cancel h
  · intro h2
    rw [h2] at h
    exact mul_right_cancel h

end Compat

section CompatPair

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H}
  {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

theorem compat_fieldTriv (hS : Setting H K₁ K₂ z) (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F₁)
    (ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F₂) (hF₁ : GoodF F₁) (hF₂ : GoodF F₂) {x : H}
    (hx : x ∈ normalizer (K₁ : Set H)) (hx2 : x * x ∈ K₁ ⊔ K₂)
    (h1 : (coordHom K₁ ê₁ hF₁ ⟨x, hx⟩).2 = 1) :
    ¬ ((coordHom K₂ ê₂ hF₂ ⟨x, hS.normalizer₁₂ hx⟩).2 ≠ 1 ∧
        (coordHom K₂ ê₂ hF₂ ⟨x, hS.normalizer₁₂ hx⟩).1 ≠ 1) := by
  rintro ⟨hσ, hε⟩
  obtain ⟨p₁, hp₁, p₂, hp₂, hxx⟩ := (mem_sup_of_comm hS.comm (x * x)).mp hx2
  have hxp₁ : ∀ y ∈ K₁, x * (x * y * x⁻¹) * x⁻¹ = p₁ * y * p₁⁻¹ := by
    intro y hy
    have hc := hS.comm y hy p₂ hp₂
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = (p₁ * p₂) * y * (p₁ * p₂)⁻¹ := by rw [hxx]
      _ = p₁ * (p₂ * y * p₂⁻¹) * p₁⁻¹ := by group
      _ = p₁ * y * p₁⁻¹ := by
        have h2 : p₂ * y * p₂⁻¹ = y := by rw [hc.symm]; group
        rw [h2]
  have hxp₂ : ∀ y ∈ K₂, x * (x * y * x⁻¹) * x⁻¹ = p₂ * y * p₂⁻¹ := by
    intro y hy
    have hc := hS.comm p₁ hp₁ y hy
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = (p₁ * p₂) * y * (p₁ * p₂)⁻¹ := by rw [hxx]
      _ = (p₁ * (p₂ * y * p₂⁻¹)) * p₁⁻¹ := by group
      _ = p₂ * y * p₂⁻¹ := by
        have h3 : p₁ * (p₂ * y * p₂⁻¹) * p₁⁻¹ = p₂ * y * p₂⁻¹ := by
          have := hS.comm p₁ hp₁ (p₂ * y * p₂⁻¹) (K₂.mul_mem (K₂.mul_mem hp₂ hy) (K₂.inv_mem hp₂))
          rw [this]; group
        exact h3
  have hfix₁ := fixes_of_fieldTriv ê₁ hF₁ hx hp₁ hxp₁ h1
  have hfix₂ : x * p₂ * x⁻¹ = p₂ := (fix_iff_of_sq hxx).mp hfix₁
  exact not_fixes_of_bad ê₂ hF₂ (hS.normalizer₁₂ hx) hp₂ hxp₂ hσ hε hfix₂

end CompatPair
end CFSG.GH74.GLS.IVK.Prod3
