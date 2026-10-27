module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Shape

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Q3L

open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.Q3.TA3
  Matrix
open scoped MatrixGroups

theorem sq_eq_neg_det {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : ¬ IsSquare M.det) {μ : F} (h : M * M = μ • (1 : Matrix (Fin 2) (Fin 2) F)) :
    μ = -M.det := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_one,
    mul_zero] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  by_cases hs : M 0 0 + M 1 1 = 0
  · have hd : M 1 1 = -M 0 0 := by linear_combination hs
    rw [hd]
    linear_combination -e00
  · exfalso
    have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have had : M 0 0 = M 1 1 := by
      have : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by
        rw [hb, hc] at e00 e11
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
    apply hM
    rw [Matrix.det_fin_two, hb, hc, had]
    exact ⟨M 1 1, by ring⟩

section Conj

variable {Y : Type} [Group Y] {τ : Y} {I : Subgroup Y} {F : Type} [Field F] {e : ↥I ≃* SL(2, F)}
  {g : GL (Fin 2) F}

theorem mul_conj_eq_one (hD : ConjData τ I e g) (hτ : τ * τ = 1) (h2 : (2 : F) ≠ 0)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) {a : Y} (ha : a ∈ I)
    (hsgn : e ⟨a * (τ * a * τ⁻¹), mul_mem ha (hD.conj_mem ha)⟩ = 1 ∨
      e ⟨a * (τ * a * τ⁻¹), mul_mem ha (hD.conj_mem ha)⟩ = -1) :
    a * (τ * a * τ⁻¹) = 1 := by
  rcases hsgn with h1 | h1
  · exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
  exfalso
  obtain ⟨y, hy, hey⟩ := hD ⟨a, ha⟩
  have hya : y = ⟨τ * a * τ⁻¹, hD.conj_mem ha⟩ := Subtype.ext hy
  set A : Matrix (Fin 2) (Fin 2) F := ((e ⟨a, ha⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    with hA
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hG
  set Gi : Matrix (Fin 2) (Fin 2) F := ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hGi, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGiG' : ∀ Z : Matrix (Fin 2) (Fin 2) F, Gi * (G * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  have hprod : A * (G * A * Gi) = -1 := by
    have h3 : (⟨a * (τ * a * τ⁻¹), mul_mem ha (hD.conj_mem ha)⟩ : ↥I) = ⟨a, ha⟩ * y := by
      rw [hya]; rfl
    have h4 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [h3, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one] at h4
    rw [hey] at h4
    exact h4
  obtain ⟨μ, hμ⟩ := hD.sq_scalar hτ
  have hdetG : ¬ IsSquare G.det := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at hns
  have hμ' : μ = -G.det := sq_eq_neg_det G hdetG hμ
  have hsq : (A * G) * (A * G) = (-μ) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc (A * G) * (A * G) = (A * (G * A * Gi)) * (G * G) := by
          simp only [Matrix.mul_assoc, hGiG']
      _ = (-μ) • 1 := by rw [hprod, hμ, neg_smul, Matrix.neg_mul, Matrix.one_mul]
  have hdetAG : (A * G).det = G.det := by
    rw [Matrix.det_mul, hA, (e ⟨a, ha⟩).2, one_mul]
  have hns' : ¬ IsSquare (A * G).det := by rw [hdetAG]; exact hdetG
  have hν : -μ = -(A * G).det := sq_eq_neg_det _ hns' hsq
  rw [hdetAG, ← hμ'] at hν
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hdetG
    have : G.det = 0 := by linear_combination hμ' - h0
    rw [this]
    exact ⟨0, by ring⟩
  have h2μ : (2 : F) * μ = 0 := by linear_combination -hν
  exact hμ0 ((mul_eq_zero.mp h2μ).resolve_left h2)

end Conj

variable {X : Type} [Group X] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem eq_one_or_z_of_mul_self₁ (Sh : Shape X F₁ F₂) (h2 : (2 : F₁) ≠ 0) {a : X}
    (ha : a ∈ Sh.I₁) (haa : a * a = 1) : a = 1 ∨ a = Sh.z := by
  have hsq : Sh.e₁ ⟨a, ha⟩ ^ 2 = 1 := by
    rw [sq, ← map_mul, ← map_one Sh.e₁]
    exact congrArg Sh.e₁ (Subtype.ext haa)
  rcases eq_one_or_neg_one_of_sq_eq_one h2 hsq with h | h
  · exact Or.inl (congrArg Subtype.val (Sh.e₁.injective (h.trans (map_one _).symm)))
  · exact Or.inr (congrArg Subtype.val (Sh.e₁.injective (h.trans Sh.e₁_z.symm)))

theorem eq_one_or_z_of_mul_self₂ (Sh : Shape X F₁ F₂) (h2 : (2 : F₂) ≠ 0) {b : X}
    (hb : b ∈ Sh.I₂) (hbb : b * b = 1) : b = 1 ∨ b = Sh.z :=
  eq_one_or_z_of_mul_self₁ Sh.swap h2 hb hbb

theorem eq_one_or_z_of_mem_inter (Sh : Shape X F₁ F₂) {x : X} (h₁ : x ∈ Sh.I₁)
    (h₂ : x ∈ Sh.I₂) : x = 1 ∨ x = Sh.z := by
  have : x ∈ Sh.I₁ ⊓ Sh.I₂ := ⟨h₁, h₂⟩
  rw [Sh.inter] at this
  exact Ivk47ab.mem_zpowers_of_sq Sh.z_sq this

theorem mul_conj_eq_one₁ (Sh : Shape X F₁ F₂) (h2 : (2 : F₁) ≠ 0) {a : X} (ha : a ∈ Sh.I₁)
    (ha₂ : a * (Sh.t * a * Sh.t⁻¹) ∈ Sh.I₂) : a * (Sh.t * a * Sh.t⁻¹) = 1 := by
  refine mul_conj_eq_one Sh.act₁ Sh.t_sq h2 Sh.ns₁ ha ?_
  rcases eq_one_or_z_of_mem_inter Sh (mul_mem ha (Sh.act₁.conj_mem ha)) ha₂ with h | h
  · left
    rw [← map_one Sh.e₁]
    exact congrArg Sh.e₁ (Subtype.ext h)
  · right
    rw [← Sh.e₁_z]
    exact congrArg Sh.e₁ (Subtype.ext h)

theorem mem_or_of_mul_self (Sh : Shape X F₁ F₂) (h2₁ : (2 : F₁) ≠ 0) (h2₂ : (2 : F₂) ≠ 0)
    {c : X} (hc : c * c = Sh.z) : c ∈ Sh.I₁ ∨ c ∈ Sh.I₂ := by
  rcases Q3Sh.mem_sup_or Sh c with hcs | hcs
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute Sh.comm hcs
    have hab : a * b = b * a := Sh.comm a ha b hb
    have hsq : (a * a) * (b * b) = Sh.z := by
      rw [← hc]
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [hab]
        _ = a * b * (a * b) := by group
    have haa₂ : a * a ∈ Sh.I₂ := by
      have : a * a = Sh.z * (b * b)⁻¹ := by rw [← hsq]; group
      rw [this]
      exact mul_mem Sh.z_mem₂ (inv_mem (mul_mem hb hb))
    rcases eq_one_or_z_of_mem_inter Sh (mul_mem ha ha) haa₂ with h1 | h1
    · right
      rcases eq_one_or_z_of_mul_self₁ Sh h2₁ ha h1 with rfl | rfl
      · rwa [one_mul]
      · exact mul_mem Sh.z_mem₂ hb
    · left
      have hbb : b * b = 1 := by
        rw [h1] at hsq
        calc b * b = Sh.z⁻¹ * (Sh.z * (b * b)) := by group
          _ = 1 := by rw [hsq, inv_mul_cancel]
      rcases eq_one_or_z_of_mul_self₂ Sh h2₂ hb hbb with rfl | rfl
      · rwa [mul_one]
      · exact mul_mem ha Sh.z_mem₁
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute Sh.comm hcs
    have hτi : Sh.t⁻¹ = Sh.t := inv_eq_of_mul_eq_one_right Sh.t_sq
    have hcab : c = a * b * Sh.t := by
      calc c = c * Sh.t * Sh.t⁻¹ := by group
        _ = a * b * Sh.t := by rw [← hab, hτi]
    have ha' : Sh.t * a * Sh.t⁻¹ ∈ Sh.I₁ := Sh.act₁.conj_mem ha
    have hb' : Sh.t * b * Sh.t⁻¹ ∈ Sh.I₂ := Sh.act₂.conj_mem hb
    have hcomm : (Sh.t * a * Sh.t⁻¹) * b = b * (Sh.t * a * Sh.t⁻¹) := Sh.comm _ ha' b hb
    have hcc : c * c = (a * (Sh.t * a * Sh.t⁻¹)) * (b * (Sh.t * b * Sh.t⁻¹)) := by
      rw [hcab]
      calc a * b * Sh.t * (a * b * Sh.t)
          = a * b * (Sh.t * a * Sh.t⁻¹) * (Sh.t * b * Sh.t⁻¹) * (Sh.t * Sh.t) := by group
        _ = a * (b * (Sh.t * a * Sh.t⁻¹)) * (Sh.t * b * Sh.t⁻¹) := by
          rw [Sh.t_sq, mul_one]; group
        _ = a * ((Sh.t * a * Sh.t⁻¹) * b) * (Sh.t * b * Sh.t⁻¹) := by rw [hcomm]
        _ = (a * (Sh.t * a * Sh.t⁻¹)) * (b * (Sh.t * b * Sh.t⁻¹)) := by group
    have hz : (a * (Sh.t * a * Sh.t⁻¹)) * (b * (Sh.t * b * Sh.t⁻¹)) = Sh.z := hcc.symm.trans hc
    have h₁ : a * (Sh.t * a * Sh.t⁻¹) ∈ Sh.I₂ := by
      have : a * (Sh.t * a * Sh.t⁻¹) = Sh.z * (b * (Sh.t * b * Sh.t⁻¹))⁻¹ := by
        rw [← hz]; group
      rw [this]
      exact mul_mem Sh.z_mem₂ (inv_mem (mul_mem hb hb'))
    have h₂ : b * (Sh.t * b * Sh.t⁻¹) ∈ Sh.swap.I₂ := by
      have : b * (Sh.t * b * Sh.t⁻¹) = (a * (Sh.t * a * Sh.t⁻¹))⁻¹ * Sh.z := by
        rw [← hz]; group
      rw [this]
      exact mul_mem (inv_mem (mul_mem ha ha')) Sh.z_mem₁
    have e₁ := mul_conj_eq_one₁ Sh h2₁ ha h₁
    have e₂ := mul_conj_eq_one₁ Sh.swap h2₂ hb h₂
    have : Sh.z = 1 := by
      rw [← hz, e₁, one_mul]
      exact e₂
    exact Sh.z_ne this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Q3L
