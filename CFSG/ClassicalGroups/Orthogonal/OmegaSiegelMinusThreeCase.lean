module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelSetting
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeN
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyConj

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

@[expose] def IsFlag (Q : QuadraticForm K' N) (a b c : N) : Prop :=
  Q a = 0 ∧ a ≠ 0 ∧ Q b = 0 ∧ Q c = 0 ∧ polar Q a b = 0 ∧ polar Q a c = 0 ∧ polar Q b c ≠ 0

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rhoE_conj_elementary (g : ↥(elementaryGroup QN)) (a b : N) :
    rhoE ρ ((g : N ≃ₗ[K'] N) a) ((g : N ≃ₗ[K'] N) b) = ρ g * rhoE ρ a b * (ρ g)⁻¹ := by
  have hG : (g : N ≃ₗ[K'] N) ∈ TauCeti.QuadraticMap.orthogonalGroup QN :=
    elementaryGroup_le_orthogonalGroup QN g.2
  unfold rhoE
  rw [← map_inv ρ, ← map_mul ρ, ← map_mul ρ]
  congr 1
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (eichler_conj hG a b).symm

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
theorem movedSpace_rhoE_apply (g : ↥(elementaryGroup QN)) (a b : N) :
    movedSpace (rhoE ρ ((g : N ≃ₗ[K'] N) a) ((g : N ≃ₗ[K'] N) b)) =
      (movedSpace (rhoE ρ a b)).map (ρ g : V →ₗ[K] V) := by
  rw [rhoE_conj_elementary, movedSpace_conj]

omit [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem exists_map_eq_of_isFlag (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {a b c : N} (h : IsFlag QN a b c) :
    ∃ g : ↥(elementaryGroup QN),
      movedSpace (rhoE ρ p e) = (movedSpace (rhoE ρ a b)).map (ρ g : V →ₗ[K] V) ∧
      movedSpace (rhoE ρ p f) = (movedSpace (rhoE ρ a c)).map (ρ g : V →ₗ[K] V) := by
  obtain ⟨ha, ha0, hb, hc, hab, hac, hbc⟩ := h
  obtain ⟨ν, hν⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K' 2) (polar QN b c)⁻¹
  have hνβ : ν * ν * polar QN b c = 1 := by
    rw [← hν, inv_mul_cancel₀ hbc]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hνβ
  have ha' : QN (ν⁻¹ • a) = 0 := by rw [map_smul_eq_sq, ha, mul_zero]
  have ha0' : ν⁻¹ • a ≠ 0 := smul_ne_zero (inv_ne_zero hν0) ha0
  have hb' : QN (ν • b) = 0 := by rw [map_smul_eq_sq, hb, mul_zero]
  have hc' : QN (ν • c) = 0 := by rw [map_smul_eq_sq, hc, mul_zero]
  have hab' : polar QN (ν⁻¹ • a) (ν • b) = 0 := by
    simp only [polar_smul_left_eq, polar_smul_right_eq, hab, mul_zero]
  have hac' : polar QN (ν⁻¹ • a) (ν • c) = 0 := by
    simp only [polar_smul_left_eq, polar_smul_right_eq, hac, mul_zero]
  have hbc' : polar QN (ν • b) (ν • c) = 1 := by
    rw [polar_smul_left_eq, polar_smul_right_eq]
    linear_combination hνβ
  obtain ⟨g, hg, hga, hgb, hgc⟩ :=
    MinusThreeFrame.exists_mem_elementaryGroup_flag hF hs.ndN ha' ha0' hb' hc' hab' hac' hbc'
  have e1 : rhoE ρ (ν⁻¹ • a) (ν • b) = rhoE ρ a b := by
    rw [rhoE_smul_left, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have e2 : rhoE ρ (ν⁻¹ • a) (ν • c) = rhoE ρ a c := by
    rw [rhoE_smul_left, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · have h1 : movedSpace (rhoE ρ (g (ν⁻¹ • a)) (g (ν • b))) =
        (movedSpace (rhoE ρ (ν⁻¹ • a) (ν • b))).map (ρ ⟨g, hg⟩ : V →ₗ[K] V) :=
      movedSpace_rhoE_apply (ρ := ρ) ⟨g, hg⟩ (ν⁻¹ • a) (ν • b)
    rw [hga, hgb, e1] at h1
    exact h1
  · have h2 : movedSpace (rhoE ρ (g (ν⁻¹ • a)) (g (ν • c))) =
        (movedSpace (rhoE ρ (ν⁻¹ • a) (ν • c))).map (ρ ⟨g, hg⟩ : V →ₗ[K] V) :=
      movedSpace_rhoE_apply (ρ := ρ) ⟨g, hg⟩ (ν⁻¹ • a) (ν • c)
    rw [hga, hgc, e2] at h2
    exact h2

omit [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem inf_eq_bot_iff_of_isFlag (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {a b c : N} (h : IsFlag QN a b c) :
    movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥ ↔
      movedSpace (rhoE ρ p e) ⊓ movedSpace (rhoE ρ p f) = ⊥ := by
  obtain ⟨g, h1, h2⟩ := exists_map_eq_of_isFlag hs hF h
  rw [h1, h2, ← Submodule.map_inf (ρ g : V →ₗ[K] V) (ρ g).injective,
    Submodule.map_eq_bot_iff]

omit [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.flag_dichotomy (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) :
    (∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥) ∨
      ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥ := by
  by_cases hT : movedSpace (rhoE ρ p e) ⊓ movedSpace (rhoE ρ p f) = ⊥
  · exact Or.inr fun a b c h => (inf_eq_bot_iff_of_isFlag hs hF h).mpr hT
  · exact Or.inl fun a b c h h0 => hT ((inf_eq_bot_iff_of_isFlag hs hF h).mp h0)

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
