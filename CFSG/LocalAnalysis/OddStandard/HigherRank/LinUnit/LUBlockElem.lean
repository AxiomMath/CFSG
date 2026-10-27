module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer

public section

namespace CFSG.OddStandard.HigherRank.LinUnit

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {E : Type} {V : Type*} [Field E] [AddCommGroup V] [Module E V]

@[expose] def ActsAsBlock (g : Module.End E V) (ζ : E) (A W : Submodule E V) : Prop :=
  IsCompl A W ∧ A ≠ ⊥ ∧ W ≠ ⊥ ∧ (∀ a ∈ A, g a = ζ • a) ∧ ∀ w ∈ W, g w = w

theorem ActsAsBlock.pow {g : Module.End E V} {ζ : E} {A W : Submodule E V}
    (h : ActsAsBlock g ζ A W) (j : ℕ) : ActsAsBlock (g ^ j) (ζ ^ j) A W := by
  obtain ⟨hc, hA, hW, hgA, hgW⟩ := h
  refine ⟨hc, hA, hW, ?_, ?_⟩
  · intro a ha
    induction j with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hgA a ha, map_smul, ih, smul_smul, pow_succ']
  · intro w hw
    induction j with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hgW w hw, ih]

theorem ActsAsBlock.eq_one_iff {g : Module.End E V} {ζ : E} {A W : Submodule E V}
    (h : ActsAsBlock g ζ A W) : g = 1 ↔ ζ = 1 := by
  constructor
  · intro hg
    obtain ⟨hc, hA, hW, hgA, hgW⟩ := h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
    have h1 : ζ • a = a := by
      have h2 := hgA a ha
      rw [hg] at h2
      simpa using h2.symm
    have h2 : (ζ - 1) • a = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right ha0)
  · intro hζ
    obtain ⟨hc, hA, hW, hgA, hgW⟩ := h
    ext v
    obtain ⟨a, w, ha, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
    rw [Module.End.one_apply, map_add, hgA a ha, hgW w hw, hζ, one_smul]

theorem ActsAsBlock.eq_one_of_eq_smul_one {g : Module.End E V} {ζ : E} {A W : Submodule E V}
    (h : ActsAsBlock g ζ A W) {c : E} (hg : g = c • 1) : ζ = 1 := by
  have hiff := ActsAsBlock.eq_one_iff h
  obtain ⟨hc, hA, hW, hgA, hgW⟩ := h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have h1 : c • w = w := by
    have h2 := hgW w hw
    rw [hg] at h2
    simpa using h2
  have h2 : c - 1 = 0 := by
    have h3 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact (smul_eq_zero.mp h3).resolve_right hw0
  have hc1 : c = 1 := sub_eq_zero.mp h2
  exact hiff.mp (by rw [hg, hc1, one_smul])

theorem ActsAsBlock.of_comp_subtype {g : Module.End E V} {ζ : E} {P Q : Submodule E V}
    (hc : IsCompl P Q) (hP : P ≠ ⊥) (hQ : Q ≠ ⊥) {ψP : Module.End E P} {ψQ : Module.End E Q}
    (hψP : P.subtype ∘ₗ ψP = g ∘ₗ P.subtype) (hψQ : Q.subtype ∘ₗ ψQ = g ∘ₗ Q.subtype)
    (hP' : ψP = ζ • 1) (hQ' : ψQ = 1) : ActsAsBlock g ζ P Q := by
  refine ⟨hc, hP, hQ, ?_, ?_⟩
  · intro a ha
    have h : g a = ζ • a := by
      have h1 := LinearMap.congr_fun hψP ⟨a, ha⟩
      rw [hP'] at h1
      simpa using h1.symm
    exact h
  · intro w hw
    have h : g w = w := by
      have h1 := LinearMap.congr_fun hψQ ⟨w, hw⟩
      rw [hQ'] at h1
      simpa using h1.symm
    exact h

theorem ActsAsBlock.pow_eq_one_iff {g : LinearMap.GeneralLinearGroup E V} {ζ : E}
    {A W : Submodule E V} (h : ActsAsBlock (g : Module.End E V) ζ A W) (j : ℕ) :
    g ^ j = 1 ↔ ζ ^ j = 1 := by
  rw [← (h.pow j).eq_one_iff]
  constructor
  · intro hg
    have h1 := congrArg (fun u : LinearMap.GeneralLinearGroup E V => (u : Module.End E V)) hg
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h1
  · intro hg
    exact Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hg)

theorem ActsAsBlock.pow_eq_one_of_mem_normOneScalars {p f : ℕ} {h : UnitaryFieldData p f E}
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {g : sesqUnitaryGroup B} {ζ : E} {A W : Submodule E V}
    (hb : ActsAsBlock (unitaryOp g) ζ A W) (j : ℕ) (hj : g ^ j ∈ sesqNormOneScalars h B) :
    ζ ^ j = 1 := by
  obtain ⟨c, hc, hcj⟩ := mem_sesqNormOneScalars.mp hj
  have hpow : unitaryOp (g ^ j) = (unitaryOp g) ^ j := by
    change (((g ^ j : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) = (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) ^ j
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact (hb.pow j).eq_one_of_eq_smul_one (c := c) (by rw [← hpow]; exact hcj)

end CFSG.OddStandard.HigherRank.LinUnit
