module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

variable {M : Type*} [Group M]

def fstarCentralPow (n : ℕ) : Subgroup M where
  carrier := {z | z ∈ CFSG.generalizedFitting M ∧
    (∀ f ∈ CFSG.generalizedFitting M, f * z = z * f) ∧ z ^ n = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun f _ => by simp, one_pow n⟩
  mul_mem' := by
    rintro a b ⟨ha, hac, han⟩ ⟨hb, hbc, hbn⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun f hf => ?_, ?_⟩
    · rw [← mul_assoc, hac f hf, mul_assoc, hbc f hf, mul_assoc]
    · have hab : Commute a b := (hac b hb).symm
      rw [hab.mul_pow, han, hbn, one_mul]
  inv_mem' := by
    rintro a ⟨ha, hac, han⟩
    refine ⟨Subgroup.inv_mem _ ha, fun f hf => ?_, by rw [inv_pow, han, inv_one]⟩
    have := hac f hf
    have h2 : f * a⁻¹ = a⁻¹ * f := by
      calc f * a⁻¹ = a⁻¹ * (a * f) * a⁻¹ := by group
        _ = a⁻¹ * (f * a) * a⁻¹ := by rw [← this]
        _ = a⁻¹ * f := by group
    exact h2

theorem normal_fstarCentralPow [Finite M] (n : ℕ) : (fstarCentralPow (M := M) n).Normal := by
  have hF : (CFSG.generalizedFitting M).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := M)).2
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨hzF, hzc, hzn⟩ := hz
  refine ⟨hF.conj_mem z hzF g, fun f hf => ?_, ?_⟩
  · have hf' : g⁻¹ * f * g ∈ CFSG.generalizedFitting M := by
      simpa using hF.conj_mem f hf g⁻¹
    have := hzc _ hf'
    calc f * (g * z * g⁻¹) = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by rw [this]
      _ = (g * z * g⁻¹) * f := by group
  · rw [conj_pow, hzn]
    simp

theorem mulAut_eq_one_of_fixes_generalizedFitting [Finite M]
    (hM : ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥)
    (α : MulAut M) {e : ℕ} (hα : α ^ (2 ^ e) = 1)
    (hfix : ∀ t ∈ CFSG.generalizedFitting M, α t = t) : α = 1 := by
  have hF : (CFSG.generalizedFitting M).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := M)).2
  ext m
  set δ : M := m⁻¹ * α m with hδ
  have hcent : ∀ f ∈ CFSG.generalizedFitting M, f * δ = δ * f := by
    intro f hf
    have h1 : α (m * f * m⁻¹) = m * f * m⁻¹ := hfix _ (hF.conj_mem f hf m)
    rw [map_mul, map_mul, hfix f hf, map_inv] at h1
    calc f * δ = f * (m⁻¹ * α m) := rfl
      _ = m⁻¹ * (m * f * m⁻¹) * α m := by group
      _ = m⁻¹ * (α m * f * (α m)⁻¹) * α m := by rw [h1]
      _ = δ * f := by simp only [hδ]; group
  have hδF : δ ∈ CFSG.generalizedFitting M :=
    CFSG.centralizer_generalizedFitting_le M
      (Subgroup.mem_centralizer_iff.mpr fun f hf => hcent f hf)
  have hαδ : α δ = δ := hfix δ hδF
  have hpow : ∀ k : ℕ, (α ^ k) m = m * δ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαδ, pow_succ']
      have : α m = m * δ := by simp [hδ]
      rw [this]; group
  have hδn : δ ^ (2 ^ e) = 1 := by
    have h := hpow (2 ^ e)
    rw [hα] at h
    simp only [MulAut.one_apply] at h
    have : m * δ ^ (2 ^ e) = m * 1 := by rw [← h]; simp
    exact mul_left_cancel this
  have hmem : δ ∈ fstarCentralPow (M := M) (2 ^ e) :=
    ⟨hδF, hcent, hδn⟩
  have hbot : fstarCentralPow (M := M) (2 ^ e) = ⊥ := by
    have := normal_fstarCentralPow (M := M) (2 ^ e)
    refine hM _ this fun g => ⟨e, ?_⟩
    obtain ⟨_, _, hg⟩ := g.2
    exact Subtype.ext (by simpa using hg)
  rw [hbot, Subgroup.mem_bot] at hmem
  have : m⁻¹ * α m = 1 := hmem
  have := mul_eq_one_iff_eq_inv.mp this
  simpa using this.symm

end CFSG.HardMathSupport.Cooperstein.StructureLie
