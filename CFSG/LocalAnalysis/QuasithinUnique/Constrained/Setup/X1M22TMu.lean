module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def muA
    : ↥m22A →* MulAut S22 where
  toFun a := conjOn NativeSporadic.M22 (a : Equiv.Perm (Fin 22)) (A_norm a.2) (A_norm' a.2)
  map_one' := by
    ext h
    simp [conjOn_apply]
  map_mul' a b := by
    ext h
    simp [conjOn_apply, mul_assoc]

theorem muA_apply
    (a : ↥m22A) (h : S22) :
    ((muA a h : S22) : Equiv.Perm (Fin 22)) = (a : Equiv.Perm (Fin 22)) * h * (a : Equiv.Perm (Fin 22))⁻¹ :=
  rfl

theorem muA_injective
    : Function.Injective muA := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, haA⟩ ha
  have hc : ∀ h ∈ NativeSporadic.M22, a * h = h * a := by
    intro h hh
    have := congrArg (fun φ : MulAut S22 => ((φ ⟨h, hh⟩ : S22) : Equiv.Perm (Fin 22))) ha
    simp only [muA_apply, MulAut.one_apply] at this
    calc a * h = (a * h * a⁻¹) * a := by group
      _ = h * a := by rw [show a * h * a⁻¹ = h from this]
  rcases mem_m22A.1 haA with hmem | hmem
  · have hz : (⟨a, hmem⟩ : S22) ∈ Subgroup.center S22 := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (hc z z.2).symm
    rw [m22_center_eq_bot', Subgroup.mem_bot] at hz
    have h1 : a = 1 := Subtype.ext_iff.1 hz
    exact Subtype.ext h1
  · exfalso
    apply m22_delta_outer _ hmem
    intro h hh
    have : m22Delta * (m22Delta⁻¹ * a) = a := by group
    rw [this]
    exact hc h hh

theorem muA_surjective
    : Function.Surjective muA := by
  intro α
  by_cases hα : α ∈ inner S22
  · obtain ⟨s, rfl⟩ := hα
    refine ⟨⟨(s : Equiv.Perm (Fin 22)), m22_le_A s.2⟩, ?_⟩
    ext h
    rfl
  · obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hα
    have hgA : g * m22Delta ∈ m22A := by
      refine mem_m22A.2 (Or.inr ?_)
      have : m22Delta⁻¹ * (g * m22Delta) = m22Delta⁻¹ * g * m22Delta := by group
      rw [this]
      exact m22_delta_conj' g hg
    refine ⟨⟨g * m22Delta, hgA⟩, ?_⟩
    ext h
    rw [muA_apply, hαg h]

theorem muA_bijective
    : Function.Bijective muA := ⟨muA_injective, muA_surjective⟩

theorem muA_of_mem
    (m : S22) : muA ⟨(m : Equiv.Perm (Fin 22)), m22_le_A m.2⟩ = MulAut.conj m := by
  ext h
  rfl

end CFSG.QuasithinUnique.Setup.X1
