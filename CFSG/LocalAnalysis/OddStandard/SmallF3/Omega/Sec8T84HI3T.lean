module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] def HI3Conc (P : Subgroup (ProjOrth Q)) (x : ProjOrth Q) : Prop :=
  ∃ B : Subgroup (ProjOrth Q), B ≤ P ∧ IsElemAb2 B 4 ∧ ∃ p ∈ P,
    (p * x) * (p * x) = 1 ∧ (∀ b ∈ B, (p * x) * b = b * (p * x)) ∧
      ∃ α : ℤˣ, HasType (p * x) 3 α

theorem hI3Conc_of_conj (hQ : Q.Nondegenerate) {P P' : Subgroup (ProjOrth Q)} (g : ProjOrth Q)
    (h : ∀ y : ProjOrth Q, y ∈ P ↔ g * y * g⁻¹ ∈ P') {x : ProjOrth Q}
    (hx : HI3Conc P' (g * x * g⁻¹)) : HI3Conc P x := by
  obtain ⟨B', hB'P', hE', p', hp'P', hsq, hcomm, α, hty⟩ := hx
  refine ⟨B'.map (MulAut.conj g⁻¹).toMonoidHom, ?_, isElemAb2_conj g⁻¹ hE',
    g⁻¹ * p' * g, ?_, ?_, ?_, α, ?_⟩
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact (h ((MulAut.conj g⁻¹).toMonoidHom y')).mpr (by
      rw [show g * ((MulAut.conj g⁻¹).toMonoidHom y') * g⁻¹ = y' by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group]
      exact hB'P' hy')
  · exact (h (g⁻¹ * p' * g)).mpr (by
      rw [show g * (g⁻¹ * p' * g) * g⁻¹ = p' by group]
      exact hp'P')
  · have hpx : (g⁻¹ * p' * g) * x = g⁻¹ * (p' * (g * x * g⁻¹)) * g := by group
    rw [hpx]
    have hsq' : g⁻¹ * (p' * (g * x * g⁻¹)) * g * (g⁻¹ * (p' * (g * x * g⁻¹)) * g) =
        g⁻¹ * ((p' * (g * x * g⁻¹)) * (p' * (g * x * g⁻¹))) * g := by group
    rw [hsq', hsq]
    group
  · intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hpx : (g⁻¹ * p' * g) * x = g⁻¹ * (p' * (g * x * g⁻¹)) * g := by group
    rw [hpx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hcomm' : g⁻¹ * (p' * (g * x * g⁻¹)) * g * (g⁻¹ * b' * g) =
        g⁻¹ * ((p' * (g * x * g⁻¹)) * b') * g := by group
    have hcomm'' : g⁻¹ * b' * g * (g⁻¹ * (p' * (g * x * g⁻¹)) * g) =
        g⁻¹ * (b' * (p' * (g * x * g⁻¹))) * g := by group
    rw [hcomm', hcomm'', hcomm b' hb']
  · have hα := hasType_conj hQ g⁻¹ hty
    have hpx : (g⁻¹ * p' * g) * x = g⁻¹ * (p' * (g * x * g⁻¹)) * g := by group
    rw [hpx]
    simpa using hα

theorem mem_hPm_conj_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {n : OGroup Q}
    (hn : n ∈ normalizer (ffP0 hQ fr : Set (OGroup Q))) (y : ProjOrth Q) :
    y ∈ hPm hQ fr ↔ toProj Q n * y * (toProj Q n)⁻¹ ∈ hPm hQ fr := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  have hmap : toProj Q n * toProj Q m * (toProj Q n)⁻¹ = toProj Q (n * m * n⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap]
  have hiff : ∀ z : OGroup Q, toProj Q z ∈ hPm hQ fr ↔ z ∈ ffP0 hQ fr := by
    intro z
    rw [← Subgroup.mem_comap, comap_hPm hQ fr]
  rw [hiff m, hiff (n * m * n⁻¹)]
  exact Subgroup.mem_normalizer_iff.mp hn m

end CFSG.OddStandard.SmallF3.Omega
