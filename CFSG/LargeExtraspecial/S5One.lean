module

public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LargeExtraspecial.S5Odd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def conjCl (S : Setting G) (g : G) : Set S.Qt :=
  {v | ∃ h : S.M, v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)}

theorem span_conjCl_eq_top (hIrr : Irr S) (H : Hyp4 S g) :
    Submodule.span (ZMod 2) (conjCl S g) = ⊤ := by
  have hinv : ∀ x ∈ S.Mbar, ∀ u ∈ Submodule.span (ZMod 2) (conjCl S g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Submodule.span (ZMod 2) (conjCl S g) := by
    intro x hx u hu
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      refine Submodule.subset_span ⟨k * h, ?_⟩
      rw [ρ_cl_conj_z S k (conj_mem_QG' S h.2 H.conj_mem)]
      simp [mul_assoc]
    | zero => simp
    | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
    | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu
  rcases hIrr (Submodule.span (ZMod 2) (conjCl S g)) hinv with h | h
  · exfalso
    have hmem : S.cl (g * S.z * g⁻¹) ∈ Submodule.span (ZMod 2) (conjCl S g) :=
      Submodule.subset_span ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at hmem
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne hmem
  · exact h

theorem eq_top_of_invariant (hIrr : Irr S) (H : Hyp4 S g) {U : Submodule (ZMod 2) S.Qt}
    (hU : U ≠ ⊥)
    (hinv : ∀ h : S.M, ∀ x ∈ S.Lbar ((h : G) * g), ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    U = ⊤ := by
  rw [eq_top_iff, ← span_conjCl_eq_top hIrr H, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  exact cl_mem_of_invariant H h hU (hinv h)

theorem fixSub_eq_bot (hIrr : Irr S) (H : Hyp4 S g) {X : Subgroup S.O} (hX : X ≠ ⊥)
    (hnorm : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O)) :
    fixSub S X = ⊥ := by
  by_contra hne
  have htop := eq_top_of_invariant hIrr H hne fun h s hs v hv x hx => by
    have hx' : s⁻¹ * x * s ∈ X := by
      have := (mem_normalizer_iff.mp (inv_mem (hnorm h hs)) x).mp hx
      simpa using this
    have h1 := hv _ hx'
    simp only [coe_mul_apply] at h1
    have h2 := congrArg (s : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2
  apply hX
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ fixSub S X := htop ▸ Submodule.mem_top
  exact hv x hx

theorem exists_not_commute (hIrr : Irr S) (H : Hyp4 S g) {X : Subgroup S.O} (hX : X ≠ ⊥)
    (hnorm : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O)) :
    ∃ s ∈ S.Lbar g, ∃ x ∈ X, s * x ≠ x * s := by
  by_contra hcon
  push Not at hcon
  have hfix : S.cl (g * S.z * g⁻¹) ∈ fixSub S X := fun x hx =>
    fix_of_mem_normalizer H (mem_normalizer_of_commute fun s hs => hcon s hs x hx)
  rw [fixSub_eq_bot hIrr H hX hnorm, Submodule.mem_bot] at hfix
  exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne hfix

end CFSG.LargeExtraspecial.S5
