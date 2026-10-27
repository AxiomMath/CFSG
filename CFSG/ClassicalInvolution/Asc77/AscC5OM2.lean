module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM1

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (twin_std_sp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

structure Frame (F : Type) [Field F] (Y : Type) [Group Y] (Φ : Set (Subgroup Y))
    (A A' : Subgroup Y) (z' : Y) where
  ψ : StatedSp 2 F →* Y
  surj : Function.Surjective ψ
  ker : ψ.ker = spScalars 2 F
  hA : A = (longRootSp2 F 2 0).map ψ
  hA' : A' = (longRootSp2 F 2 1).map ψ
  hz : z' = ψ (longInv F 2 0)
  mem : ∀ J ∈ Φ, ∃ P, IsHyperbolicPlane P ∧ J = (planeGroup P).map ψ
  mem' : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ Φ

section Helpers

variable {G : Type} [Group G]

theorem map_conj_mul (g h : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

end Helpers

variable {F : Type} [Field F]

theorem ker_comp_conj {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y) (hk : ψ.ker = spScalars 2 F)
    (g : StatedSp 2 F) : (ψ.comp (MulAut.conj g).toMonoidHom).ker = spScalars 2 F := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hk, mem_spScalars_iff,
    mem_spScalars_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro (h | h)
    · left
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = negOne F := by rw [h, mul_assoc, negOne_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  · rintro (rfl | rfl)
    · left; group
    · right; rw [← negOne_comm]; group

theorem map_planeGroup_comp_conj {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y) (g : StatedSp 2 F)
    (u w : Fin 2 ⊕ Fin 2 → F) :
    (planeGroup (Submodule.span F {u, w})).map (ψ.comp (MulAut.conj g).toMonoidHom) =
      (planeGroup (Submodule.span F {mat 2 F g *ᵥ u, mat 2 F g *ᵥ w})).map ψ := by
  rw [planeGroup_span_conj, Subgroup.map_map]

theorem map_inv_eq (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {L : Subgroup (StatedSp 2 F)}
    {j : StatedSp 2 F} (hL : IsLongRootSp2 L j) {z : Y} (hzL : IsUniqueInvolution (L.map ψ) z) :
    ψ j = z := by
  have hjL : j ∈ L := (hL.isClassicalSL2 h2).mem
  have hj2 : j * j = 1 := hL.mul_self h2
  rcases hzL.unique (ψ j) (Subgroup.mem_map_of_mem ψ hjL) (by rw [← map_mul, hj2, map_one]) with
    h | h
  · exfalso
    have hjc := hker (show j ∈ ψ.ker from h)
    rw [CFSG.LieType.Universal.Symplectic.center_eq] at hjc
    obtain ⟨c, hc⟩ := C25W.Sp.scalar_of_mem_spScalars hjc
    obtain ⟨k, g, -, hjg⟩ := hL
    rw [hjg] at hc
    exact C25W.Sp.longInv_conj_not_scalar h2 k g ⟨c, hc⟩
  · exact h

theorem exists_frame_model [Finite F] (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hi : IsLongRootSp2 R i) (hi' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hzA : IsUniqueInvolution (R.map ψ) z') (hzA' : IsUniqueInvolution (R'.map ψ) z')
    {Φ : Set (Subgroup Y)}
    (hΦ1 : ∀ J ∈ Φ, ∃ P, IsHyperbolicPlane P ∧ J = (planeGroup P).map ψ)
    (hΦ2 : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ Φ) :
    Nonempty (Frame F Y Φ (R.map ψ) (R'.map ψ) z') := by
  have hkψ := C25W.Sp.ker_eq_spScalars h2 ψ hker hi hi' hne hzA hzA'
  have hψi := map_inv_eq h2 ψ hker hi hzA
  have hψi' := map_inv_eq h2 ψ hker hi' hzA'
  have hiR : i ∈ R := (hi.isClassicalSL2 h2).mem
  have hi'R' : i' ∈ R' := (hi'.isClassicalSL2 h2).mem
  have hi1 : i ≠ 1 := by
    intro h
    have := (hi.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hi'1 : i' ≠ 1 := by
    intro h
    have := (hi'.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hc : i' * i⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    change i' * i⁻¹ ∈ spScalars 2 F
    rw [← hkψ, MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel]
  have hRne : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨g, k₀, hRg, hR'g⟩ := twin_std_sp h2 ⟨i, hi⟩ ⟨i', hi'⟩ hRne hiR (hi.mul_self h2) hi1
    hi'R' (hi'.mul_self h2) hi'1 hc
  obtain ⟨g', hR0, hR1⟩ : ∃ g' : StatedSp 2 F,
      R = (longRootSp2 F 2 0).map (MulAut.conj g').toMonoidHom ∧
        R' = (longRootSp2 F 2 1).map (MulAut.conj g').toMonoidHom := by
    fin_cases k₀
    · exact ⟨g, hRg, hR'g⟩
    · refine ⟨g * sw F, ?_, ?_⟩
      · rw [map_conj_mul, map_sw_L h2]
        exact hRg
      · rw [map_conj_mul, map_sw_L h2]
        exact hR'g
  refine ⟨⟨ψ.comp (MulAut.conj g').toMonoidHom, ?_, ker_comp_conj ψ hkψ g', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨g'⁻¹ * x * g', by simp [mul_assoc]⟩
  · rw [hR0, Subgroup.map_map]
  · rw [hR1, Subgroup.map_map]
  · have hL : IsLongRootSp2 R (g' * longInv F 2 0 * g'⁻¹) := ⟨0, g', hR0, rfl⟩
    exact (map_inv_eq h2 ψ hker hL hzA).symm
  · intro J hJ
    obtain ⟨P₂, ⟨u, w, huw, rfl⟩, rfl⟩ := hΦ1 J hJ
    refine ⟨Submodule.span F {mat 2 F g'⁻¹ *ᵥ u, mat 2 F g'⁻¹ *ᵥ w},
      ⟨_, _, by rw [form_mulVec]; exact huw, rfl⟩, ?_⟩
    rw [map_planeGroup_comp_conj, mulVec_mulVec_inv, mulVec_mulVec_inv]
  · rintro P₃ ⟨u, w, huw, rfl⟩
    rw [map_planeGroup_comp_conj]
    exact hΦ2 _ ⟨_, _, by rw [form_mulVec]; exact huw, rfl⟩

end CFSG.ClassicalInvolution.Asc77.C5O.M
