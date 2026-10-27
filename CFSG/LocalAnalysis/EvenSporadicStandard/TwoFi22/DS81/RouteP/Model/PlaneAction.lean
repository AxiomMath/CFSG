module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Orders
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem smul_mem_plane_of_perm {g : Q3} (π : Perm (Fin 24))
    (h : ∀ i, g • planePt i = planePt (π i)) :
    ∀ p ∈ plane, g • p ∈ plane ∧ g⁻¹ • p ∈ plane := by
  intro p hp
  obtain ⟨j, rfl⟩ := mem_plane_iff.1 hp
  refine ⟨?_, ?_⟩
  · rw [h j]
    exact planePt_mem _
  · have hj : g⁻¹ • planePt j = planePt (π.symm j) := by
      rw [inv_smul_eq_iff, h, π.apply_symm_apply]
    rw [hj]
    exact planePt_mem _

theorem Zq_smul_mem_plane_both
    {g : Q3} (hg : g ∈ Zq) : ∀ p ∈ plane, g • p ∈ plane ∧ g⁻¹ • p ∈ plane := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ p ∈ plane, g • p ∈ plane ∧ g⁻¹ • p ∈ plane) ?_ ?_ ?_ ?_ hg
  · rintro x ((rfl | rfl) | ⟨j, rfl⟩)
    · exact smul_mem_plane_of_perm PA aElt_smul_planePt
    · exact smul_mem_plane_of_perm PB bElt_smul_planePt
    · exact smul_mem_plane_of_perm 1 (fun i => by rw [epsElt_smul_planePt, Perm.one_apply])
  · intro p hp
    rw [one_smul, inv_one, one_smul]
    exact ⟨hp, hp⟩
  · intro x y _ _ hx hy p hp
    obtain ⟨hy1, -⟩ := hy p hp
    obtain ⟨-, hx2⟩ := hx p hp
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact (hx _ hy1).1
    · rw [mul_inv_rev, mul_smul]
      exact (hy _ hx2).2
  · intro x _ hx p hp
    rw [inv_inv]
    exact (hx p hp).symm

theorem Zq_preserves_plane
    {g : Q3} (hg : g ∈ Zq) {p : Ω} (hp : p ∈ plane) : g • p ∈ plane :=
  (Zq_smul_mem_plane_both hg p hp).1

theorem E0_smul_planePt
    {g : Q3} (hg : g ∈ E0) (i : Fin 24) : g • planePt i = planePt i := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ i, g • planePt i = planePt i) ?_ ?_ ?_ ?_ hg i
  · rintro _ ⟨j, rfl⟩ i
    exact epsElt_smul_planePt j i
  · intro i
    exact one_smul _ _
  · intro x y _ _ hx hy i
    rw [mul_smul, hy, hx]
  · intro x _ hx i
    rw [inv_smul_eq_iff, hx]

noncomputable def planeIdx
    (g : Zq) (i : Fin 24) : Fin 24 :=
  Classical.choose (mem_plane_iff.1 (Zq_preserves_plane g.2 (planePt_mem i)))

theorem planePt_planeIdx
    (g : Zq) (i : Fin 24) : planePt (planeIdx g i) = (g : Q3) • planePt i :=
  Classical.choose_spec (mem_plane_iff.1 (Zq_preserves_plane g.2 (planePt_mem i)))

theorem planeIdx_one
    (i : Fin 24) : planeIdx 1 i = i := by
  apply planePt_injective
  rw [planePt_planeIdx, Subgroup.coe_one, one_smul]

theorem planeIdx_mul
    (g h : Zq) (i : Fin 24) : planeIdx (g * h) i = planeIdx g (planeIdx h i) := by
  apply planePt_injective
  rw [planePt_planeIdx, planePt_planeIdx, planePt_planeIdx, Subgroup.coe_mul, mul_smul]

noncomputable def planeHom :
    Zq →* Perm (Fin 24) where
  toFun g :=
    { toFun := planeIdx g
      invFun := planeIdx g⁻¹
      left_inv := fun i => by
        show planeIdx g⁻¹ (planeIdx g i) = i
        rw [← planeIdx_mul, inv_mul_cancel, planeIdx_one]
      right_inv := fun i => by
        show planeIdx g (planeIdx g⁻¹ i) = i
        rw [← planeIdx_mul, mul_inv_cancel, planeIdx_one] }
  map_one' := Perm.ext planeIdx_one
  map_mul' g h := Perm.ext (planeIdx_mul g h)

theorem planePt_planeHom
    (g : Zq) (i : Fin 24) : planePt (planeHom g i) = (g : Q3) • planePt i :=
  planePt_planeIdx g i

theorem planeHom_aElt :
    planeHom ⟨aElt, aElt_mem_Zq⟩ = PA := by
  refine Perm.ext fun i => ?_
  apply planePt_injective
  rw [planePt_planeHom]
  exact aElt_smul_planePt i

theorem planeHom_bElt :
    planeHom ⟨bElt, bElt_mem_Zq⟩ = PB := by
  refine Perm.ext fun i => ?_
  apply planePt_injective
  rw [planePt_planeHom]
  exact bElt_smul_planePt i

theorem planeHom_eq_one_of_mem_E0
    {g : Zq} (hg : (g : Q3) ∈ E0) : planeHom g = 1 := by
  refine Perm.ext fun i => ?_
  apply planePt_injective
  rw [planePt_planeHom, E0_smul_planePt hg, Perm.one_apply]

noncomputable def sigmaM24 : Perm (Fin 24) :=
  Equiv.ofBijective
    (![23, 14, 7, 22, 3, 13, 1, 9, 10, 15, 21, 6, 5, 2, 20, 11, 16, 17, 0, 19, 4, 18, 8, 12] :
      Fin 24 → Fin 24) (by decide)

theorem sigmaM24_PA : ∀ i : Fin 24, sigmaM24 (PA i) = m24gA (sigmaM24 i) := by decide

theorem sigmaM24_PB : ∀ i : Fin 24, m24gB (sigmaM24 (PB i)) = sigmaM24 i := by decide

theorem conj_m24gA : sigmaM24⁻¹ * m24gA * sigmaM24 = PA := by
  refine Perm.ext fun i => ?_
  rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_eq]
  exact (sigmaM24_PA i).symm

theorem conj_m24gB : sigmaM24⁻¹ * m24gB * sigmaM24 = PB⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  refine Perm.ext fun i => ?_
  rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_eq,
    sigmaM24_PB]
  rfl

theorem card_M24_le_card_closure_PA_PB :
    Nat.card (NativeSporadic.Carrier .M24) ≤ Nat.card (Subgroup.closure {PA, PB}) := by
  let c : Perm (Fin 24) →* Perm (Fin 24) := (MulAut.conj sigmaM24⁻¹).toMonoidHom
  have hc : ∀ x, c x = sigmaM24⁻¹ * x * sigmaM24 := fun x => by
    simp [c, MulAut.conj_apply]
  have hle : NativeSporadic.M24.map c ≤ Subgroup.closure {PA, PB} := by
    rw [m24_eq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · rw [hx, hc, conj_m24gA]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, hc, conj_m24gB]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  calc Nat.card (NativeSporadic.Carrier .M24) = Nat.card (NativeSporadic.M24.map c) :=
        (Subgroup.card_map_of_injective (MulAut.conj sigmaM24⁻¹).injective).symm
    _ ≤ Nat.card (Subgroup.closure {PA, PB}) := Subgroup.card_le_of_le hle

theorem card_Zq_ge :
    2 ^ 11 * Nat.card (NativeSporadic.Carrier .M24) ≤ Nat.card Zq := by
  haveI : Finite Q3 := Finite.of_injective rho rho_injective
  have hker : Nat.card E0 ≤ Nat.card planeHom.ker := by
    have hle : E0 ≤ (planeHom.ker).map Zq.subtype := by
      intro g hg
      refine ⟨⟨g, E0_le_Zq hg⟩, ?_, rfl⟩
      exact planeHom_eq_one_of_mem_E0 hg
    calc Nat.card E0 ≤ Nat.card (planeHom.ker.map Zq.subtype) := Subgroup.card_le_of_le hle
      _ = Nat.card planeHom.ker := Subgroup.card_map_of_injective Zq.subtype_injective
  have hrange : Nat.card (Subgroup.closure {PA, PB}) ≤ Nat.card planeHom.range := by
    apply Subgroup.card_le_of_le
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, planeHom_aElt⟩
    · exact ⟨_, planeHom_bElt⟩
  calc 2 ^ 11 * Nat.card (NativeSporadic.Carrier .M24)
      = Nat.card E0 * Nat.card (NativeSporadic.Carrier .M24) := by rw [card_E0]
    _ ≤ Nat.card planeHom.ker * Nat.card planeHom.range :=
        Nat.mul_le_mul hker (card_M24_le_card_closure_PA_PB.trans hrange)
    _ = Nat.card Zq := Subgroup.card_ker_mul_card_range planeHom

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
