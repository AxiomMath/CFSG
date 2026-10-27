module

public import CFSG.ClassicalInvolution.Q3.TL4VtxFamB
public import CFSG.ClassicalInvolution.Q3.TL4VtxAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace Vtx

theorem map_conjSub_hom {G H : Type*} [Group G] [Group H] (φ : G →* H) (x : G)
    (K : Subgroup G) : (conjSub x K).map φ = conjSub (φ x) (K.map φ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

variable {Q : Type} [Group Q] [Finite Q]

noncomputable def innHom (L : Subgroup Q) : ↥L →* ↥(inducedAutOn L) :=
  (MulAut.conj : ↥L →* MulAut ↥L).codRestrict (inducedAutOn L) fun l =>
    innSubgroup_le_inducedAutOn L ⟨l, rfl⟩

omit [Finite Q] in
theorem innHom_eq_one_iff (L : Subgroup Q) (l : ↥L) :
    innHom L l = 1 ↔ l ∈ Subgroup.center ↥L := by
  constructor
  · intro h1
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun α : ↥(inducedAutOn L) => (α : MulAut ↥L) g) h1
    simp only [innHom, MonoidHom.codRestrict_apply, MulAut.conj_apply, OneMemClass.coe_one,
      MulAut.one_apply] at this
    calc g * l = (l * g * l⁻¹) * l := by rw [this]
      _ = l * g := by group
  · intro hl
    apply Subtype.ext
    ext g
    simp only [innHom, MonoidHom.codRestrict_apply, MulAut.conj_apply, OneMemClass.coe_one,
      MulAut.one_apply]
    rw [← Subgroup.mem_center_iff.mp hl g]
    group

omit [Finite Q] in
theorem ker_innHom (L : Subgroup Q) : (innHom L).ker = Subgroup.center ↥L := by
  ext l
  exact innHom_eq_one_iff L l

omit [Finite Q] in
theorem innHom_range_normal (L : Subgroup Q) : (innHom L).range.Normal := by
  constructor
  rintro _ ⟨l, rfl⟩ α
  exact ⟨(α : MulAut ↥L) l, Subtype.ext (mulAut_mul_conj_mul_inv (α : MulAut ↥L) l).symm⟩

omit [Finite Q] in
noncomputable def innHomRangeEquiv (L : Subgroup Q) :
    ↥(innHom L).range ≃* ↥L ⧸ Subgroup.center ↥L :=
  (QuotientGroup.quotientKerEquivRange (innHom L)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_innHom L))

omit [Finite Q] in
theorem isSimpleGroup_innHom_range {L : Subgroup Q} (hL : IsComponent L) :
    IsSimpleGroup ↥(innHom L).range := by
  have := hL.1.2.1
  exact (innHomRangeEquiv L).isSimpleGroup

omit [Finite Q] in
theorem nonabelian_innHom_range {L : Subgroup Q} (hL : IsComponent L) :
    ∃ a b : ↥(innHom L).range, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  refine ⟨(innHomRangeEquiv L).symm a, (innHomRangeEquiv L).symm b, fun h => hab ?_⟩
  apply (innHomRangeEquiv L).symm.injective
  rw [map_mul, map_mul, h]

omit [Finite Q] in
theorem centralizer_innHom_range {L : Subgroup Q} (hL : IsComponent L) :
    Subgroup.centralizer ((innHom L).range : Set ↥(inducedAutOn L)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  have hcen : ∀ l : ↥L, l⁻¹ * (α : MulAut ↥L) l ∈ Subgroup.center ↥L := by
    intro l
    have hc := Subgroup.mem_centralizer_iff.mp hα (innHom L l) ⟨l, rfl⟩
    have e1 : α * innHom L l * α⁻¹ = innHom L ((α : MulAut ↥L) l) :=
      Subtype.ext (mulAut_mul_conj_mul_inv _ _)
    have e2 : innHom L ((α : MulAut ↥L) l) = innHom L l := by
      calc innHom L ((α : MulAut ↥L) l) = α * innHom L l * α⁻¹ := e1.symm
        _ = innHom L l * α * α⁻¹ := by rw [← hc]
        _ = innHom L l := by group
    have h3 : innHom L ((α : MulAut ↥L) l * l⁻¹) = 1 := by
      rw [map_mul, map_inv, e2, mul_inv_cancel]
    have hc' := (innHom_eq_one_iff L _).mp h3
    have hcl : (α : MulAut ↥L) l * l⁻¹ * l = l * ((α : MulAut ↥L) l * l⁻¹) :=
      (Subgroup.mem_center_iff.mp hc' l).symm
    have e3 : l⁻¹ * (α : MulAut ↥L) l = (α : MulAut ↥L) l * l⁻¹ := by
      calc l⁻¹ * (α : MulAut ↥L) l = l⁻¹ * ((α : MulAut ↥L) l * l⁻¹ * l) := by group
        _ = l⁻¹ * (l * ((α : MulAut ↥L) l * l⁻¹)) := by rw [hcl]
        _ = (α : MulAut ↥L) l * l⁻¹ := by group
    rw [e3]
    exact hc'
  exact Subtype.ext (mulAut_eq_one_of_central hL.1.1 _ hcen)

theorem fstar_inducedAutOn_eq {L : Subgroup Q} (hL : IsComponent L) :
    genFittingFStar ↥(inducedAutOn L) = (innHom L).range := by
  have := innHom_range_normal L
  have := isSimpleGroup_innHom_range hL
  exact genFittingFStar_eq_of_normal_simple _ (nonabelian_innHom_range hL)
    (centralizer_innHom_range hL)

theorem isSimpleGroup_fstar_inducedAutOn {L : Subgroup Q} (hL : IsComponent L) :
    IsSimpleGroup ↥(genFittingFStar ↥(inducedAutOn L)) := by
  rw [fstar_inducedAutOn_eq hL]
  exact isSimpleGroup_innHom_range hL

theorem nonabelian_fstar_inducedAutOn {L : Subgroup Q} (hL : IsComponent L) :
    ∃ a b : ↥(genFittingFStar ↥(inducedAutOn L)), a * b ≠ b * a := by
  rw [fstar_inducedAutOn_eq hL]
  exact nonabelian_innHom_range hL

omit [Finite Q] in
theorem imgFam_transitive {Φ : Set (Subgroup Q)} {K L : Subgroup Q}
    (hXN : orbGrp Φ K ≤ Subgroup.normalizer (L : Set Q)) :
    ∀ M ∈ imgFam Φ K L hXN, ∀ M' ∈ imgFam Φ K L hXN,
      ∃ g : ↥(inducedAutOn L), conjSub g M = M' := by
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
  refine ⟨psiL L (orbGrp Φ K) hXN (b * a⁻¹), ?_⟩
  simp only
  rw [← map_conjSub_hom, ← conjSub_mul, inv_mul_cancel_right]

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
