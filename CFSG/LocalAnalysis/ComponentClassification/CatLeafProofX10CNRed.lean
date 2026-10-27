module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNDef
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81NoNilp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf
public import CFSG.LocalAnalysis.ComponentClassification.TBLitConfig
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10CN

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

variable {M : Type} [Group M]

theorem map_center_eq_self (α : MulAut M) : (center M).map (α : M →* M) = center M := by
  have key : ∀ (β : MulAut M) (z : M), z ∈ center M → β z ∈ center M := by
    intro β z hz
    rw [mem_center_iff] at hz ⊢
    intro w
    calc w * β z = β (β.symm w * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = β (z * β.symm w) := by rw [hz]
      _ = β z * w := by rw [map_mul, MulEquiv.apply_symm_apply]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact key α z hz
  · intro z hz
    exact ⟨α.symm z, key α.symm z hz, by simp⟩

@[expose] noncomputable def barAut (α : MulAut M) : MulAut (M ⧸ center M) :=
  QuotientGroup.congr (center M) (center M) α (map_center_eq_self α)

theorem barAut_mk (α : MulAut M) (x : M) :
    barAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem barAut_mul (α β : MulAut M) : barAut (α * β) = barAut α * barAut β := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAut.mul_apply, barAut_mk]

theorem barAut_one : barAut (1 : MulAut M) = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAut.one_apply, barAut_mk]

theorem barAut_mul_self {α : MulAut M} (hα : α * α = 1) : barAut α * barAut α = 1 := by
  rw [← barAut_mul, hα, barAut_one]

theorem barAut_mk_eq_iff (α : MulAut M) (x : M) :
    barAut α (QuotientGroup.mk x) = QuotientGroup.mk x ↔ x⁻¹ * α x ∈ center M := by
  rw [barAut_mk, eq_comm, QuotientGroup.eq]

@[expose] noncomputable def defect (α : MulAut M) :
    ↥((fixSub (barAut α)).comap (QuotientGroup.mk' (center M))) →* ↥(center M) where
  toFun x := ⟨(x : M)⁻¹ * α x, (barAut_mk_eq_iff α x).mp x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hx : (x : M)⁻¹ * α x ∈ center M := (barAut_mk_eq_iff α x).mp x.2
    have hc := mem_center_iff.mp hx (y : M)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
    calc (y : M)⁻¹ * (x : M)⁻¹ * (α x * α y) =
          (y : M)⁻¹ * ((x : M)⁻¹ * α x) * α y := by group
      _ = ((x : M)⁻¹ * α x) * (y : M)⁻¹ * α y := by rw [← hc]
      _ = (x : M)⁻¹ * α x * ((y : M)⁻¹ * α y) := by group

theorem mem_ker_defect_iff (α : MulAut M)
    (x : ↥((fixSub (barAut α)).comap (QuotientGroup.mk' (center M)))) :
    x ∈ (defect α).ker ↔ (x : M) ∈ fixSub α := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (x : M)⁻¹ * α x = 1 := congrArg Subtype.val h
    show α (x : M) = (x : M)
    calc α (x : M) = (x : M) * ((x : M)⁻¹ * α x) := by group
      _ = (x : M) := by rw [h1, mul_one]
  · intro h
    have h1 : α (x : M) = (x : M) := h
    apply Subtype.ext
    show (x : M)⁻¹ * α x = 1
    rw [h1, inv_mul_cancel]

theorem eq_one_of_barAut_eq_one [Group.IsPerfect M] {α : MulAut M} (h : barAut α = 1) :
    α = 1 := by
  have hall : ∀ x : M, x⁻¹ * α x ∈ center M := fun x =>
    (barAut_mk_eq_iff α x).mp (by rw [h]; rfl)
  let φ : M →* ↥(center M) :=
    { toFun := fun x => ⟨x⁻¹ * α x, hall x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := mem_center_iff.mp (hall x) y⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [← hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hφ : ∀ x : M, φ x = 1 := by
    intro x
    have h1 : x ∈ φ.ker := Abelianization.commutator_subset_ker φ
      (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top x)
    exact h1
  ext x
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val (hφ x)
  show α x = x
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h1, mul_one]

variable [Finite M]

theorem hasNormalPComplement_fixSub_barAut {α : MulAut M} (hZ : IsPGroup 2 (center M))
    (hC : HasNormalPComplement 2 ↥(fixSub α)) :
    HasNormalPComplement 2 ↥(fixSub (barAut α)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (fixSub (barAut α)).comap (QuotientGroup.mk' (center M)) with hP
  have hker : (defect α).ker = (fixSub α).subgroupOf P := by
    ext x
    rw [mem_ker_defect_iff, mem_subgroupOf]
  have hCP : fixSub α ≤ P := by
    intro x hx
    show barAut α (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [barAut_mk]
    exact congrArg QuotientGroup.mk (show α x = x from hx)
  have hq : IsPGroup 2 (↥P ⧸ (defect α).ker) :=
    (hZ.to_subgroup (defect α).range).of_equiv
      (QuotientGroup.quotientKerEquivRange (defect α)).symm
  have hKC : HasNormalPComplement 2 ↥((defect α).ker) :=
    QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv
      ((subgroupOfEquivOfLe hCP).symm.trans (MulEquiv.subgroupCongr hker.symm)) hC
  have hPC : HasNormalPComplement 2 ↥P :=
    BenderSuzuki.External.hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
      (defect α).ker hq hKC
  have hmap := RankThree.Coprime.hasNormalPComplement_map (QuotientGroup.mk' (center M)) hPC
  have hPm : P.map (QuotientGroup.mk' (center M)) = fixSub (barAut α) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hPm) hmap

theorem ne_one_of_hasNormalPComplement [Group.IsPerfect M] {z : M} (hz : orderOf z = 2)
    {α : MulAut M} (hC : HasNormalPComplement 2 ↥(fixSub α)) : α ≠ 1 := by
  rintro rfl
  have htop : fixSub (1 : MulAut M) = ⊤ := by
    ext x
    exact ⟨fun _ => mem_top x, fun _ => rfl⟩
  have hX : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M) := by
    have h1 : commutator M = ⊤ := Group.IsPerfect.commutator_eq_top
    rwa [commutator_def] at h1
  have heven : 2 ∣ Nat.card (⊤ : Subgroup M) := by
    rw [card_top, ← hz]
    exact orderOf_dvd_natCard z
  exact NoNilp.not_hasNormalPComplement le_rfl hX heven (htop ▸ hC)

theorem barAut_ne_one [Group.IsPerfect M] {z : M} (hz : orderOf z = 2) {α : MulAut M}
    (hC : HasNormalPComplement 2 ↥(fixSub α)) : barAut α ≠ 1 := fun h =>
  ne_one_of_hasNormalPComplement hz hC (eq_one_of_barAut_eq_one h)

end CFSG.ComponentClassification.CatLeafProof.X10CN
