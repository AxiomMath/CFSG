module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedNormal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

section Special

variable {σ : E →+* E} (B : V →ₛₗ[σ] V →ₗ[E] E)

abbrev unitarySpecial : Subgroup (sesqUnitaryGroup B) :=
  (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B)

variable {B} in
theorem mem_unitarySpecial {g : sesqUnitaryGroup B} :
    g ∈ unitarySpecial B ↔
      LinearMap.det ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = 1 := by
  rw [Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
  exact and_iff_right g.2

instance unitarySpecial_normal : (unitarySpecial B).Normal where
  conj_mem g hg x := by
    rw [mem_unitarySpecial] at hg ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      map_mul, map_mul, hg, mul_one, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      map_one]

end Special

section Image

variable (h : UnitaryFieldData p f E) (B : V →ₛₗ[h.bar] V →ₗ[E] E)

abbrev projSpecial : Subgroup (sesqProjUnitary h B) :=
  (unitarySpecial B).map (QuotientGroup.mk' (sesqNormOneScalars h B))

instance projSpecial_normal : (projSpecial h B).Normal :=
  (unitarySpecial_normal B).map _ (QuotientGroup.mk'_surjective _)

@[expose] def specialProj : unitarySpecial B →* projSpecial h B :=
  ((QuotientGroup.mk' (sesqNormOneScalars h B)).comp (unitarySpecial B).subtype).codRestrict _
    fun g => Subgroup.mem_map_of_mem _ g.2

theorem specialProj_surjective : Function.Surjective (specialProj h B) := by
  rintro ⟨x, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ker_specialProj :
    (specialProj h B).ker = (sesqNormOneScalars h B).subgroupOf (unitarySpecial B) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
  exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩

@[expose] def specialQuotientEquiv :
    unitarySpecial B ⧸ (sesqNormOneScalars h B).subgroupOf (unitarySpecial B) ≃*
      projSpecial h B :=
  (QuotientGroup.quotientMulEquivOfEq (ker_specialProj h B).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (specialProj_surjective h B))

theorem specialQuotientEquiv_mk (g : unitarySpecial B) :
    (specialQuotientEquiv h B (QuotientGroup.mk g) : sesqProjUnitary h B) =
      QuotientGroup.mk (g : sesqUnitaryGroup B) :=
  rfl

end Image

section Fixed

variable {G : Type*} [Group G]

theorem fixedSubgroup_conj (a : G) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj a) = Subgroup.centralizer {a} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change a * x * a⁻¹ = x ↔ x * a = a * x
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

@[expose] def infSubgroupOfEquiv (N C : Subgroup G) : (N ⊓ C : Subgroup G) ≃* N.subgroupOf C :=
  (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).symm.trans
    (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right N C))

theorem inf_pComponent_quasisimple [Finite G] (N C : Subgroup G) [N.Normal] (ℓ : ℕ)
    [Fact ℓ.Prime] (hC : ∀ L : Subgroup C, CFSG.IsPComponent ℓ L → CFSG.IsQuasisimple L)
    (L : Subgroup (N ⊓ C : Subgroup G)) (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ (infSubgroupOfEquiv N C)
    (CatalogueBOrthogonalLinearFixed.normal_subgroup_pComponent_quasisimple (N.subgroupOf C) ℓ
      hC) L hL

end Fixed

theorem odd_unitary_inner_diagonal_involution_fixed_p_components (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    (∀ a : sesqProjUnitary h B, orderOf a = 2 → ∀ ℓ : ℕ, ℓ.Prime →
      ∀ L : Subgroup (projSpecial h B ⊓ Subgroup.centralizer {a} :
        Subgroup (sesqProjUnitary h B)),
        CFSG.IsPComponent ℓ L → CFSG.IsQuasisimple L) ∧
    (unitarySpecial B).Normal ∧ (projSpecial h B).Normal ∧
    ∃ e : unitarySpecial B ⧸ (sesqNormOneScalars h B).subgroupOf (unitarySpecial B) ≃*
        projSpecial h B,
      ∀ g : unitarySpecial B,
        (e (QuotientGroup.mk g) : sesqProjUnitary h B) =
          QuotientGroup.mk (g : sesqUnitaryGroup B) := by
  refine ⟨fun a ha ℓ hℓ L hL => ?_, inferInstance, inferInstance, specialQuotientEquiv h B,
    specialQuotientEquiv_mk h B⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite E := h.finite
  exact inf_pComponent_quasisimple (projSpecial h B) _ ℓ
    (projective_unitary_involution_centralizer_p_components h hp hn hB hBl a ha ℓ hℓ) L hL

end CFSG.ComponentClassification.CatalogueBUnitaryB
