module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPrimeResidual
public import CFSG.LocalAnalysis.ComponentClassification.BFailureOddLowerImage

public section

namespace CFSG.ComponentClassification.LiteratureLocal

open CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {G : Type*} [Group G] [Finite G]

theorem eq_top_of_isPGroup_quotient_of_perfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] {p : ℕ} [Fact p.Prime] (N : Subgroup X) [N.Normal]
    (h : IsPGroup p (X ⧸ N)) : N = ⊤ := by
  rw [← QuotientGroup.subsingleton_iff]
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  have : Group.IsNilpotent (X ⧸ N) := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

theorem p_component_commutator_eq_bot_of_le_centralizer {p : ℕ} [Fact p.Prime]
    {S P H : Subgroup G} (hS : IsPGroup p S) (hPn : P.Normal) (hP : IsPGroup p P)
    (hCH : Subgroup.centralizer (S : Set G) ≤ H) {L : Subgroup H} (hL : IsPComponent p L)
    (hLS : L.map H.subtype ≤ Subgroup.centralizer (S : Set G)) :
    ⁅L.map H.subtype, P⁆ = ⊥ := by
  have hPH : L.map H.subtype ≤ Subgroup.centralizer ((P ⊓ H : Subgroup G) : Set G) := by
    have hnormal : (P.subgroupOf H).Normal := hPn.subgroupOf H
    have hpgroup : IsPGroup p (P.subgroupOf H) := hP.comap_of_injective _ H.subtype_injective
    have h := congrArg (Subgroup.map H.subtype)
      (p_component_normal_p_centralizer hL hnormal hpgroup)
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hperfect : Group.IsPerfect L := CatalogueBHeldSmallCore.pComponent_perfect p L hL
  have hLmem : ∀ x : L, ((x : H) : G) ∈ L.map H.subtype :=
    fun x => Subgroup.mem_map_of_mem H.subtype x.2
  let α : L →* MulAut P := (MulAut.conjNormal (H := P)).comp (H.subtype.comp L.subtype)
  let β : S →* MulAut P := (MulAut.conjNormal (H := P)).comp S.subtype
  have hα : ∀ x v, ((α x v : P) : G) = ((x : H) : G) * v * ((x : H) : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ b v, ((β b v : P) : G) = (b : G) * v * (b : G)⁻¹ := fun _ _ => rfl
  have hcomm : ∀ x b, α x * β b = β b * α x := by
    intro x b
    have hxb : (b : G) * ((x : H) : G) = ((x : H) : G) * b :=
      Subgroup.mem_centralizer_iff.mp (hLS (hLmem x)) b b.2
    ext v
    simp only [MulAut.mul_apply, hα, hβ]
    calc ((x : H) : G) * ((b : G) * v * (b : G)⁻¹) * ((x : H) : G)⁻¹
        = (((x : H) : G) * b) * v * (((x : H) : G) * b)⁻¹ := by group
      _ = ((b : G) * ((x : H) : G)) * v * ((b : G) * ((x : H) : G))⁻¹ := by rw [hxb]
      _ = (b : G) * (((x : H) : G) * v * ((x : H) : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix : ∀ x v, (∀ b, β b v = v) → α x v = v := by
    intro x v hv
    have hvS : (v : G) ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hv ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (v : G) = b * v * b⁻¹ * b := by group
        _ = v * b := by rw [h]
    have hxv : (v : G) * ((x : H) : G) = ((x : H) : G) * v :=
      Subgroup.mem_centralizer_iff.mp (hPH (hLmem x)) v ⟨v.2, hCH hvS⟩
    apply Subtype.ext
    rw [hα, ← hxv, mul_inv_cancel_right]
  have hall := (OutcomeLocal.prime_residual_commuting_fixed_points (p := p) hP
    (fun N _ hN => eq_top_of_isPGroup_quotient_of_perfect N hN) hS α β hcomm).mp hfix
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := congrArg Subtype.val (hall ⟨y, hy⟩ ⟨v, hv⟩)
  rw [hα] at h
  calc v * H.subtype y = (y : G) * v * (y : G)⁻¹ * y := by
        rw [h]
        rfl
    _ = H.subtype y * v := by
        simp only [Subgroup.coe_subtype, inv_mul_cancel_right]

theorem local_p_component_centralizes_ambient_p_core :
    (∀ (p : ℕ) (_ : p.Prime) (S P : Subgroup G), IsPGroup p S → P.Normal → IsPGroup p P →
      ∀ L : Subgroup (Subgroup.normalizer (S : Set G)), IsPComponent p L →
        ⁅L.map (Subgroup.normalizer (S : Set G)).subtype, P⁆ = ⊥) ∧
    ∀ S : Subgroup G, IsPGroup 2 S →
      (badTwoComponentSubgroup (Subgroup.normalizer (S : Set G))).map
        (Subgroup.normalizer (S : Set G)).subtype ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
  have hmain : ∀ (p : ℕ) (_ : p.Prime) (S P : Subgroup G), IsPGroup p S → P.Normal →
      IsPGroup p P → ∀ L : Subgroup (Subgroup.normalizer (S : Set G)), IsPComponent p L →
        ⁅L.map (Subgroup.normalizer (S : Set G)).subtype, P⁆ = ⊥ := by
    intro p hp S P hS hPn hP L hL
    have : Fact p.Prime := ⟨hp⟩
    exact p_component_commutator_eq_bot_of_le_centralizer hS hPn hP
      (Subgroup.centralizer_le_normalizer _) hL
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (p_component_normalizer_centralizes hS hL))
  refine ⟨hmain, fun S hS => ?_⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (hmain 2 Nat.prime_two S _ hS pCore_normal pCore_isPGroup L hL.1)

theorem badSubgroup_normalizer_le_centralizer_pCore {S : Subgroup G} (hS : IsPGroup 2 S) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G))).map
      (Subgroup.normalizer (S : Set G)).subtype ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
  rw [BFailureOdd.badSubgroup_eq_badTwoComponentSubgroup]
  exact local_p_component_centralizes_ambient_p_core.2 S hS

end CFSG.ComponentClassification.LiteratureLocal
