module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.GroupTheory

open Subgroup
open TauCeti.Subgroup (normalizerQuotient)
open scoped commutatorElement

theorem isMulCommutative_normalizerQuotient_of_borel {G : Type} [Group G] [Finite G]
    {B U : Subgroup G} (hNB : Subgroup.normalizer (U : Set G) = B)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ U) :
    IsMulCommutative (normalizerQuotient U) := by
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_subgroupOf]
  have hx : (x : G) ∈ B := by rw [← hNB]; exact x.2
  have hy : (y : G) ∈ B := by rw [← hNB]; exact y.2
  have hcoe : (Subgroup.normalizer (U : Set G)).subtype ⁅x, y⁆ =
      (Subgroup.normalizer (U : Set G)).subtype x *
      (Subgroup.normalizer (U : Set G)).subtype y *
      ((Subgroup.normalizer (U : Set G)).subtype x)⁻¹ *
      ((Subgroup.normalizer (U : Set G)).subtype y)⁻¹ := by
    rw [map_commutatorElement, commutatorElement_def]
  change (Subgroup.normalizer (U : Set G)).subtype ⁅x, y⁆ ∈ U
  rw [hcoe]
  exact hcomm _ hx _ hy

theorem commutator_mem_of_diag_ker {G : Type} [Group G] {B U : Subgroup G}
    {A : Type} [CommGroup A] (φ : B →* A) (hker : φ.ker = U.subgroupOf B)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) : ⁅b, b'⁆ ∈ U := by
  have hmem : ⁅(⟨b, hb⟩ : ↥B), (⟨b', hb'⟩ : ↥B)⁆ ∈ _root_.commutator ↥B :=
    commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hker' := Abelianization.commutator_subset_ker φ hmem
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hcoe : ((⁅(⟨b, hb⟩ : ↥B), (⟨b', hb'⟩ : ↥B)⁆ : ↥B) : G) = ⁅b, b'⁆ :=
    map_commutatorElement B.subtype ⟨b, hb⟩ ⟨b', hb'⟩
  rwa [hcoe] at hker'

theorem isMulCommutative_normalizerQuotient_of_odd_cover {G X : Type} [Group G] [Finite G]
    [Group X] [Finite X] (α : G →* X) (hα : Function.Surjective α)
    (hodd : Odd (Nat.card α.ker)) {B U : Subgroup G}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hNB : Subgroup.normalizer (U : Set G) = B)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ U) :
    IsMulCommutative (normalizerQuotient (U.map α)) := by
  let B' : Subgroup X := U.map α
  have hNB' : Subgroup.normalizer (B' : Set X) = B.map α := by
    rw [← CFSG.ComponentClassification.OddKernelNormalizers.image α hα hodd U hU.2.1, hNB]
  have hUleB : U ≤ B := by rw [← hNB]; exact Subgroup.le_normalizer
  have hNBle : B ≤ Subgroup.normalizer (U : Set G) := by rw [hNB]
  have hNnormal : (U.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUleB).mpr hNBle
  let ψ : ↥B →* ↥(Subgroup.normalizer (B' : Set X)) :=
    { toFun := fun b => ⟨α b, by
        rw [hNB']
        exact Subgroup.mem_map_of_mem α b.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : (y : X) ∈ B.map α := by rw [← hNB']; exact y.2
    obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨b, hb⟩, Subtype.ext hbval⟩
  let φ : ↥B →* normalizerQuotient B' :=
    (TauCeti.Subgroup.normalizerQuotientMk B').comp ψ
  have hφ : Function.Surjective φ :=
    (TauCeti.Subgroup.normalizerQuotientMk_surjective B').comp hψ
  have hUker : U.subgroupOf B ≤ φ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    exact (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff B' (ψ u)).mpr
      (Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mp hu))
  have hBU : IsMulCommutative (↥B ⧸ U.subgroupOf B) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
      Subgroup.commutator_le]
    intro b _ b' _
    rw [Subgroup.mem_subgroupOf]
    exact hcomm b b.2 b' b'.2
  let Ψ : (↥B ⧸ U.subgroupOf B) →* normalizerQuotient B' :=
    @QuotientGroup.lift ↥B _ _ _ (U.subgroupOf B) hNnormal φ hUker
  have hΨ : Function.Surjective Ψ :=
    QuotientGroup.lift_surjective_of_surjective (U.subgroupOf B) φ hφ hUker
  rw [isMulCommutative_iff] at hBU ⊢
  intro a b
  obtain ⟨x, rfl⟩ := hΨ a
  obtain ⟨y, rfl⟩ := hΨ b
  rw [← map_mul, ← map_mul, hBU x y]

end CFSG.GroupTheory
