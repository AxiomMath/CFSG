module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Kernel

variable {H P : Type*} [Group H] [Group P]

theorem card_eq_card_map_mul_card_ker_of_ker_le (φ : H →* P) {S : Subgroup H} (hS : φ.ker ≤ S) :
    Nat.card S = Nat.card (S.map φ) * Nat.card φ.ker := by
  have h1 := Subgroup.card_mul_index (φ.domRestrict S).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  rw [← h1, mul_comm, Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv]

theorem range_inf_stabilizer_eq_map {X : Type*} [MulAction H X] (x : X) :
    (MulAction.toPermHom H X).range ⊓ MulAction.stabilizer (Equiv.Perm X) x =
      (MulAction.stabilizer H x).map (MulAction.toPermHom H X) := by
  ext σ
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, hg⟩

theorem ker_toPermHom_le_stabilizer {X : Type*} [MulAction H X] (x : X) :
    (MulAction.toPermHom H X).ker ≤ MulAction.stabilizer H x := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [MulAction.mem_stabilizer_iff]
  exact congrArg (fun σ : Equiv.Perm X => σ x) hg

theorem card_stabilizer_eq_card_range_inf_mul {X : Type*} [MulAction H X] (x : X) :
    Nat.card (MulAction.stabilizer H x) =
      Nat.card ((MulAction.toPermHom H X).range ⊓ MulAction.stabilizer (Equiv.Perm X) x :
        Subgroup (Equiv.Perm X)) * Nat.card (MulAction.toPermHom H X).ker := by
  rw [range_inf_stabilizer_eq_map]
  exact card_eq_card_map_mul_card_ker_of_ker_le _ (ker_toPermHom_le_stabilizer x)

end Kernel

section Outer

variable {G : Type*} [Group G]

theorem card_dvd_card_sup_mul_card_outer {L T₁ M : Subgroup G} {t : G}
    (hML : M ≤ normalizer (L : Set G)) (hMT : M ≤ normalizer (T₁ : Set G))
    (hMt : M ≤ centralizer ({t} : Set G)) (htL : t ∈ centralizer (L : Set G))
    (hCt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ zpowers t) (hT₁ : T₁ ≤ L) :
    Nat.card M ∣ Nat.card (normalizer (T₁ : Set G) ⊓ L ⊔ zpowers t : Subgroup G) *
      Nat.card (Outer L) := by
  set ψ : M →* Outer L := (QuotientGroup.mk' (inner L)).comp
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hML)) with hψ
  have hcard : Nat.card M = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard]
  refine Nat.mul_dvd_mul ?_ (Subgroup.card_subgroup_dvd_card _)
  rw [← Subgroup.card_map_of_injective (K := ψ.ker) M.subtype_injective]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  obtain ⟨y, hy⟩ := hx
  have hconj : ∀ z ∈ L, (x : G) * z * (x : G)⁻¹ = (y : G) * z * (y : G)⁻¹ := by
    intro z hz
    have h2 := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : G)) hy
    simp only [MulAut.conj_apply, coe_mul, coe_inv, MonoidHom.comp_apply,
      normalizerMonoidHom_apply_apply_coe, coe_inclusion] at h2
    exact h2.symm
  have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.mp (hMt x.2)
  have hyt : (y : G) * t = t * y := mem_centralizer_iff.mp htL y y.2
  have hkL : (y : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    refine mem_centralizer_iff.mpr fun z hz => ?_
    calc z * ((y : G)⁻¹ * x) = (y : G)⁻¹ * (y * z * (y : G)⁻¹) * x := by group
      _ = (y : G)⁻¹ * (x * z * (x : G)⁻¹) * x := by rw [hconj z hz]
      _ = (y : G)⁻¹ * x * z := by group
  have hkt : (y : G)⁻¹ * x ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (y : G)⁻¹ * x * t = (y : G)⁻¹ * (t * x) := by rw [mul_assoc, hxt]
      _ = t * ((y : G)⁻¹ * x) := by
        rw [← mul_assoc, ← mul_assoc, (Commute.inv_left hyt).eq]
  have hk : (y : G)⁻¹ * x ∈ zpowers t := hCt (mem_inf.mpr ⟨hkL, hkt⟩)
  have hkT₁ : ((y : G)⁻¹ * x)⁻¹ ∈ normalizer (T₁ : Set G) :=
    inv_mem (zpowers_le.mpr (centralizer_le_normalizer _ (centralizer_le hT₁ htL)) hk)
  have hyN : (y : G) ∈ normalizer (T₁ : Set G) := by
    have e : (y : G) = x * ((y : G)⁻¹ * x)⁻¹ := by group
    rw [e]
    exact mul_mem (hMT x.2) hkT₁
  have e : (x : G) = y * ((y : G)⁻¹ * x) := by group
  change (x : G) ∈ normalizer (T₁ : Set G) ⊓ L ⊔ zpowers t
  rw [e]
  exact mul_mem_sup (mem_inf.mpr ⟨hyN, y.2⟩) hk

end Outer

end CFSG.SeitzReduction.RankOne
