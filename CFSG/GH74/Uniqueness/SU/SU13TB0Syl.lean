module

public import CFSG.GH74.Uniqueness.SU.SU4Sylow

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TB

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {G : Type} [Group G]

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] [Finite G] {S T : Subgroup G}
    (hS : IsPGroup p S) (hTS : T < S) :
    ∃ g ∈ S, g ∈ normalizer (T : Set G) ∧ g ∉ T := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < normalizer (T.subgroupOf S : Set S) := by
    refine Group.normalizerCondition_of_isNilpotent (T.subgroupOf S) ?_
    refine lt_top_iff_ne_top.mpr (fun h => ?_)
    exact absurd (Subgroup.subgroupOf_eq_top.mp h) (not_le_of_gt hTS)
  obtain ⟨⟨g, hgS⟩, hgN, hgT⟩ := Set.exists_of_ssubset hlt
  refine ⟨g, hgS, ?_, fun h => hgT h⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhS : h ∈ S := hTS.le hh
    exact (mem_normalizer_iff.mp hgN ⟨h, hhS⟩).mp hh
  · intro hh
    have hhS : h ∈ S := by
      have := S.mul_mem (S.mul_mem (S.inv_mem hgS) (hTS.le hh)) hgS
      simpa [mul_assoc] using this
    exact (mem_normalizer_iff.mp hgN ⟨h, hhS⟩).mpr hh

variable [Finite G]

theorem isSylowIn_of_normalizer_le_centralizer {X T : Subgroup G} {z : G}
    (hT : IsSylowIn (X ⊓ centralizer ({z} : Set G)) T)
    (hN : ∀ g ∈ X, g ∈ normalizer (T : Set G) → g * z = z * g) : IsSylowIn X T := by
  have hTX : T ≤ X := hT.1.trans inf_le_left
  obtain ⟨S, hS, hTS⟩ := exists_isSylowIn_ge hTX hT.isPGroup
  have hTeq : T = S := by
    by_contra hne
    obtain ⟨g, hgS, hgN, hgT⟩ := exists_mem_normalizer_not_mem (p := 2) hS.isPGroup
      (lt_of_le_of_ne hTS hne)
    have hK : T ⊔ zpowers g ≤ S := sup_le hTS ((zpowers_le).mpr hgS)
    have hKC : T ⊔ zpowers g ≤ X ⊓ centralizer ({z} : Set G) := by
      refine sup_le hT.1 ((zpowers_le).mpr ?_)
      refine mem_inf.mpr ⟨hS.1 hgS, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact hN g (hS.1 hgS) hgN
    have hKp : IsPGroup 2 (T ⊔ zpowers g : Subgroup G) := hS.isPGroup.to_le hK
    have := hT.eq_of_le hKC hKp le_sup_left
    exact hgT (this ▸ (le_sup_right : zpowers g ≤ T ⊔ zpowers g) (mem_zpowers g))
  rw [hTeq]
  exact hS

theorem isSylowIn_of_unique_involution {X T : Subgroup G} {z : G}
    (hT : IsSylowIn (X ⊓ centralizer ({z} : Set G)) T) (hzT : z ∈ T) (hz : orderOf z = 2)
    (hu : ∀ y ∈ T, orderOf y = 2 → y = z) : IsSylowIn X T := by
  refine isSylowIn_of_normalizer_le_centralizer hT fun g _ hg => ?_
  have hgz : g * z * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg z).mp hzT
  have hord : orderOf (g * z * g⁻¹) = 2 := by
    have h := (MulAut.conj g).orderOf_eq z
    rw [MulAut.conj_apply] at h
    rw [h]; exact hz
  have := hu _ hgz hord
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem eq_of_isPGroup_le_of_normalizer {p : ℕ} [Fact p.Prime] {H E Es R : Subgroup G}
    (hEH : normalizer (E : Set G) ≤ H)
    (hchar : ∀ g ∈ normalizer (Es : Set G), g ∈ normalizer (E : Set G))
    (hmax : ∀ R' : Subgroup G, R' ≤ H → IsPGroup p R' → Es ≤ R' → R' = Es)
    (hR : IsPGroup p R) (hER : Es ≤ R) : R = Es := by
  by_contra hne
  obtain ⟨g, hgR, hgN, hgE⟩ := exists_mem_normalizer_not_mem (p := p) hR
    (lt_of_le_of_ne hER (Ne.symm hne))
  have hgH : g ∈ H := hEH (hchar g hgN)
  have hK : Es ⊔ zpowers g ≤ R := sup_le hER ((zpowers_le).mpr hgR)
  have hKH : Es ⊔ zpowers g ≤ H := sup_le (fun x hx => hEH (hchar x (le_normalizer hx))) 
    ((zpowers_le).mpr hgH)
  have := hmax _ hKH (hR.to_le hK) le_sup_left
  exact hgE (this ▸ (le_sup_right : zpowers g ≤ Es ⊔ zpowers g) (mem_zpowers g))

end CFSG.GH74.Uniqueness.SU.SU13.TB
