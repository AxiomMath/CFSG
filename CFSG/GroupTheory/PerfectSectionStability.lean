module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

private noncomputable def commutatorQuotientHom {G : Type*} [Group G]
    {V J T N : Subgroup G}
    (hTJ : ⁅T, J⁆ ≤ N) (hJT : J ≤ Subgroup.normalizer (T : Set G))
    (hVJ : ⁅V, J⁆ ≤ T) (hNn : (N.subgroupOf T).Normal) (v : G) (hv : v ∈ V) :
    J →* T ⧸ N.subgroupOf T := by
  classical
  haveI : (N.subgroupOf T).Normal := hNn
  have hTJ' : ⁅J, T⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact hTJ
  have hmem : ∀ l : J, ⁅v, (l : G)⁆ ∈ T := fun l =>
    hVJ (Subgroup.commutator_mem_commutator hv l.2)
  let q : T →* T ⧸ N.subgroupOf T := QuotientGroup.mk' (N.subgroupOf T)
  exact
  { toFun := fun l => q ⟨⁅v, (l : G)⁆, hmem l⟩
    map_one' := by
      change QuotientGroup.mk' (N.subgroupOf T)
        ⟨⁅v, ((1 : J) : G)⁆, hmem 1⟩ = 1
      refine (QuotientGroup.eq_one_iff (N := N.subgroupOf T) _).mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using N.one_mem
    map_mul' := by
      intro l l'
      change QuotientGroup.mk' (N.subgroupOf T)
          ⟨⁅v, (l : G) * (l' : G)⁆, hmem (l * l')⟩ =
        QuotientGroup.mk' (N.subgroupOf T) ⟨⁅v, (l : G)⁆, hmem l⟩ *
          QuotientGroup.mk' (N.subgroupOf T) ⟨⁅v, (l' : G)⁆, hmem l'⟩
      rw [← map_mul]
      refine (QuotientGroup.mk'_eq_mk' (N := N.subgroupOf T)).mpr
        ⟨⟨((l : G) * ⁅v, (l' : G)⁆ * (l : G)⁻¹)⁻¹ * ⁅v, (l' : G)⁆, ?_⟩, ?_, ?_⟩
      · have hb : (l : G) * ⁅v, (l' : G)⁆ * (l : G)⁻¹ ∈ T :=
          (Subgroup.mem_normalizer_iff.mp (hJT l.2) ⁅v, (l' : G)⁆).1 (hmem l')
        exact T.mul_mem (T.inv_mem hb) (hmem l')
      · rw [Subgroup.mem_subgroupOf]
        change ((l : G) * ⁅v, (l' : G)⁆ * (l : G)⁻¹)⁻¹ * ⁅v, (l' : G)⁆ ∈ N
        have hz : ((l : G) * ⁅v, (l' : G)⁆ * (l : G)⁻¹)⁻¹ * ⁅v, (l' : G)⁆ =
            ⁅(l : G), (⁅v, (l' : G)⁆)⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [hz]
        exact hTJ' (Subgroup.commutator_mem_commutator l.2 (T.inv_mem (hmem l')))
      · apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [commutatorElement_mul_right_eq_mul_conj]
        group }

theorem commutator_le_of_isPerfect_of_le {G : Type*} [Group G] {V J T N : Subgroup G}
    (hJ : Group.IsPerfect J) (hTs : Group.IsSolvable T) (hNT : N ≤ T)
    (hNn : (N.subgroupOf T).Normal) (hTJ : ⁅T, J⁆ ≤ N) (hVJ : ⁅V, J⁆ ≤ T) :
    ⁅V, J⁆ ≤ N := by
  classical
  haveI : Group.IsPerfect J := hJ
  haveI : Group.IsSolvable T := hTs
  haveI : (N.subgroupOf T).Normal := hNn
  have hJT : J ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hTJ.trans hNT)
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hmem : ⁅v, (l : G)⁆ ∈ T := hVJ (Subgroup.commutator_mem_commutator hv hl)
  let φ := commutatorQuotientHom hTJ hJT hVJ hNn v hv
  have hφ1 : φ = 1 := by
    have hrange : φ.range = ⊥ := by
      by_contra hne
      haveI : Nontrivial φ.range :=
        (Subgroup.nontrivial_iff_ne_bot φ.range).mpr hne
      haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact Group.IsPerfect.not_isSolvable φ.range inferInstance
    refine MonoidHom.ext fun x => ?_
    have hx : φ x ∈ φ.range := ⟨x, rfl⟩
    rw [hrange] at hx
    simpa using hx
  have hφl : φ ⟨l, hl⟩ = 1 := by rw [hφ1]; rfl
  have hmemN : (⟨⁅v, ((⟨l, hl⟩ : J) : G)⁆, hmem⟩ : T) ∈ N.subgroupOf T := by
    simpa [φ, commutatorQuotientHom] using hφl
  exact Subgroup.mem_subgroupOf.mp hmemN

end CFSG.GroupTheory
