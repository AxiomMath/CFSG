module

public import CFSG.GH74.SectionalRank
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.Asc75.Conj
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec64_sylow_pair [Finite G] {T C : Subgroup G} {x y : G} (hT : IsSylow2Of T C)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) (hxC : x ∈ C)
    (hyC : y ∈ C) :
    ∃ T' : Subgroup G, IsSylow2Of T' C ∧ x ∈ T' ∧ y ∈ T' ∧
      CFSG.Open.pRank 2 T' = CFSG.Open.pRank 2 T ∧
      CFSG.GH74.sectionalTwoRank T' = CFSG.GH74.sectionalTwoRank T ∧ (IsCyclic ↥T' → IsCyclic ↥T) :=
  by
  have hx2 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hy2 : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute x y from hxy).zpow_zpow m n).eq
  have hElem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hx2)
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hy2) hcomm
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.isPGroup hElem
  have hPC : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ C :=
    sup_le ((Subgroup.zpowers_le (g := x)).mpr hxC) ((Subgroup.zpowers_le (g := y)).mpr hyC)
  obtain ⟨T', hT', hle⟩ := exists_isSylow2Of_ge hP hPC
  have hxT' : x ∈ T' := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hyT' : y ∈ T' := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  obtain ⟨a, -, hconj⟩ := IsSylow2Of.exists_conj_mem hT hT'
  have hT'eq : T' = CFSG.conjugate T a⁻¹ := by
    ext z
    simp only [hconj z, mem_conjugate_iff', inv_inv]
  let e : ↥T' ≃* ↥T :=
    (MulEquiv.subgroupCongr hT'eq).trans
      (Subgroup.equivMapOfInjective T (MulAut.conj (a⁻¹)⁻¹).toMonoidHom
        (MulAut.conj (a⁻¹)⁻¹).injective).symm
  refine ⟨T', hT', hxT', hyT', ?_, ?_, ?_⟩
  · rw [hT'eq, CFSG.Asc75.pRank_conjugate]
  · exact CFSG.GH74.sectionalTwoRank_eq_of_mulEquiv e
  · intro hcyc
    exact e.isCyclic.mp hcyc

end CFSG.OddStandard.SmallF3.Omega
