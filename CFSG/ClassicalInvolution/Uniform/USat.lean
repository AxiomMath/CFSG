module

public import CFSG.ClassicalInvolution.Uniform.USaturate
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

open scoped Classical in
@[expose] noncomputable def satU (t : MemberType) {Y : Type*} [Group Y] (K : Subgroup Y) (z : Y) :
    Subgroup Y :=
  if t.IsSolvableType then K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) else K

section Basic

variable {t : MemberType} {Y : Type*} [Group Y] {K : Subgroup Y} {z : Y}

theorem satU_of_isSolvableType (hs : t.IsSolvableType) :
    satU t K z = K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) := by
  simp [satU, hs]

theorem satU_of_not_isSolvableType (hs : ¬ t.IsSolvableType) : satU t K z = K := by
  simp [satU, hs]

theorem le_satU : K ≤ satU t K z := by
  by_cases hs : t.IsSolvableType
  · rw [satU_of_isSolvableType hs]
    exact le_sup_left
  · rw [satU_of_not_isSolvableType hs]

theorem satU_eq_of_isIntrinsicU (h : IsIntrinsicU t K z) : satU t K z = K := by
  by_cases hs : t.IsSolvableType
  · rw [satU_of_isSolvableType hs]
    exact sup_eq_left.mpr (h hs)
  · exact satU_of_not_isSolvableType hs

theorem oddCoreIn_le_satU (hs : t.IsSolvableType) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) ≤ satU t K z := by
  rw [satU_of_isSolvableType hs]
  exact le_sup_right

theorem isIntrinsicU_satU (t : MemberType) (K : Subgroup Y) (z : Y) :
    IsIntrinsicU t (satU t K z) z := fun hs => oddCoreIn_le_satU hs

theorem mem_satU_of_mem (h : z ∈ K) : z ∈ satU t K z := le_satU h

theorem satU_satU (t : MemberType) (K : Subgroup Y) (z : Y) :
    satU t (satU t K z) z = satU t K z :=
  satU_eq_of_isIntrinsicU (isIntrinsicU_satU t K z)

end Basic

section Member

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem IsClassicalMemberU.satU_member (h : IsClassicalMemberU t K z) :
    IsClassicalMemberU t (satU t K z) z := by
  by_cases hs : t.IsSolvableType
  · rw [satU_of_isSolvableType hs]
    exact (h.saturate hs).1
  · rwa [satU_of_not_isSolvableType hs]

end Member

section Conj

variable {t : MemberType} {Y : Type} [Group Y] {K : Subgroup Y} {z : Y}

theorem satU_conj (t : MemberType) (K : Subgroup Y) (z g : Y) :
    satU t (conjSub g K) (g * z * g⁻¹) = conjSub g (satU t K z) := by
  by_cases hs : t.IsSolvableType
  · rw [satU_of_isSolvableType hs, satU_of_isSolvableType hs, ← map_conj_centralizer_singleton g z,
      show (Subgroup.centralizer ({z} : Set Y)).map (MulAut.conj g).toMonoidHom =
        conjSub g (Subgroup.centralizer ({z} : Set Y)) from rfl, oddCoreIn_conjSub]
    exact (Subgroup.map_sup _ _ _).symm
  · rw [satU_of_not_isSolvableType hs, satU_of_not_isSolvableType hs]

theorem mem_conjClass_satU_iff {J : Subgroup Y} :
    J ∈ CoreAssembly.conjClass (satU t K z) ↔
      ∃ g : Y, J = satU t (conjSub g K) (g * z * g⁻¹) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (satU_conj t K z g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, (satU_conj t K z g).symm⟩

end Conj

end CFSG.ClassicalInvolution.Uniform
