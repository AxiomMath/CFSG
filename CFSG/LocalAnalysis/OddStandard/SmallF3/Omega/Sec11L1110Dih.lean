module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralSubgroupShapes
public import CFSG.CharacterTheory.Semidihedral.ElementStructure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem dih_unique_involution {X : Type} [Group X] [Finite X] [IsCyclic X]
    {a b : X} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hsub : ({1, a, b} : Finset X) ⊆ Finset.univ.filter (fun x : X => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h
    · rw [h]
      exact one_pow 2
    · rw [h, ← ha]
      exact pow_orderOf_eq_one a
    · rw [h, ← hb]
      exact pow_orderOf_eq_one b
  have hcard : ({1, a, b} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [ha1.symm, hb1.symm]
  have := Finset.card_le_card hsub
  omega

private theorem dih_case {E : Type} [Group E] [Finite E] {D : Subgroup E} {m : ℕ} (hm : 1 ≤ m)
    (hD : Nonempty (↥D ≃* DihedralGroup (2 ^ m)))
    {Θ : Set E} (hΘD : Θ ⊆ D) (hΘ2 : ∀ s ∈ Θ, orderOf s = 2) {t z : E}
    (ht : t ∈ Θ) (htz : t * z ∈ Θ) (hz : z * z = 1) (hz1 : z ≠ 1) :
    IsDih2 (Subgroup.closure Θ) := by
  classical
  set C : Subgroup E := Subgroup.closure Θ
  have hCD : C ≤ D := (Subgroup.closure_le D).mpr hΘD
  have hS : Nonempty (DihedralGroup (2 ^ ((m + 1) - 1)) ≃* ↥D) := by
    obtain ⟨e⟩ := hD
    rw [show m + 1 - 1 = m from Nat.add_sub_cancel m 1]
    exact ⟨e.symm⟩
  have hshapes := CFSG.Semidihedral.Principal.dihedral_subgroup_shapes (S := ↥D)
    (n := m + 1) (by omega) hS
  rcases hshapes.1 (C.subgroupOf D) with hcyc | ⟨m', hm'2, -, ⟨eT⟩⟩
  · exfalso
    haveI : IsCyclic C := (Subgroup.subgroupOfEquivOfLe hCD).isCyclic.mp hcyc
    have htC : t ∈ C := Subgroup.subset_closure ht
    have htzC : t * z ∈ C := Subgroup.subset_closure htz
    have hzC : z ∈ C := by
      have hmul : t⁻¹ * (t * z) ∈ C := C.mul_mem (C.inv_mem htC) htzC
      simpa using hmul
    have hto : orderOf (⟨t, htC⟩ : C) = 2 := by
      rw [Subgroup.orderOf_mk, hΘ2 t ht]
    have hzo : orderOf (⟨z, hzC⟩ : C) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rwa [pow_two] : z ^ 2 = 1) hz1
    have htz_eq : (⟨t, htC⟩ : C) = ⟨z, hzC⟩ := dih_unique_involution hto hzo
    have htz1 : t * z ≠ 1 := by
      intro h1
      have h2 := hΘ2 (t * z) htz
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have htnez : t ≠ z := by
      intro h
      exact htz1 (by rw [h, hz])
    exact htnez (congrArg Subtype.val htz_eq)
  · exact ⟨m' - 1, by omega, ⟨(Subgroup.subgroupOfEquivOfLe hCD).symm.trans eT⟩⟩

theorem sec11L1110_isDih2_closure {E : Type} [Group E] [Finite E] {D : Subgroup E}
    (hD : IsDihSd D) {Θ : Set E} (hΘD : Θ ⊆ D) (hΘ2 : ∀ s ∈ Θ, orderOf s = 2) {t z : E}
    (ht : t ∈ Θ) (htz : t * z ∈ Θ) (hz : z * z = 1) (hz1 : z ≠ 1) (hcomm : t * z = z * t) :
    IsDih2 (Subgroup.closure Θ) := by
  rcases hD with ⟨m, hm, hD⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact dih_case hm hD hΘD hΘ2 ht htz hz hz1
  ·
    let f : CFSG.Open.SemidihedralGroup n →* E := D.subtype.comp e.symm.toMonoidHom
    have hf : Function.Injective f := by
      intro a b hab
      exact e.symm.injective (Subtype.val_injective hab)
    let D' : Subgroup E := (CFSG.Semidihedral.dihedralSubgroup n).map f
    have hD' : Nonempty (↥D' ≃* DihedralGroup (2 ^ (n - 2))) :=
      ⟨(Subgroup.equivMapOfInjective (CFSG.Semidihedral.dihedralSubgroup n) f hf).symm.trans
        (CFSG.Semidihedral.dihedralEquiv n hn).symm⟩
    have hΘD' : Θ ⊆ D' := by
      intro s hs
      refine ⟨e ⟨s, hΘD hs⟩, ?_, ?_⟩
      · exact CFSG.Semidihedral.involution_mem_dihedralSubgroup n (by omega) _
          (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hΘ2 s hs])
      · show f (e ⟨s, hΘD hs⟩) = s
        simp [f]
    exact dih_case (m := n - 2) (by omega) hD' hΘD' hΘ2 ht htz hz hz1

end CFSG.OddStandard.SmallF3.Omega
