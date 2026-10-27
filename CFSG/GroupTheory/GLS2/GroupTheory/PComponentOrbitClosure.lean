module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.StandardType.GGPumpupQuot
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.SecondGeneration

open Subgroup CFSG.GH74.GLS

variable {G : Type*} [Group G]

theorem map_normalClosure_subgroupOf_eq_closureIn
    (N I : Subgroup G) (hIN : I ≤ N) :
    (Subgroup.normalClosure (I.subgroupOf N : Set N)).map N.subtype =
      CFSG.StandardType.GGPumpup.closureIn N I := by
  let J := (Subgroup.normalClosure (I.subgroupOf N : Set N)).map N.subtype
  have hJN : J ≤ N := Subgroup.map_subtype_le _
  have hIJ : I ≤ J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hIN]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hJnormal : (J.subgroupOf N).Normal := by
    have heq : J.subgroupOf N = Subgroup.normalClosure (I.subgroupOf N : Set N) :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [heq]
    infer_instance
  have hNJ : N ≤ normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).mp hJnormal
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.normalClosure (I.subgroupOf N : Set N) ≤
      (CFSG.StandardType.GGPumpup.closureIn N I).subgroupOf N
    let : ((CFSG.StandardType.GGPumpup.closureIn N I).subgroupOf N).Normal :=
      CFSG.StandardType.GGPumpup.closureIn_subgroupOf_normal hIN
    apply Subgroup.normalClosure_le_normal
    intro i hi
    exact CFSG.StandardType.GGPumpup.le_closureIn N I hi
  · apply CFSG.StandardType.GGPumpup.closureIn_le
    intro n hn
    exact ((CFSG.StandardType.GGPumpup.conjugate_le_conjugate_iff n).mpr hIJ).trans
      (CFSG.StandardType.GGPumpup.conjugate_eq_of_mem_normalizer (hNJ hn)).le

private theorem orbitJoinLT_inv_eq_iSup_map_conj
    (A : Subgroup G) (x : G) (n : ℕ) :
    CFSG.StandardType.GGPumpup.orbitJoinLT A x⁻¹ n =
      ⨆ i : Fin n, A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom := by
  apply le_antisymm
  · apply CFSG.StandardType.GGPumpup.orbitJoinLT_le
    intro i hi
    simpa only [CFSG.conjugate, inv_pow, inv_inv] using
      (le_iSup (fun i : Fin n =>
        A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom) ⟨i, hi⟩)
  · refine iSup_le fun i => ?_
    simpa only [CFSG.conjugate, inv_pow, inv_inv] using
      CFSG.StandardType.GGPumpup.conjugate_le_orbitJoinLT A x⁻¹ i.2

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_pComponent_normalClosure_eq_orbit_join
    {x : G} (hx : orderOf x = p) {I : Subgroup G}
    (hI : IsPCompIn p (centralizer ({x} : Set G)) I)
    (hIL : I ≤ CFSG.pLayer G p) :
    let J := (Subgroup.normalClosure
      (I.subgroupOf (CFSG.pLayer G p) : Set (CFSG.pLayer G p))).map
        (CFSG.pLayer G p).subtype
    ∃ A : Subgroup G, CFSG.IsPComponent p A ∧
      J = (⨆ i : Fin p, A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom) ∧
      (∀ i : Fin p, CFSG.IsPComponent p
        (A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom)) ∧
      (∀ i : Fin p,
        (A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom).map
            (MulAut.conj x).toMonoidHom =
          A.map (MulAut.conj (x ^ (((i : ℕ) + 1) % p))).toMonoidHom) ∧
      ((x ∈ normalizer (A : Set G) ∧ J = A) ∨
        (x ∉ normalizer (A : Set G) ∧ Function.Injective
          (fun i : Fin p => A.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom))) := by
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hCinv : centralizer ({x⁻¹} : Set G) = centralizer ({x} : Set G) := by
    ext a
    simp only [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  have hIinv : IsPCompIn p (centralizer ({x⁻¹} : Set G)) I := by
    rwa [hCinv]
  obtain ⟨A, hA, hclosure⟩ :=
    CFSG.StandardType.GGPumpup.exists_pComponent_closureIn_eq
      (x := x⁻¹) (by rw [inv_pow, hxp, inv_one]) hIinv.1 hIinv.2 hIL
  let J := (Subgroup.normalClosure
    (I.subgroupOf (CFSG.pLayer G p) : Set (CFSG.pLayer G p))).map
      (CFSG.pLayer G p).subtype
  have hJ : J = CFSG.StandardType.GGPumpup.orbitJoinLT A x⁻¹ p :=
    (map_normalClosure_subgroupOf_eq_closureIn (CFSG.pLayer G p) I hIL).trans hclosure
  refine ⟨A, hA, hJ.trans (orbitJoinLT_inv_eq_iSup_map_conj A x p), ?_, ?_, ?_⟩
  · intro i
    exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent
      p (MulAut.conj (x ^ (i : ℕ))) hA
  · intro i
    change (CFSG.GroupTheory.conjugatePower x A (i : ℕ)).map
      (MulAut.conj x).toMonoidHom =
        CFSG.GroupTheory.conjugatePower x A (((i : ℕ) + 1) % p)
    have h := CFSG.GroupTheory.conjugatePower_add x A 1 (i : ℕ)
    simp only [pow_one] at h
    rw [← h, Nat.add_comm 1 (i : ℕ), CFSG.GroupTheory.conjugatePower_mod x A hxp]
  · by_cases hxA : x ∈ normalizer (A : Set G)
    · exact Or.inl ⟨hxA, hJ.trans
        (CFSG.StandardType.GGPumpup.orbitJoinLT_eq_self (inv_mem hxA)
          (Fact.out : p.Prime).pos)⟩
    · refine Or.inr ⟨hxA, ?_⟩
      intro i j hij
      apply Fin.ext
      exact CFSG.GroupTheory.conjugatePower_injOn (by rw [hx]; exact Fact.out) hxA
        (by rw [Set.mem_Iio, hx]; exact i.2)
        (by rw [Set.mem_Iio, hx]; exact j.2) hij

end CFSG.SecondGeneration
