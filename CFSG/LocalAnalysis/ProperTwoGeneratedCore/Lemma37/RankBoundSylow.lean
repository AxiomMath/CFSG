module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundStructure
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.Dihedral.GorensteinWalter

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.Semidihedral.CentralQuotients
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {t : X}

namespace RankBoundHyp

variable (h : RankBoundHyp X t)
include h

theorem mem_center_iff_mem_nativeQuaternionZ {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (T : Sylow 2 J) {m : ℕ} (hm : 2 ≤ m) (e : (T : Subgroup J) ≃* QuaternionGroup m)
    (x : (T : Subgroup J)) :
    (x : J) ∈ Subgroup.center J ↔ e x ∈ nativeQuaternionZ m := by
  constructor
  · intro hx
    have hxT : x ∈ Subgroup.center (T : Subgroup J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx g)
    have hc : e x ∈ Subgroup.center (QuaternionGroup m) := by
      rw [Subgroup.mem_center_iff] at hxT ⊢
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hxT g']
    rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 (e x)).mp hc with h0 | h1
    · rw [h0, ← QuaternionGroup.one_def]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers _
  · intro hx
    have hsq : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ^ 2 = 1 := by
      rw [pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self,
        ← QuaternionGroup.one_def]
    have hx2 : x ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one, ← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_pow_eq_one hsq)
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf (((x : J) : X)) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact orderOf_eq_prime hx2 hx1
      have hxt : ((x : J) : X) = t := h.eq_of_mem_component hJ (x : J).2 hord
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxt]
      exact Subgroup.mem_center_iff.mp h.central g

theorem exists_sylow_dihedral {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ P : Sylow 2 (J ⧸ Subgroup.center J), ∃ n : ℕ,
      Nonempty ((P : Subgroup (J ⧸ Subgroup.center J)) ≃* DihedralGroup n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨r, hr, ⟨e⟩⟩ := h.sylow_quaternion hJ T
  have hm : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  let P := Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) T
  refine ⟨P, 2 ^ (r - 2), ⟨?_⟩⟩
  let ψ : (T : Subgroup J) →* J ⧸ Subgroup.center J :=
    (QuotientGroup.mk' (Subgroup.center J)).comp (T : Subgroup J).subtype
  let χ : (T : Subgroup J) →* DihedralGroup (2 ^ (r - 2)) :=
    (quaternionToDihedral (2 ^ (r - 2))).comp e.toMonoidHom
  have hχ : Function.Surjective χ :=
    (quaternionToDihedral_surjective (2 ^ (r - 2))).comp e.surjective
  have hker : ψ.ker = χ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (QuotientGroup.mk' (Subgroup.center J)) (x : J) = 1 ↔
      quaternionToDihedral (2 ^ (r - 2)) (e x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← MonoidHom.mem_ker,
      quaternionToDihedral_ker]
    exact h.mem_center_iff_mem_nativeQuaternionZ hJ T hm e x
  have hrange : ψ.range = (P : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective χ hχ)))

theorem quotient_classification
    {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (J ⧸ Subgroup.center J ≃* PSL(2, GaloisField p k)) := by
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  obtain ⟨P, n, hP⟩ := h.exists_sylow_dihedral hJ
  exact CFSG.GorensteinWalter.gorenstein_walter _ hJ.1.2.2 P ⟨n, hP⟩

end RankBoundHyp

end CFSG.ProperTwoGeneratedCore.Lemma37
