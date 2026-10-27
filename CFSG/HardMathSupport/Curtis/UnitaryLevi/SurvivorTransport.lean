module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {K : Type} [Field K] {r ε f : ℕ}

theorem center_statedSU_eq_scalars [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) :
    Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f) hK
    (by omega) ?_).2
  intro e
  have := congrArg Prod.fst e
  simp at this
  omega

@[expose] noncomputable def hypPSUToCentralQuot (h : UnitaryFieldData 2 f K) {n : ℕ}
    (ψ : hypSU h r ε ≃* StatedSU n (2 ^ f) K)
    (hZ : (hypScalars h r ε).map ψ.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
    (hc : Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) :
    hypPSU h r ε →* StatedSU n (2 ^ f) K ⧸ Subgroup.center (StatedSU n (2 ^ f) K) :=
  QuotientGroup.lift (hypScalars h r ε)
    ((QuotientGroup.mk' (Subgroup.center (StatedSU n (2 ^ f) K))).comp ψ.toMonoidHom) (by
      intro z hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hc, ← hZ]
      exact ⟨z, hz, rfl⟩)

theorem hypPSUToCentralQuot_hypProj (h : UnitaryFieldData 2 f K) {n : ℕ}
    (ψ : hypSU h r ε ≃* StatedSU n (2 ^ f) K)
    (hZ : (hypScalars h r ε).map ψ.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
    (hc : Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) (g : hypSU h r ε) :
    hypPSUToCentralQuot h ψ hZ hc (hypProj h r ε g) =
      QuotientGroup.mk' (Subgroup.center (StatedSU n (2 ^ f) K)) (ψ g) := rfl

theorem hypPSUToCentralQuot_injective (h : UnitaryFieldData 2 f K) {n : ℕ}
    (ψ : hypSU h r ε ≃* StatedSU n (2 ^ f) K)
    (hZ : (hypScalars h r ε).map ψ.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
    (hc : Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) :
    Function.Injective (hypPSUToCentralQuot h ψ hZ hc) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  rw [hypPSUToCentralQuot_hypProj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hc,
    ← hZ] at hx
  obtain ⟨z, hz, hzg⟩ := hx
  have : z = g := ψ.injective hzg
  subst this
  rw [← ker_hypProj] at hz
  exact hz

theorem cyclic_hypProj_of_cyclic_centralQuot (h : UnitaryFieldData 2 f K) {n : ℕ}
    (ψ : hypSU h r ε ≃* StatedSU n (2 ^ f) K)
    (hZ : (hypScalars h r ε).map ψ.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
    (hc : Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
    (I : Set ℕ) {J : Subgroup (StatedSU n (2 ^ f) K)}
    (hJ : J = (flagStabilizer h r ε I).map ψ.toMonoidHom)
    (hcyc : ∀ V : Subgroup (StatedSU n (2 ^ f) K), V ≤ J → ⁅V, V⁆ = V →
      ∀ A : Subgroup (StatedSU n (2 ^ f) K), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center (StatedSU n (2 ^ f) K))))) :
    ∀ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I → ⁅V, V⁆ = V →
      ∀ A : Subgroup (hypSU h r ε), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (hypProj h r ε)) := by
  intro V hV hVp A hAV hA
  have h1 := hcyc (V.map ψ.toMonoidHom) (hJ ▸ Subgroup.map_mono hV)
    (by rw [← Subgroup.map_commutator, hVp]) (A.map ψ.toMonoidHom) (Subgroup.map_mono hAV)
    (hA.map ψ.toMonoidHom)
  have hinj := hypPSUToCentralQuot_injective h ψ hZ hc
  have h2 : (A.map (hypProj h r ε)).map (hypPSUToCentralQuot h ψ hZ hc) =
      (A.map ψ.toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center (StatedSU n (2 ^ f) K))) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  exact (Subgroup.equivMapOfInjective (A.map (hypProj h r ε)) _ hinj).isCyclic.mpr (h2 ▸ h1)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
