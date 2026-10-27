module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoord

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem perfect_le_conjugate_of_le_centralizer (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (g : G) {S : Subgroup G} (hS : ⁅S, S⁆ = S)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G)) : S ≤ CFSG.conjugate L g := by
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'def
  have hS' : ⁅S', S'⁆ = S' := by rw [hS'def, ← map_commutator, hS]
  have hS't : S' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (hSt hp)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * p * g⁻¹ * t = g * (p * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * p) * g⁻¹ := by rw [h]
      _ = t * (g * p * g⁻¹) := by group
  have hS'L := CFSG.SeitzReduction.std_perfect_le hset hOut htC ht hS' hS't
  intro p hp
  refine ⟨g * p * g⁻¹, hS'L ⟨p, hp, by simp [MulAut.conj_apply]⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

omit [Finite G] in
theorem le_of_le_sup_of_commute {A B S : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) (hSAB : S ≤ A ⊔ B)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) {z : G} (hzS : z ∈ S) (hzA : z ∈ A)
    (hz1 : z ≠ 1) : S ≤ A := by
  have hBN : B ≤ normalizer (A : Set G) := fun x hx => centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun a ha => (mem_centralizer_iff.1 (hAB ha) x hx).symm)
  have hnorm : (A.subgroupOf S).Normal :=
    normal_subgroupOf_of_le_normalizer (hSAB.trans (sup_le le_normalizer hBN))
  rcases hSsimple _ hnorm with h | h
  · exfalso
    have hmem : (⟨z, hzS⟩ : S) ∈ A.subgroupOf S := mem_subgroupOf.2 hzA
    rw [h, mem_bot] at hmem
    exact hz1 (congrArg Subtype.val hmem)
  · intro x hx
    have hmem : (⟨x, hx⟩ : S) ∈ A.subgroupOf S := by
      rw [h]
      exact mem_top _
    exact mem_subgroupOf.1 hmem

variable {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem le_centralizer_blockSL_compl_of_conj_eq_mul (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (xab hab 1) : L) : G)) {S : Subgroup G}
    (hSperf : ⁅S, S⁆ = S) (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSY : S ≤ centralizer (modelToG e (pairTorus (K := K) a b) : Set G))
    (hzS : ((e.symm (xab hab 1) : L) : G) ∈ S) :
    S ≤ centralizer (modelToG e (blockSL ({a, b}ᶜ : Finset (Fin n))) : Set G) := by
  obtain ⟨e', he', -, hB, hcore⟩ :=
    exists_coords_blockScalar hset hOut hq hn hκ e htC ht hab hg
  have hSL' := perfect_le_conjugate_of_le_centralizer hset hOut htC ht g hSperf hSt
  have hScore : S ≤ perfectCore (CFSG.conjugate L g ⊓
      centralizer (modelToG e (pairTorus (K := K) a b) : Set G)) :=
    le_perfectCore_of_perfect (le_inf hSL' hSY) hSperf
  rw [hcore] at hScore
  have hAB : modelToG e' (blockSL (K := K) ({a, b} : Finset (Fin n))) ≤
      centralizer (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) : Set G) := by
    rw [hB]
    refine modelToG_le_centralizer e' fun x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact (commute_blockSL_of_disjoint disjoint_compl_right x hx y hy).eq.symm
  have hzA : ((e.symm (xab hab 1) : L) : G) ∈
      modelToG e' (blockSL (K := K) ({a, b} : Finset (Fin n))) := by
    rw [← he']
    exact symm_mem_modelToG e' (xab_mem_blockSL hab (by simp) (by simp) 1)
  have hz1 : ((e.symm (xab hab 1) : L) : G) ≠ 1 := by
    intro h
    apply proj_transvection_ne_one (K := K) hab one_ne_zero
    apply e.symm.injective
    apply Subtype.ext
    rw [map_one]
    exact h
  exact (le_of_le_sup_of_commute hAB hScore hSsimple hzS hzA hz1).trans hAB

end Core

end CFSG.SeitzReduction.LinearPilot
