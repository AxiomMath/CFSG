module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionPerfectOdd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_map_oddCore_of_conj_eq_mul (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) (htX : t ∈ centralizer (X : Set G))
    (hDX : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))
    (hZD : Odd (Nat.card (center
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))))
    (hOutD : Group.IsSolvable (Outer
      ((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) ⧸
        center (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
          L.subtype))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map
          e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hDt : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans (le_centralizer_of_mem_centralizer htK.1)
  obtain ⟨-, y₁, hy₁D, hy₁, -, P, hP, hPD⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul hset hOut hq hn e ht hKt hab hXodd hXJ hyD hy hg
  exact not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center htX ht hDX hDq hZD hOutD hDt
    hsyl hy₁D hy₁ (Or.inr rfl) hP hPD

end CFSG.SeitzReduction.LinearPilot
