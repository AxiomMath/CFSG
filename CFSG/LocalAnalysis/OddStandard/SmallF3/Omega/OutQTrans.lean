module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem aor_isSubnormal_subgroupOf_restrict {K M E : Subgroup G} (hEM : E ≤ M)
    (h : (K.subgroupOf M).IsSubnormal) : (K.subgroupOf E).IsSubnormal := by
  have hEq : (K.subgroupOf M).comap (Subgroup.inclusion hEM) = K.subgroupOf E := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← hEq]
  exact h.comap _

private theorem aor_isSubnormal_subgroupOf_trans {A B C : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).IsSubnormal) (hB : (B.subgroupOf C).IsSubnormal) :
    (A.subgroupOf C).IsSubnormal := by
  let ψ : (B.subgroupOf C) →* B :=
    { toFun := fun x => ⟨((x : C) : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hA' : ((A.subgroupOf C).subgroupOf (B.subgroupOf C)).IsSubnormal := by
    convert hA.comap ψ using 1
    ext x
    exact Iff.rfl
  exact Subgroup.IsSubnormal.trans (fun x hx => hAB hx) hA' hB

theorem aor_subnormal_pair {A B M X K : Subgroup G} (hXA : X ≤ A) (hKX : K ≤ X) (hKM : K ≤ M)
    (hMA : M ≤ A) (hXM : X ⊓ M = X ⊓ B) (hX : (X.subgroupOf A).IsSubnormal)
    (hK : (K.subgroupOf M).IsSubnormal) : (K.subgroupOf (A ⊓ B)).IsSubnormal := by
  have hKE : K ≤ X ⊓ B := by
    intro x hx
    rw [← hXM]
    exact ⟨hKX hx, hKM hx⟩
  have hEM : X ⊓ B ≤ M := by
    intro x hx
    rw [← hXM] at hx
    exact hx.2
  have hKEsn : (K.subgroupOf (X ⊓ B)).IsSubnormal :=
    aor_isSubnormal_subgroupOf_restrict hEM hK
  have hXAB : (X.subgroupOf (A ⊓ B)).IsSubnormal :=
    aor_isSubnormal_subgroupOf_restrict (inf_le_left : A ⊓ B ≤ A) hX
  have hEABsn : ((X ⊓ B).subgroupOf (A ⊓ B)).IsSubnormal := by
    have hEq : X.subgroupOf (A ⊓ B) = (X ⊓ B).subgroupOf (A ⊓ B) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨hx, x.2.2⟩, fun hx => hx.1⟩
    rwa [hEq] at hXAB
  exact aor_isSubnormal_subgroupOf_trans hKE hKEsn hEABsn

theorem aor_subnormal_subgroupOf_subgroupOf {B D K : Subgroup G} (hDB : D ≤ B) (hKD : K ≤ D)
    (h : (K.subgroupOf D).IsSubnormal) :
    ((K.subgroupOf B).subgroupOf (D.subgroupOf B)).IsSubnormal := by
  let φ : ↥(D.subgroupOf B) →* ↥D :=
    { toFun := fun x => ⟨((x : B) : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hEq : (K.subgroupOf D).comap φ = (K.subgroupOf B).subgroupOf (D.subgroupOf B) := by
    ext x
    exact Iff.rfl
  rw [← hEq]
  exact h.comap φ

theorem aor_centralizer_pair_subgroupOf (y : G) (s : ↥(centralizer ({y} : Set G))) :
    (centralizer ({(s : G), y} : Set G)).subgroupOf (centralizer ({y} : Set G)) =
      centralizer ({s} : Set ↥(centralizer ({y} : Set G))) := by
  ext ⟨g, hg⟩
  have hyg : y * g = g * y := mem_centralizer_iff.mp hg y (Set.mem_singleton y)
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subtype.ext (h (s : G) (Set.mem_insert _ _))
  · intro h x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact congrArg Subtype.val (h s (Set.mem_singleton s))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hyg

theorem aor_exists_hom_of_isSL23Mod {Q : Type} [Group Q] [Finite Q] (h : IsSL23Mod Q) :
    ∃ χ : Q →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker) := by
  obtain ⟨e⟩ := h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore Q)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore Q))).ker =
      CFSG.oddCore Q := by
    ext n
    change e (QuotientGroup.mk' (CFSG.oddCore Q) n) = 1 ↔ n ∈ CFSG.oddCore Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff n
  rw [hker]
  have hEq : CFSG.oddCore Q = CFSG.pPrimeCore 2 Q := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
  rw [hEq]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := Q))

theorem aor_exists_hom_of_mulEquiv {Q R : Type} [Group Q] [Group R] (e : R ≃* Q)
    (h : ∃ χ : Q →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker)) :
    ∃ χ : R →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker) := by
  obtain ⟨χ, hs, hodd⟩ := h
  refine ⟨χ.comp (e : R →* Q), hs.comp e.surjective, ?_⟩
  have hcard : Nat.card ((χ.comp (e : R →* Q)).ker) = Nat.card χ.ker := by
    rw [MonoidHom.ker_comp_mulEquiv]
    exact Subgroup.card_mapSubgroup (H := χ.ker) e.symm
  rwa [hcard]

end CFSG.OddStandard.SmallF3.Omega
