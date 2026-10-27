module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section General

variable {A : Type} [Group A]

theorem quasisimple_normal_le_center_or_eq {J N : Subgroup A} (hJ : IsQuasisimple ↥J) (hNJ : N ≤ J)
    (hN : (N.subgroupOf J).Normal) : N ≤ J ⊓ centralizer (J : Set A) ∨ N = J := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hN with h | h
  · exact Or.inr (le_antisymm hNJ (Subgroup.subgroupOf_eq_top.mp h))
  · refine Or.inl (le_inf hNJ fun n hn => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have := Subgroup.mem_center_iff.mp (h (show (⟨n, hNJ hn⟩ : J) ∈ N.subgroupOf J from hn)) ⟨j, hj⟩
    exact congrArg Subtype.val this

theorem comm_eq_bot_of_central {J X : Subgroup A} (hJ : ⁅J, J⁆ = J) (_hXJ : X ≤ normalizer (J : Set A))
    (h : ⁅J, X⁆ ≤ centralizer (J : Set A)) : ⁅J, X⁆ = ⊥ :=
  CFSG.LocalCores.perfect_double_commutator (Subgroup.isPerfect_iff.mpr hJ)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)

theorem exists_comp_comm_ne {X : Subgroup A} (h : ⁅layer A, X⁆ ≠ ⊥) :
    ∃ J : Subgroup A, IsComponent J ∧ ⁅J, X⁆ ≠ ⊥ := by
  by_contra hcon
  refine h (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sSup_le fun J hJ => ?_))
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp (not_not.mp fun hne => hcon ⟨J, hJ, hne⟩)

theorem isComponent_conj {J : Subgroup A} (hJ : IsComponent J) (g : A) :
    IsComponent (J.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ

private theorem mem_map_conj_iff {K : Subgroup A} {g a : A} :
    a ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * a * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

private theorem map_conj_map_conj (K : Subgroup A) (g h : A) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  ext a
  rw [mem_map_conj_iff, mem_map_conj_iff, mem_map_conj_iff]
  have : (g * h)⁻¹ * a * (g * h) = h⁻¹ * (g⁻¹ * a * g) * h := by group
  rw [this]

private theorem mem_normalizer_of_map_conj_eq {K : Subgroup A} {g : A}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have h1 := Subgroup.ext_iff.mp h (g * a * g⁻¹)
  rw [mem_map_conj_iff] at h1
  have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  rw [this] at h1
  exact h1

theorem X_le_normalizer_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup A} (hXp : IsPGroup p ↥X)
    (hJ : IsComponent J)
    (h3 : ∀ J₁ J₂ J₃ : Subgroup A, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ → J₁ ≠ J₂ → J₁ ≠ J₃ →
      J₂ ≠ J₃ → False) : X ≤ normalizer (J : Set A) := by
  intro x hx
  have hsq : x * x ∈ normalizer (J : Set A) := by
    refine mem_normalizer_of_map_conj_eq ?_
    rw [← map_conj_map_conj]
    by_cases h1 : J.map (MulAut.conj x).toMonoidHom = J
    · rw [h1, h1]
    · by_contra h2
      refine h3 J (J.map (MulAut.conj x).toMonoidHom)
        ((J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom) hJ
        (isComponent_conj hJ x) (isComponent_conj (isComponent_conj hJ x) x) (Ne.symm h1)
        (Ne.symm h2) fun h => h1 ?_
      exact Subgroup.map_injective (MulAut.conj x).injective h.symm
  obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  have hxm : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm, hk', one_mul]
  rw [hxm]
  exact Subgroup.pow_mem _ (by rw [pow_two]; exact hsq) _

end General

section Finite

variable {A : Type} [Group A] [Finite A]

theorem quasisimple_odd_normal_le_center {J N : Subgroup A} (hJ : IsQuasisimple ↥J) (hNJ : N ≤ J)
    (hN : (N.subgroupOf J).Normal) (hodd : Odd (Nat.card ↥N)) : N ≤ centralizer (J : Set A) := by
  rcases quasisimple_normal_le_center_or_eq hJ hNJ hN with h | rfl
  · exact h.trans inf_le_right
  · exfalso
    have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial ↥N := CFSG.LocalCores.isQuasisimple_nontrivial hJ
    have : Group.IsPerfect ↥N := hJ.1
    exact Group.IsPerfect.not_isSolvable ↥N hsolv

theorem comp_le_or_comm {K J : Subgroup A} [K.Normal] (hJ : IsComponent J) : J ≤ K ∨ ⁅J, K⁆ = ⊥ :=
  CFSG.LocalCores.component_normal_subgroup hJ inferInstance

theorem comp_comm_of_ne {J₁ J₂ : Subgroup A} (h₁ : IsComponent J₁) (h₂ : IsComponent J₂) (hne : J₁ ≠ J₂) :
    ⁅J₁, J₂⁆ = ⊥ :=
  (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne

theorem comp_le_ncl {X J : Subgroup A} (hJ : IsComponent J) (h : ⁅J, X⁆ ≠ ⊥) : J ≤ ncl X := by
  have : (ncl X).Normal := Subgroup.normalClosure_normal
  rcases comp_le_or_comm (K := ncl X) hJ with h1 | h1
  · exact h1
  · exact absurd (le_bot_iff.mp (h1 ▸ Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure)) h

end Finite

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
