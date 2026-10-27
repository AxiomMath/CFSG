module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section ZEq

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem false_of_ZLeq1_noncentral (hc : centerOf L = ⊥) {a : G} (haT : a ∈ T)
    (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g z : G} (hz : z ∈ lin2Z L (thompsonJ S))
    (hg : a = g⁻¹ * z * g)
    (hnc : ¬ ∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a) : False := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hZR : Z = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := Z) rfl).resolve_right fun h => h.1 hc).2
  have ha1 : a ≠ 1 := fun h => haR (by rw [h]; exact one_mem _)
  have haZg : a ∈ conjR Z g := mem_conjR_iff'.2 ⟨z, hz, hg⟩
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hnab : ¬ ∀ i ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G),
      ∀ j ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G), i * j = j * i := by
    by_cases haS : a ∈ S
    · exact E.not_commutative_of_mem_S hcfg hc
        (lt_of_le_of_ne (thompsonJ_le_self S) (fun h => haR (by rw [h]; exact haS))) haS haR ha2
    · have hsq : a ^ 2 ∈ thompsonJ S := by rw [ha2]; exact one_mem _
      obtain ⟨-, -, h14'⟩ := E.h14 G T M H S L D n hcfg a haT haS hsq
      rcases h14' ha2 with ⟨-, hZeq, -⟩ | ⟨-, hev, hcard, hΩ⟩ | ⟨hc', -⟩
      · exfalso
        apply hnc
        intro y hy
        have hy' : y ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G) := by
          rw [← hZeq, ← hZR]; exact hy
        exact (Subgroup.mem_centralizer_singleton_iff.1 hy'.2).symm
      · obtain ⟨m, hm⟩ := hev
        refine E.not_commutative_of_card_omegaOne hcfg
          (I := thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G)) inf_le_left (m := m)
          (by have := hcfg.one_lt; omega) ?_ ?_
        · rw [hcard]; congr 1; omega
        · rw [hΩ]; congr 1; omega
      · exact absurd hc hc'
  push Not at hnab
  obtain ⟨i, hi, j, hj, hij⟩ := hnab
  have hw1 : ⁅i, j⁆ ≠ 1 := fun h => hij (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hwmem := E.commutator_inf_centralizer_le hcfg a (Subgroup.commutator_mem_commutator hi hj)
  have hwZ : ⁅i, j⁆ ∈ Z := by rw [hZR]; exact hwmem.1
  have hI2 : IsPGroup 2 ↥(thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G)) :=
    hcfg.sylowT.isPGroup.to_le (inf_le_left.trans hRT)
  have hconj : conjR Z g ≤ Subgroup.centralizer ({⁅i, j⁆} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (E.commutator_centralizes_conjR_Z hcfg hc hZdef haZg ha1 inf_le_right hI2 hi hj hy).symm
  have hcomm := commute_of_centralizes_TI tiAbelianTwoGroupCommute (E.Zbasic hcfg hZdef).1
    (E.ZTI hcfg hZdef) hwZ hw1 hconj
  apply hnc
  intro y hy
  have h1 := Subgroup.commutator_mem_commutator haZg hy
  rw [hcomm, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem false_of_ZLeq1 (hLQ : Lemma2421LQ) (hc : centerOf L = ⊥) {a : G} (haT : a ∈ T)
    (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g z : G} (hz : z ∈ lin2Z L (thompsonJ S))
    (hz1 : z ≠ 1) (hg : a = g⁻¹ * z * g) : False := by
  by_cases hnc : ∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a
  ·
    by_cases haS : a ∈ S
    · exfalso
      have hRlt : thompsonJ S < S :=
        lt_of_le_of_ne (thompsonJ_le_self S) (fun h => haR (by rw [h]; exact haS))
      have hcard := E.card_Z_inf_centralizer hcfg hRlt (Z := lin2Z L (thompsonJ S)) rfl haS haR ha2
      have hle : lin2Z L (thompsonJ S) ≤
          lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
        ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 (hnc y hy).symm⟩
      have h1 := Subgroup.card_le_of_le hle
      have h2 := (E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl).2.1
      rw [hcard, h2] at h1
      have hn := hcfg.one_lt
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show n / 2 < n by omega)
      omega
    · exact hLQ G T M H S L D n hcfg hc a haT haS ha2 hnc g z hz hz1 hg
  · exact E.false_of_ZLeq1_noncentral hcfg hc haT haR ha2 hz hg hnc

end ZEq

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
