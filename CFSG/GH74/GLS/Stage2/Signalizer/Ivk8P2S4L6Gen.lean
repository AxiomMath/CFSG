module

import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
import CFSG.GH74.AS16.Standard
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_of_not_le_centralizer {J Z : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Z ≤ normalizer (J : Set G)) (hnc : ¬ Z ≤ centralizer (J : Set G)) : ⁅J, Z⁆ = J := by
  have hperf : Group.IsPerfect ↥J := hq.1
  set L := ⁅J, Z⁆ with hL
  have hLJ : L ≤ J := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ normalizer (J : Set G) := hZ hb
    have h1 := (mem_normalizer_iff.mp hbN a⁻¹).mp (J.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using J.mul_mem ha h1
  have hnorm : ∀ g ∈ J, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg
    have h1 : L ≤ L.comap (MulAut.conj g).toMonoidHom := by
      rw [hL, Subgroup.commutator_le]
      intro a ha b hb
      show g * ⁅a, b⁆ * g⁻¹ ∈ L
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅g, b⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem (Subgroup.commutator_mem_commutator (J.mul_mem hg ha) hb)
        (L.inv_mem (Subgroup.commutator_mem_commutator hg hb))
    intro l hl
    exact h1 hl
  have hLn : (L.subgroupOf J).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ L := hn
    exact hnorm (g : G) g.2 (n : G) hn'⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hLn with htop | hcen
  · exact le_antisymm hLJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    apply hnc
    have := hperf
    intro g hg
    have hgJ : g ∈ centralizer (J : Set G) :=
      P2S3.mem_centralizer_of_comm_central (hZ hg) fun j hj k hk => by
        have hmem : (⟨g * j * g⁻¹ * j⁻¹, by
            have h1 : g * j * g⁻¹ ∈ J := (mem_normalizer_iff.mp (hZ hg) j).mp hj
            exact J.mul_mem h1 (J.inv_mem hj)⟩ : ↥J) ∈ L.subgroupOf J := by
          have h1 : ⁅j, g⁆ ∈ L := Subgroup.commutator_mem_commutator hj hg
          have h2 : ⁅g, j⁆ = ⁅j, g⁆⁻¹ := (commutatorElement_inv j g).symm
          show g * j * g⁻¹ * j⁻¹ ∈ L
          have h3 : g * j * g⁻¹ * j⁻¹ = ⁅g, j⁆ := by simp [commutatorElement_def]
          rw [h3, h2]
          exact L.inv_mem h1
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hmem) ⟨k, hk⟩)
    exact hgJ

theorem normalizer_of_le_comp {H I J : Subgroup G} {c : G} (hI : IsCompIn H I) (hcH : c ∈ H)
    (hJq : IsQuasisimple ↥J) (hJI : J ≤ I) (hcJ : c ∈ normalizer (J : Set G)) :
    c ∈ normalizer (I : Set G) := by
  have hI' := P2S3.isCompIn_map_conj_of_mem hI hcH
  rcases AS16.isCompIn_commute hI hI' with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
  · exfalso
    have hJc : J.map (MulAut.conj c).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hcJ
    have hJI' : J ≤ I.map (MulAut.conj c).toMonoidHom := by
      rw [← hJc]
      exact Subgroup.map_mono hJI
    have hcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
      intro a ha b hb
      have h1 : ⁅a, b⁆ ∈ ⁅I, I.map (MulAut.conj c).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator (hJI ha) (hJI' hb)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hperf : Group.IsPerfect ↥J := hJq.1
    have hbot : J = ⊥ := by
      have h1 : ⁅J, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b hb a ha)
      exact (Subgroup.isPerfect_iff.mp hperf).symm.trans h1
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this hbot

end Gen

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
