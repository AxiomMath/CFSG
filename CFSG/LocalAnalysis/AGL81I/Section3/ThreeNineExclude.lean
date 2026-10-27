module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSetup
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.GroupTheory.SupCommute
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)

local notation "pRank" => CFSG.Open.pRank

open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem normalizer_inf_le_normalizer_of_eq_sup {K Q : Subgroup X}
    (hQ : Q = (Q ⊓ K) ⊔ (Q ⊓ Subgroup.centralizer (K : Set X))) :
    Subgroup.normalizer (Q ⊓ K : Set X) ⊓ K ≤ Subgroup.normalizer (Q : Set X) := by
  have key : ∀ h ∈ K, h ∈ Subgroup.normalizer (Q ⊓ K : Set X) →
      Q.map (MulAut.conj h).toMonoidHom ≤ Q := by
    intro h hhK hhN q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    have hq₀' : q₀ ∈ ((Q ⊓ K) ⊔ (Q ⊓ Subgroup.centralizer (K : Set X))) := by
      rw [← hQ]; exact hq₀
    have hcomm : ∀ s ∈ Q ⊓ K, ∀ c ∈ Q ⊓ Subgroup.centralizer (K : Set X), Commute s c := by
      intro s hs c hc
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 s (Subgroup.mem_inf.mp hs).2
    obtain ⟨s, hs, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hq₀'
    have hsQ : s ∈ Q := (Subgroup.mem_inf.mp hs).1
    have hsK : s ∈ K := (Subgroup.mem_inf.mp hs).2
    have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hc).1
    have hcC : c ∈ Subgroup.centralizer (K : Set X) := (Subgroup.mem_inf.mp hc).2
    have hconjS : h * s * h⁻¹ ∈ Q ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp hhN s).mp hs
    have hcomm : h * c = c * h :=
      Subgroup.mem_centralizer_iff.mp hcC h hhK
    have hconjC : h * c * h⁻¹ = c := by
      calc h * c * h⁻¹ = (c * h) * h⁻¹ := by rw [hcomm]
        _ = c := by group
    have hsc : h * (s * c) * h⁻¹ = (h * s * h⁻¹) * c := by
      calc h * (s * c) * h⁻¹ = (h * s * h⁻¹) * (h * c * h⁻¹) := by group
        _ = (h * s * h⁻¹) * c := by rw [hconjC]
    have hmem : h * (s * c) * h⁻¹ ∈ Q := by
      rw [hsc]
      exact Q.mul_mem hconjS.1 hcQ
    simpa [MulAut.conj_apply] using hmem
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgK⟩ := hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key g hgK hgN) ?_
  intro q hq
  have hgKinv : g⁻¹ ∈ K := K.inv_mem hgK
  have hgNinv : g⁻¹ ∈ Subgroup.normalizer (Q ⊓ K : Set X) :=
    (Subgroup.normalizer (Q ⊓ K : Set X)).inv_mem hgN
  refine ⟨g⁻¹ * q * g, ?_, ?_⟩
  · have hmem := key g⁻¹ hgKinv hgNinv
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hq)
    simpa [MulAut.conj_apply] using hmem
  · simp [MulAut.conj_apply]
    group

end CFSG.LocalAnalysis.AGL81I.Section3
