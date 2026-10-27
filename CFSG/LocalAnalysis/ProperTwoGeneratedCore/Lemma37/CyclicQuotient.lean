module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase

open CFSG.Open

variable {K Q : Type*} [Group K] [Group Q]

theorem card_le_two_of_isElemAbelian_of_isCyclic {E : Subgroup Q} (hE : IsElemAbelian 2 E)
    (hc : IsCyclic E) : Nat.card E ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd (by norm_num) (Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (hE.2 g g.2))

theorem isCyclic_map_of_isCyclic (f : K →* Q) {P : Subgroup K} (hP : IsCyclic P) :
    IsCyclic (P.map f) :=
  isCyclic_of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)

theorem isPGroup_of_isElemAbelian {E : Subgroup Q} (hE : IsElemAbelian 2 E) : IsPGroup 2 E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

variable [Finite Q]

theorem pRank_inf_conjBy_le_one_of_cyclic (π : K →* Q) (hπ : Function.Surjective π)
    {B : Subgroup K} (hker : π.ker ≤ B) (hker2 : IsPGroup 2 π.ker)
    (hcyc : ∀ g : K, g ∉ B → ∀ P : Subgroup K, IsPGroup 2 P →
      (∀ p ∈ P, p ∈ B ∧ g⁻¹ * p * g ∈ B) → IsCyclic P)
    (g : Q) (hg : g ∉ B.map π) :
    CFSG.Open.pRank 2 (B.map π ⊓ (B.map π).conjBy g⁻¹) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨E, hEle, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by decide) (B.map π ⊓ (B.map π).conjBy g⁻¹)
  obtain ⟨h, rfl⟩ := hπ g
  have hB : (B.map π).comap π = B := Subgroup.comap_map_eq_self hker
  have hhB : h⁻¹ ∉ B := fun hh => hg (Subgroup.mem_map_of_mem π (B.inv_mem_iff.mp hh))
  have hP : IsPGroup 2 (E.comap π) := (isPGroup_of_isElemAbelian hE).comap_of_ker_isPGroup π hker2
  have hPc : IsCyclic (E.comap π) := by
    refine hcyc h⁻¹ hhB (E.comap π) hP fun p hp => ⟨?_, ?_⟩
    · rw [← hB]
      exact (hEle hp).1
    · obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.mp (hEle hp).2
      rw [← hB, inv_inv, Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hyp]
      simpa [MulAut.conj_apply, mul_assoc] using hy
  have hEc : IsCyclic E := by
    have h := isCyclic_map_of_isCyclic π hPc
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at h
  have h2 := card_le_two_of_isElemAbelian_of_isCyclic hE hEc
  rw [hEcard] at h2
  have h4 : 2 ^ 2 ≤ 2 ^ CFSG.Open.pRank 2 (B.map π ⊓ (B.map π).conjBy (π h)⁻¹) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem gamma_two_le_map_of_cyclic (π : K →* Q) (hπ : Function.Surjective π)
    {B : Subgroup K} (hker : π.ker ≤ B) (hker2 : IsPGroup 2 π.ker)
    (hcyc : ∀ g : K, g ∉ B → ∀ P : Subgroup K, IsPGroup 2 P →
      (∀ p ∈ P, p ∈ B ∧ g⁻¹ * p * g ∈ B) → IsCyclic P)
    (S : Sylow 2 Q) (hSB : (S : Subgroup Q) ≤ B.map π) :
    properTwoGenCoreGamma (S : Subgroup Q) 2 ≤ B.map π :=
  (two_generated_core_le_iff_intersection_rank_le_one S _ hSB).mpr fun g hg =>
    pRank_inf_conjBy_le_one_of_cyclic π hπ hker hker2 hcyc g hg

omit [Finite Q] in
theorem map_ne_top_of_ker_le (π : K →* Q) {B : Subgroup K} (hker : π.ker ≤ B) (hB : B ≠ ⊤) :
    B.map π ≠ ⊤ := by
  intro htop
  apply hB
  rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]

end CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase
