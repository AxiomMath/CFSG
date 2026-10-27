module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec76_caseA [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z)
    (hc : IsConj t (t * z)) {x : G} (hx : x ∈ S ⊓ centralizer (L : Set G))
    (hx4 : orderOf x = 4) : False := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff_inv_mul.mp hc
  have hctxg : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hctx.conjugate g
  have hLP : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hctx.isOm6P g
  have ht : t * z = z * t := hctx.central t hctx.t_mem_S
  have htz : z * (t * z) = (t * z) * z := by
    calc z * (t * z) = (z * t) * z := by group
      _ = (t * z) * z := by rw [← ht]
  have hzC : z ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [hg, Subgroup.mem_centralizer_singleton_iff]
    exact htz
  have hzN : z ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hctxg.cent_le_normalizer h36 z hzC
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hdisj : InducesTypeSome (CFSG.conjugate L g) z 6 1 4 1 ∨
      InducesTypeSome (CFSG.conjugate L g) z 6 1 2 (-1) ∨
      (∃ α : ℤˣ, InducesTypeSome (CFSG.conjugate L g) z 6 1 1 α) ∨
      (∃ α : ℤˣ, InducesTypeSome (CFSG.conjugate L g) z 6 1 3 α) ∨
      InducesOutsideGStar (CFSG.conjugate L g) 6 1 z := by
    rcases sec7_lemma73_sym h73 hctx g (IsConj.refl z) hzC with h3 | h4
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inl h4
  have hz_notC : z ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hP.nontrivial G (CFSG.conjugate L g) hLP z hz2 hzN hdisj
  have hx4pow : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hx2 : x * x = t := sec76_sq_eq_t h72 hctx hx hx4
  have hsC : g⁻¹ * t * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    mem_centralizer_conjugate hctx.t_mem_centralizer g
  have ht_notC : t ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    intro htC
    apply hz_notC
    have hmem := (centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)).mul_mem
      (inv_mem htC) hsC
    rw [hg] at hmem
    have h2 : t⁻¹ * (t * z) = z := by group
    rwa [h2] at hmem
  have hx2_notC : x ^ 2 ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [pow_two, hx2]
    exact ht_notC
  have hLH : CFSG.conjugate L g ≤ centralizer ({t * z} : Set G) := by
    rw [← hg]
    exact hctxg.le_centralizer
  have hHN : centralizer ({t * z} : Set G) ≤
      normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [← hg]
    exact hctxg.cent_le_normalizer h36
  have hSyl : IsSylow2Of S (centralizer ({t * z} : Set G)) := sec76_sylow_cent_tz hctx hg
  have hx4C : x ^ 4 ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [hx4pow]
    exact Subgroup.one_mem _
  have hnorm : ∀ y ∈ S, y⁻¹ * x * y ∈
      zpowers x ⊔ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.mem_sup_left (sec76_conj_mem_zpowers h36 h72 hctx hx hx4 hy)
  exact hP.no_normal_z4 G (CFSG.conjugate L g) hLP (centralizer ({t * z} : Set G)) S
    hLH hHN hSyl x hx.1 hx4C hx2_notC hnorm

end CFSG.OddStandard.SmallF3.Omega
