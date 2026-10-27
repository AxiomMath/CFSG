module

public import CFSG.LieType.Ree.BorelSelfNormalizers

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem reeFixedBruhatCell_one :
    t.reeFixedBruhatCell K a 1 = (t.reeFixedBorel K a : Set (ModGL t.tag K)) := by
  ext x
  rw [mem_reeFixedBruhatCell, canonicalRep_one]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    rw [mul_one]
    exact mul_mem hb hb'
  · intro hx
    exact ⟨x, hx, 1, one_mem _, by rw [mul_one, mul_one]⟩

theorem height_fixedOrbitElement_smul_neg
    {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.fixedOrbitRoots j) :
    height (t.fixedOrbitElement j • α) < 0 := by
  have h := (mem_fixedOrbitRoots_iff.1 (neg_smul_mem_fixedOrbitRoots hα)).2.1
  rw [height_neg] at h
  omega

theorem canonicalRep_conj_mem_reeFixedNegUnipotent
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) {j : Fin t.fixedOrbitCount}
    (hj : ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) {u : ModGL t.tag K}
    (hu : u ∈ t.reeFixedOrbitUnipotent K a j) :
    canonicalRep (coxeterSystem t.tag) K w * u * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
      t.reeFixedNegUnipotent K a := by
  obtain ⟨hS, hΓ⟩ := Subgroup.mem_inf.1 hu
  have hmap := (canonical_weyl_root_transport t.tag K).1 w (t.fixedOrbitRoots j)
    fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1
  have hS' : canonicalRep (coxeterSystem t.tag) K w * u *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        rootSpan t.tag K ((fun α => w • α) '' t.fixedOrbitRoots j) := by
    rw [← hmap]
    exact ⟨u, hS, rfl⟩
  have hn : canonicalRep (coxeterSystem t.tag) K w ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a hw).2
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hS', mul_mem (mul_mem hn hΓ) (inv_mem hn)⟩
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨IsRoot.smul (mem_fixedOrbitRoots_iff.1 hα).1 w, hj α hα⟩

theorem canonicalRep_fixedOrbitElement_mem_reeGamma_inf
    (j : Fin t.fixedOrbitCount) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :=
  Subgroup.mem_inf.2 ⟨(canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2,
    canonicalRep_mem_parabolicSubgroup (fixedOrbitElement_mem_fixedOrbitWeyl j)⟩

theorem reeFixedBorel_le_reeGamma_inf_parabolicSubgroup
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedBorel K a ≤ t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :=
  le_inf reeFixedBorel_le_reeGamma (inf_le_left.trans (borelGroup_le_parabolicSubgroup _))

theorem coe_reeGamma_inf_parabolicSubgroup
    (j : Fin t.fixedOrbitCount) :
    ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      (t.reeFixedBorel K a : Set (ModGL t.tag K)) ∪
        t.reeFixedBruhatCell K a (t.fixedOrbitElement j) := by
  refine Set.Subset.antisymm (fun g hg => ?_) (Set.union_subset
    (SetLike.coe_subset_coe.2 (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j))
    fun g hg => ?_)
  · obtain ⟨hgΓ, hgP⟩ := Subgroup.mem_inf.1 hg
    have hgΓ' : g ∈ (t.reeGamma K a : Set (ModGL t.tag K)) := hgΓ
    rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hgΓ'
    obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hgΓ'
    have hgP' : g ∈ parabolicCells t.tag K (t.fixedOrbitSet j) := by
      rw [← parabolicSubgroup_eq_parabolicCells]
      exact hgP
    obtain ⟨v, hv, hgv⟩ := mem_parabolicCells.1 hgP'
    have hwv : w = v := by
      by_contra h
      exact Set.disjoint_left.1 (disjoint_bruhatCell h)
        (reeFixedBruhatCell_subset_bruhatCell w hgw) hgv
    have hwj : w ∈ (t.fixedOrbitWeyl j : Set (WeylGroup t.tag)) ∩ t.relWeylRee :=
      ⟨hwv ▸ hv, hw⟩
    rw [fixedOrbitWeyl_inter_relWeylRee] at hwj
    rcases hwj with rfl | hwj
    · left
      rw [← reeFixedBruhatCell_one]
      exact hgw
    · obtain rfl := Set.mem_singleton_iff.1 hwj
      exact Or.inr hgw
  · exact Subgroup.mem_inf.2 ⟨reeFixedBruhatCell_subset (fixedOrbitElement_mem j) hg,
      bruhatCell_subset_parabolicSubgroup (fixedOrbitElement_mem_fixedOrbitWeyl j)
        (reeFixedBruhatCell_subset_bruhatCell _ hg)⟩

theorem disjoint_reeFixedBorel_reeFixedBruhatCell
    (j : Fin t.fixedOrbitCount) :
    Disjoint (t.reeFixedBorel K a : Set (ModGL t.tag K))
      (t.reeFixedBruhatCell K a (t.fixedOrbitElement j)) := by
  rw [← reeFixedBruhatCell_one]
  exact disjoint_reeFixedBruhatCell (fixedOrbitElement_ne_one j).symm

theorem not_normal_reeFixedBorel_subgroupOf
    (j : Fin t.fixedOrbitCount) :
    ¬((t.reeFixedBorel K a).subgroupOf
      (t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j))).Normal := by
  intro hN
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  have huB : u ∈ t.reeFixedBorel K a :=
    reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu)
  have hc : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ t.reeFixedBorel K a :=
    Subgroup.mem_subgroupOf.1 (hN.conj_mem
      ⟨u, reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j huB⟩
      (Subgroup.mem_subgroupOf.2 huB) ⟨_, canonicalRep_fixedOrbitElement_mem_reeGamma_inf j⟩)
  have hU := canonicalRep_conj_mem_reeFixedNegUnipotent (fixedOrbitElement_mem j)
    (fun _ hα => height_fixedOrbitElement_smul_neg hα) hu
  have h₁ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a := Subgroup.mem_inf.2 ⟨hc, hU⟩
  rw [reeFixedBorel_inf_reeFixedNegUnipotent, Subgroup.mem_bot, mul_inv_eq_one,
    mul_eq_left] at h₁
  exact hu1 h₁

theorem ree_fixed_two_cell_parabolics
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (j : Fin t.fixedOrbitCount) :
    ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      (t.reeFixedBorel K a : Set (ModGL t.tag K)) ∪
        t.reeFixedBruhatCell K a (t.fixedOrbitElement j) ∧
    Disjoint (t.reeFixedBorel K a : Set (ModGL t.tag K))
      (t.reeFixedBruhatCell K a (t.fixedOrbitElement j)) ∧
    t.reeFixedBorel K a ≤ t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) ∧
    ¬((t.reeFixedBorel K a).subgroupOf
      (t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j))).Normal :=
  ⟨coe_reeGamma_inf_parabolicSubgroup j, disjoint_reeFixedBorel_reeFixedBruhatCell j,
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j, not_normal_reeFixedBorel_subgroupOf j⟩

end ReeTag

end CFSG.LieType.Ree
