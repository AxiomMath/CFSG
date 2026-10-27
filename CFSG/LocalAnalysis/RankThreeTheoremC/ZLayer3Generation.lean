module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X]

theorem le_rankThreeAschCore_of_generation {P : Sylow 3 X} {K Y : Subgroup X} (hKY : K ≤ Y)
    (hPY : (P : Subgroup X) ≤ Y) {z : X} (hz3 : orderOf z = 3) (hzP : z ∈ (P : Subgroup X))
    (hzc : ∀ g ∈ (P : Subgroup X), z * g = g * z) (hzK : ∀ k ∈ K, z * k = k * z)
    {A : Subgroup ↥Y} (hAR : A ≤ (P : Subgroup X).subgroupOf Y)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA3 : 3 ≤ CFSG.Open.pRank 3 A)
    (hgen : closure {k : ↥(K.subgroupOf Y) | ∃ f ∈ A,
      f ∉ centralizer ((K.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ∧
        f * (k : ↥Y) * f⁻¹ = (k : ↥Y)} = ⊤) :
    K ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  have hA₀P : A.map Y.subtype ≤ (P : Subgroup X) :=
    (Subgroup.map_mono hAR).trans (map_subgroupOf_eq_of_le hPY).le
  have hA₀e : CFSG.Open.IsElemAbelian 3 (A.map Y.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hA Y.subtype
  have hA₀3 : 3 ≤ CFSG.Open.pRank 3 (A.map Y.subtype) :=
    hA3.trans (CFSG.SectionRank.pRank_le_map (by norm_num) Y.subtype Y.subtype_injective A)
  let g : ↥(K.subgroupOf Y) →* X := Y.subtype.comp (K.subgroupOf Y).subtype
  have htop : (⊤ : Subgroup ↥(K.subgroupOf Y)) ≤
      (rankThreeAschCore 2 3 (P : Subgroup X)).comap g := by
    refine hgen.symm.le.trans ((closure_le _).2 ?_)
    rintro k ⟨f, hfA, hfc, hfk⟩
    have hfz : ((f : ↥Y) : X) ∉ zpowers z := by
      intro hf
      refine hfc (mem_centralizer_iff.2 fun h hh => ?_)
      have hhK : (h : X) ∈ K := Subgroup.mem_subgroupOf.1 hh
      have hcomm : Commute ((f : ↥Y) : X) (h : X) := by
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hf
        rw [← hn]
        exact Commute.zpow_left (show Commute z (h : X) from hzK _ hhK) n
      exact Subtype.ext hcomm.symm.eq
    have hfk' : f * (k : ↥Y) = (k : ↥Y) * f :=
      calc f * (k : ↥Y) = f * (k : ↥Y) * f⁻¹ * f := (inv_mul_cancel_right _ _).symm
        _ = (k : ↥Y) * f := by rw [hfk]
    exact mem_rankThreeAschCore_of_commute hA₀P hA₀e hA₀3 hzP hzc hz3 ⟨f, hfA, rfl⟩ hfz
      (hzK _ (Subgroup.mem_subgroupOf.1 k.2)) (congrArg Subtype.val hfk')
  intro k hk
  exact htop (Subgroup.mem_top ⟨⟨k, hKY hk⟩, Subgroup.mem_subgroupOf.2 hk⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
