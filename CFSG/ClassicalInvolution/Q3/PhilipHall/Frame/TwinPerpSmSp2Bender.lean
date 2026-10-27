module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp2Pair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.GH74.Uniqueness.Bender

namespace SP2

theorem commute_of_benderType {G : Type*} [Group G] [Finite G]
    {F : Subgroup G} {m i e : ℕ} (hB : BenderType ↥F m i e) :
    ∀ H : Subgroup G, H ≤ F → IsPGroup 2 ↥H → ∀ w ∈ H, w * w = 1 → ∀ g ∈ H,
      w * g = g * w := by
  intro H hHF hH w hw hw2 g hg
  have hH' : IsPGroup 2 ↥(H.subgroupOf F) := hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHF).symm
  obtain ⟨Q₀, hQ₀⟩ := hH'.exists_le_sylow
  obtain ⟨s, hc⟩ := hB.exists_benderCore Q₀
  by_cases hw1 : w = 1
  · rw [hw1, one_mul, mul_one]
  have hwQ : (⟨w, hHF hw⟩ : ↥F) ∈ (Q₀ : Subgroup ↥F) := hQ₀ (Subgroup.mem_subgroupOf.mpr hw)
  have hgQ : (⟨g, hHF hg⟩ : ↥F) ∈ (Q₀ : Subgroup ↥F) := hQ₀ (Subgroup.mem_subgroupOf.mpr hg)
  have hord : orderOf (⟨w, hHF hw⟩ : ↥F) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext hw2
    · intro h1
      exact hw1 (congrArg Subtype.val h1)
  have hz := hc.center_of_involution _ (le_borel _ hwQ) hord
  have hcent := (Subgroup.mem_inf.mp hz).2
  have h1 := Subgroup.mem_centralizer_iff.mp hcent _ hgQ
  exact (congrArg Subtype.val h1).symm

theorem outTwoCyclic_of_benderType {K : Type} [Group K] [Finite K]
    {m i e : ℕ} (hB : BenderType K m i e) : Nobq.OutTwoCyclic K := by
  intro P hP
  obtain ⟨S₀, hS₀⟩ := hP.exists_le_sylow
  haveI := hB.isCyclic_sylow_outer S₀
  exact Nobq.isCyclic_of_injective_hom (Subgroup.inclusion hS₀) (Subgroup.inclusion_injective hS₀)

set_option linter.unusedSectionVars false


theorem false_of_benderType {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypS n Y R S t) {m i e : ℕ}
    (hB : BenderType ↥(genFittingFStar Y) m i e) : False := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  exact false_of_perp_central h
    (Nobq.isCyclic_of_outTwoCyclic _ hC (outTwoCyclic_of_benderType hB))
    (commute_of_benderType hB)

end SP2

set_option linter.unusedSectionVars false


theorem leaf_sz8 {n : ℕ} : NoTwinS n fun F _ => LieModel F .twistedB2 0 2 3 := by
  intro Y _ _ R S t h _ hF
  rcases hF with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, ha, L, _, _, hf, hcard, ⟨e⟩⟩ := hS
    have hK : Nat.card L = 2 ^ (2 * a + 1) := by
      rw [← hf]
      exact hcard
    let e' : ↥(genFittingFStar Y) ≃* ↥(CFSG.Theory.Comparator.SzModel a) :=
      (e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
        (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm)
    exact SP2.false_of_benderType h (BenderType.suzuki a ha e')

theorem leaf_u34 {n : ℕ} :
    NoTwinS n fun F _ => CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2 := by
  intro Y _ _ R S t h _ hF
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff _ 2 le_rfl).1 hF
  exact SP2.false_of_benderType h (BenderType.unitary 2 le_rfl e)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
