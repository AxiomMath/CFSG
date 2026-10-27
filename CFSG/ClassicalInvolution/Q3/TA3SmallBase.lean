module

public import CFSG.ClassicalInvolution.Q3.TA3SmallDescent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

theorem smallList (hGH : GH74SectionalModels) (F : Type) [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) (hP : TwoSubgroupsFourGenerated F) :
    SmallFamily F ∨ Nobq.ExcludedSmall F := by
  by_cases h3 : 3 ≤ CFSG.Open.twoRank F
  · rcases hGH F hnab h3 hP with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, hf, hm, h⟩ |
      ⟨p, f, hp, hf, hm, h⟩ | h | ⟨n, hn1, hn2, he⟩ | h
    · have : SmallG2 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallD4 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallPSp4 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallTwistedG2 F := ⟨f, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallL4 F := ⟨p, f, hp, hp2, hf, hm, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallU4 F := ⟨p, f, hp, hp2, hf, hm, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallL5 F := ⟨p, f, hp, ne_two_of_pow_mod_four hf (Or.inl hm), hf, hm, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallU5 F := ⟨p, f, hp, ne_two_of_pow_mod_four hf (Or.inr hm), hf, hm, h⟩
      left; unfold SmallFamily; tauto
    · right; unfold Nobq.ExcludedSmall; tauto
    · right
      unfold Nobq.ExcludedSmall
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn1, hn2, he⟩))))))
    · rcases h with h | h | h | h | h | h | h | h
      · have : SmallM12 F := h
        left; unfold SmallFamily; tauto
      all_goals right; unfold Nobq.ExcludedSmall; tauto
  · have h2 : CFSG.Open.twoRank F ≤ 2 := by omega
    have heven : Even (Nat.card F) := by
      by_contra hodd
      have := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := F) (Nat.not_even_iff_odd.mp hodd)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
    have h2' : CFSG.Open.twoRank F = 2 :=
      le_antisymm h2 (CFSG.Assembly.LowTwoRank.two_le_twoRank F hnab heven)
    rcases CFSG.Milestones.lr_rank_two_isomorphism_types F hnab h2' with
      ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h
    · have : SmallL2 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallL3 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · have : SmallU3 F := ⟨p, f, hp, hp2, hf, h⟩
      left; unfold SmallFamily; tauto
    · right; unfold Nobq.ExcludedSmall; tauto
    · right; unfold Nobq.ExcludedSmall; tauto
    · have : SmallM11 F := isSporadic_m11_of_nonempty_mulEquiv_statedM11 h
      left; unfold SmallFamily; tauto


theorem smallSimple_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeaves) (Y : Type)
    [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)] (hA : CIT3Below (Nat.card Y))
    (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    (hP : TwoSubgroupsFourGenerated (genFittingFStar Y)) (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) :
    TightEx Y R S t ∨ GoodThreeElement R t := by
  rcases smallList hGH _ hnab hP with
    (h | h | h | h | h | h | h | h | h | h | h | h | h) | hex
  · exact hL.g2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.d4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.psp4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.twistedG2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l5 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u5 Y hA hnab hP h R S t hd hc hE2
  · exact hL.m12 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l3 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u3 Y hA hnab hP h R S t hd hc hE2
  · exact hL.m11 Y hA hnab hP h R S t hd hc hE2
  · exfalso
    have := genFittingFStar_normal Y
    obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
    exact (Nobq.smallNoDatum_of_dvd Nobq.card_outer_Ly_dvd_two).noDatum _ hex Y
      (genFittingFStar Y) ⟨MulEquiv.refl _⟩ (Nobq.centralizer_genFittingFStar_eq_bot hnab) R S r
      hr ⟨eS⟩ t hd.mem hd.order hd.cent hd.normal

theorem tightSmallBase_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeaves) :
    TightSmallBase := by
  intro Y _ _ hA R S t hd hc hE2 hQ hsmall
  by_cases htw : ∃ c ∈ fstarCenter Y, c ≠ 1 ∧ ∃ y : Y, y * t * y⁻¹ = t * c
  · obtain ⟨c, hcN, hc1, hy⟩ := htw
    exact Or.inr (hL.twin hGH Y hA hQ hsmall R S t hd hc hE2 c hcN hc1 hy)
  have hnt : ∀ y : Y, ∀ n ∈ fstarCenter Y, y * t * y⁻¹ = t * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact htw ⟨n, hn, h1, y, hy⟩
  have hNc := fstarCenter_le_center hd hc hE2
  have hN2 := isPGroup_fstarCenter hc
  have htN := not_mem_fstarCenter hc hE2
  have hF := genFittingFStar_quotient_fstarCenter Y hQ hNc
  have := isSimpleGroup_fstarBar Y hQ
  have : IsSimpleGroup ↥(genFittingFStar (Y ⧸ fstarCenter Y)) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hnab : ∃ a b : genFittingFStar (Y ⧸ fstarCenter Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_comm_fstarBar Y hQ
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => ?_⟩
    exact hab (by simpa using congrArg (MulEquiv.subgroupCongr hF) h)
  have hP : TwoSubgroupsFourGenerated (genFittingFStar (Y ⧸ fstarCenter Y)) :=
    twoSubgroupsFourGenerated_of_mulEquiv (MulEquiv.subgroupCongr hF).symm
      (twoSubgroupsFourGenerated_fstarBar Y hsmall)
  have hA' : CIT3Below (Nat.card (Y ⧸ fstarCenter Y)) := fun Y' _ _ hY' Λ hΛ =>
    hA Y' (lt_of_lt_of_le hY'
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _))) Λ hΛ
  exact tightExOrGood_of_quotient hd hc hE2 hnt
    (smallSimple_of_leaves hGH hL (Y ⧸ fstarCenter Y) hA' hnab hP _ _ _
      (TwistQ.datum hd hN2 htN hnt) (TwistQ.cls hd hNc hN2 htN hc)
      fun h => hE2 (TwistQ.inO2_of hN2 h))

end CFSG.ClassicalInvolution.Q3.TA3
