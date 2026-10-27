module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stmt5_2_L2Two_of_F4 (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0})
    (hU3 : FactU3Cover) (h515 : Stmt5_1_5_F4) (h510 : Stmt5_1_10_F4) : Stmt5_2_L2Two_F4 := by
  intro G _ _ T M L H B D K₁ n hyp hN hK₁ hKeq hlt hbend
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁
  have hK₁K : K₁ ≤ oTwoUpper H := hlt.le
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  have hMK := hyp.borel_eq hBorel
  obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hlt
  have hK₂ := tc.cK₂
  have hKeq2 := tc.sup
  have hCK := tc.cK
  have hK₁c : K₁ ∈ cComp (oTwoUpper H) := cComp_mem_of_le hK₁ hK₁K hKH
  have hborel := tc.borelOf_le hK₁ hTH
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · have hy' : y ∈ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact hborel hy
    exact hy'.1
  ·
    intro X hXK _ hXodd x hx
    have hxodd : Odd (orderOf x) := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : X)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hXodd this
    refine mem_normalizer_of_odd_of_pair (p := fun Q => Q ∈ cComp (oTwoUpper H)) hK₁c
      (fun P₁ P₂ P₃ h₁ h₂ h₃ => ?_) hxodd fun Q hQ => ?_
    · rcases hCK P₁ h₁ with e₁ | e₁ <;> rcases hCK P₂ h₂ with e₂ | e₂ <;>
        rcases hCK P₃ h₃ with e₃ | e₃ <;>
        first
        | exact Or.inl (e₁.trans e₂.symm)
        | exact Or.inr (Or.inl (e₂.trans e₃.symm))
        | exact Or.inr (Or.inr (e₁.trans e₃.symm))
    · have h1 := cComp_map_mulEquiv (MulAut.conj x) hQ
      rwa [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hXK hx)] at h1
  ·
    intro X hXK hXP
    set Bk := oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)
      with hBk
    have hBkH : Bk ≤ H := inf_le_left.trans hKH
    have hBks : Group.IsSolvable ↥Bk := by
      have hs := ((h515 G T M L H D n h hyp.hStar hN.2.1).2.2 hyp.lieQuot).1
      have hle : Bk ≤ H ⊓ M := by
        rw [← hMK]
        exact le_inf (inf_le_right.trans hKH) inf_le_left
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    have hBkN : Bk ≤ Subgroup.normalizer (K₁ : Set G) := by
      refine inf_le_left.trans ?_
      rw [hKeq2]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ hK₂)
    set P₁ := K₁ ⊔ Bk with hP₁
    have hP₁N : P₁ ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hBkN
    have hcore : perfectCore P₁ = K₁ :=
      le_antisymm (perfectCore_le_of_sup_solvable le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hP₁N) rfl hBks)
        (le_perfectCore_of_perfect le_sup_left hK₁.2.1)
    have hTK₁ : IsSylowTwoOf (T ⊓ K₁) K₁ := A312.isSylowTwoOf_inf_of_subnormal hK₁.2.2.1 hTH
    have hOK₁ : pCoreOf 2 K₁ ≤ T ⊓ K₁ := F7.isSylowTwoOf_pCoreOf_le hTK₁
    have hTK₁Bk : T ⊓ K₁ ≤ Bk :=
      le_inf (inf_le_right.trans hK₁K) ((inf_le_inf_left T hK₁K).trans Subgroup.le_normalizer)
    have hRS := hRL _ (isRankOneListed_of_isBenderAny hU3 hbend)
    have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK₁
    have hidx : ¬ 2 ∣ (modO2Image K₁ (T ⊓ K₁)).index := by
      have := hTt.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
    obtain ⟨-, hmax, -⟩ := hRS _ hTt.2.1 hidx
    have hP₁r : IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P₁ := by
      refine ⟨lt_of_le_of_ne le_sup_right fun he => not_isSolvable_of_mem_cComp hK₁ ?_,
        sup_le hK₁K inf_le_left, fun Q hBQ hQP => ?_⟩
      · have hK₁B : K₁ ≤ Bk := le_sup_left.trans he.ge
        exact Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hK₁B) (Subgroup.inclusion_injective _)
      · have hQeq : Q = Bk ⊔ (Q ⊓ K₁) :=
          A3.eq_sup_inf_of_le_sup hBkN hBQ.le (hQP.trans (sup_comm K₁ Bk).le)
        have hTQ : T ⊓ K₁ ≤ Q ⊓ K₁ := le_inf (hTK₁Bk.trans hBQ.le) inf_le_right
        by_cases hQ₁ : modO2Image K₁ (Q ⊓ K₁) = ⊤
        · have h1 := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top inf_le_right hQ₁
          rw [sup_eq_left.mpr (hOK₁.trans hTQ)] at h1
          have hK₁Q : K₁ ≤ Q := h1.trans inf_le_left
          rw [hQeq, inf_eq_right.mpr hK₁Q, sup_comm Bk K₁]
        · exfalso
          have h1 := hmax _ (Subgroup.map_mono fun x hx => hTQ hx) hQ₁
          have h2 := h1.trans (normalizer_modO2Image_le (P := K₁ ⊓ Subgroup.normalizer
            ((T ⊓ K₁ : Subgroup G) : Set G)) inf_le_right hOK₁ le_rfl)
          have h3 := le_sup_of_modO2Image_le inf_le_right inf_le_left h2
          rw [sup_eq_left.mpr (hOK₁.trans (le_inf inf_le_right Subgroup.le_normalizer))] at h3
          have h4 : Q ⊓ K₁ ≤ Bk := h3.trans hborel
          rw [hQeq, sup_eq_left.mpr h4] at hBQ
          exact lt_irrefl _ hBQ
    rw [← hcore]
    exact (hXP P₁ hP₁r).trans (normalizer_le_normalizer_perfectCore P₁)

theorem stmt5_2_L2Lie_of_inputs_F4
    (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hRL : RankOneListedFacts.{0})
    (h515 : Stmt5_1_5_F4) (h510 : Stmt5_1_10_F4) : Stmt5_2_L2Lie_F4 :=
  stmt5_2_L2Lie_of_F4 hU3 hF (stmt5_2_L2Two_of_F4 a38ForSQTKCat_holds hRL hU3 h515 h510) h510

theorem stmt5_2_1_par_of_inputs_F4
    (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hRL : RankOneListedFacts.{0})
    (h515 : Stmt5_1_5_F4) (h510 : Stmt5_1_10_F4) : Stmt5_2_1_par_F4 :=
  stmt5_2_1_par_of_F4 hF (stmt5_2_L2Two_of_F4 a38ForSQTKCat_holds hRL hU3 h515 h510) h510

theorem ch5L2ChoiceExists_of_inputs_F4 (h510 : Stmt5_1_10_F4) (hF : FactL2LieParabolic) :
    Ch5L2ChoiceExists_F4 :=
  ch5L2ChoiceExists_of_F4 h510 (rankTwoParabolicFact_of hF)

end CFSG.Quasithin.H13
