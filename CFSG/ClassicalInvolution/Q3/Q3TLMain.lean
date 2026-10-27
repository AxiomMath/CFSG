module

public import CFSG.ClassicalInvolution.Q3.Q3TLTwin
public import CFSG.ClassicalInvolution.Q3.Q3TK
public import CFSG.ClassicalInvolution.Q3.Q3TLNeg

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.Open (IsSubnormal classicalInvolutionOddCore)
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Balance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

theorem exists_orth_hypPairs {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {W W' : Submodule K V} (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    (hdim : finrank K W = 4) {U : Submodule K V} (hUW : U ≤ W) (hU : ∀ x ∈ U, Q x = 0)
    (hU2 : finrank K U = 2) : ∃ P₁ P₂ : HypPair (Q.comp W.subtype), P₁.Orth P₂ := by
  have hQW := nondegenerate_comp_subtype hQ hc horth
  obtain ⟨P, -, hP, -⟩ := exists_hypPairs_of_flag (Q := Q.comp W.subtype) 2 ⊤
    (polarNondegOn_top hQW) (by rw [finrank_top, hdim]) (U.comap W.subtype) le_top
    (fun x hx => hU _ hx) (by rw [(Submodule.comapSubtypeEquivOfLe hUW).finrank_eq, hU2]) 0
    (Nat.zero_le 2) (fun _ => ⊥) bot_le (fun i hi => by rw [Nat.le_zero.mp hi, finrank_bot])
    (fun i hi => absurd hi (Nat.not_lt_zero i))
    (fun x hx => by rw [(Submodule.mem_bot K).mp hx, QuadraticMap.map_zero])
  exact ⟨P 0, P 1, hP 0 1 (by decide)⟩

theorem d4OuterThree3_proved : D4OuterThree3 := by
  intro Y _ _ _ _ z L hz T _ _ _ _ hTn hCT f hf hker x hx hx3
  have hK := natCard_galoisField_three
  have hZ : Subgroup.center T = ⊥ := by
    refine eq_bot_iff.mpr fun c hc => ?_
    have hc' : (c : Y) ∈ Subgroup.centralizer (T : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
    rw [hCT, Subgroup.mem_bot] at hc'
    exact Subgroup.mem_bot.mpr (Subtype.ext hc')
  have hker' : f.ker = Subgroup.center _ :=
    le_antisymm hker (ModelFacts.ChevAut.center_le_ker_of_surjective hf hZ)
  obtain ⟨e, -⟩ := exists_mulEquiv_apply_eq f hf (d4Proj (GaloisField 3 1))
    (spinToStatedProj_quadPlus three_le_four).1
    (hker'.trans (spinToStatedProj_quadPlus three_le_four).2.2.symm)
  have hzT : z ∈ T := mem_of_socle_d4 hz hCT e
  set β := MulAut.congr e (MulAut.conjNormal x : MulAut T) with hβ
  obtain ⟨k, hk⟩ := hx3
  have hβk : β ^ (3 ^ k) = 1 := by
    rw [hβ, ← map_pow, ← map_pow, ← hk, pow_orderOf_eq_one, map_one, map_one]
  have hβodd : Odd (orderOf β) := by
    have h1 : orderOf β ∣ orderOf x :=
      orderOf_map_dvd ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) x
    rw [hk] at h1
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat h1
  have hinner : β • statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) → x ∈ T := fun hF => by
    obtain ⟨y, hy⟩ := exists_eq_conj_of_smul_statedPointFamily β hF hβodd
    exact mem_of_congr_mem_inner hCT e ⟨y, hy.symm⟩
  have hβt : β (e ⟨z, hzT⟩) = e ⟨z, hzT⟩ := by
    refine congr_conjNormal_apply_eq e ?_
    rw [MulEquiv.symm_apply_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hz.le_centralizer hx)
  have ht2 : e ⟨z, hzT⟩ ^ 2 = 1 := by
    have h1 : (⟨z, hzT⟩ : T) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← hz.orderOf_eq_two, pow_orderOf_eq_one, OneMemClass.coe_one])
    rw [← map_pow, h1, map_one]
  have ht1 : e ⟨z, hzT⟩ ≠ 1 := fun h1 => hz.ne_one (by
    have h2 := congrArg (fun q => (e.symm q : Y)) h1
    simpa using h2)
  obtain ⟨g, hgt, hgs, hg | hg⟩ := exists_lift_of_sq_eq_one _ ht2 ht1
  · rcases smul_eq_or_solid_of_sq_eq_one hK β hβk g hg (by rw [hgt]; exact hβt) with
      hF | ⟨S, hS, hinv⟩
    · exact hinner hF
    · obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
      obtain ⟨h4p, -, h2p, h2m⟩ := root_of_solid hK g hg hgs hS hinv
      have hGO := toLinEquiv_mem_orthogonalGroup g.2
      have hc := isCompl_plusSp_minusSp h2 hg
      have horth : ∀ u ∈ plusSp (toLinEquiv _ (GaloisField 3 1) g.val),
          ∀ w ∈ minusSp (toLinEquiv _ (GaloisField 3 1) g.val),
            polar (quadPlus 4 (GaloisField 3 1)) u w = 0 :=
        fun u hu w hw => polar_plusSp_minusSp h2 hGO hu hw
      obtain ⟨P₁, P₂, hP⟩ := exists_orth_hypPairs (nondegenerate_polarBilin_quadPlus 4 _) hc
        horth h4p inf_le_right (fun y hy => hS.2 y hy.1) h2p
      have hne : S ⊓ minusSp (toLinEquiv _ (GaloisField 3 1) g.val) ≠ ⊥ := fun h0 => by
        rw [h0, finrank_bot] at h2m
        omega
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
      have hOT : oddCoreIn (Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T)) = ⊥ :=
        oddCentralizerFreeTag_POmegaPlus 4 Nat.prime_three trivial hadm T f hf hker ⟨z, hzT⟩
          ((Subgroup.orderOf_coe (⟨z, hzT⟩ : T)).symm.trans hz.orderOf_eq_two)
      exact mem_of_root hCT e hzT hOT g hgt.symm hg hc horth hP h4p hw.2 hw0 (hS.2 w hw.1) hz x
        hx ⟨k, hk⟩
  · exact hinner (smul_eq_of_sq_eq_neg hK β hβk g hg (by rw [hgt]; exact hβt))

theorem quasisimpleConnected3_of_memberFree (hMF : MemberFreeSocleOuter3) :
    QuasisimpleConnected3 :=
  quasisimpleConnected3_of_socle hMF d4OuterThree3_proved

end CFSG.ClassicalInvolution.Q3.Q3T
