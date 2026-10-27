module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.PieceDel
open scoped commutatorElement

theorem delKernelProp : DelKernelProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hloc hgen hsum
  classical
  have hS := ctx.setting
  have hbase := hloc.base.base
  have hQn := normal_Q hcore.normal
  have hLSn := hcore.normal
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hS.reduced.2.1)
  have hCn := centralizer_normal_of_normal hVn
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set Q : Subgroup G := pCoreOf 2 (L ⊔ baum R) with hQ
  have hQ2 : IsPGroup 2 ↥Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (L ⊔ baum R)
  have hQLS : Q ≤ L ⊔ baum R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (L ⊔ baum R)
  have hQO : Q ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q ⊤ le_top inferInstance hQ2
  have hO2C : pCoreOf 2 (⊤ : Subgroup G) ≤ Subgroup.centralizer (V : Set G) := by
    have hO2 : IsPGroup 2 ↥(pCoreOf 2 (⊤ : Subgroup G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 ⊤
    refine hS.reduced.2.2.2 _ le_top
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤) fun d hd => ?_
    obtain ⟨k, hk⟩ := hO2 ⟨d, hd⟩
    exact ⟨k, by
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact Subgroup.one_mem _⟩
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := hQO.trans hO2C
  have hUQ : ⁅Q, L⁆ ≤ BlueprintB2.centerTorsion 2 Q := by
    have := hgen.central
    rwa [BlueprintB2.omegaOneCenterOf_eq_centerTorsion] at this
  have hQLV : ⁅Q, L⁆ = ⁅V, L⁆ := hsum.commutator.1
  have hVL_le : ⁅V, L⁆ ≤ V := Subgroup.commutator_le_left V L
  have hodd1 : ∀ c ∈ (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G), Odd (orderOf c) → c = 1 := by
    intro c hc hodd
    have hcL : c ∈ L := Subgroup.subset_closure ⟨Subgroup.mem_top c, hodd⟩
    have hcQ : ∀ x ∈ Q, c * x = x * c := by
      refine commute_of_odd_order_of_commutator_central (U := ⁅Q, L⁆) hodd (fun x hx => ?_)
        (fun w hw => ?_) (fun w hw => ?_)
      · have h := Subgroup.commutator_mem_commutator hcL hx
        rwa [Subgroup.commutator_comm] at h
      · obtain ⟨-, hc', h2⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hUQ hw)
        exact ⟨hc', h2⟩
      · have hwV : w ∈ V := hVL_le (hQLV ▸ hw)
        exact (Subgroup.mem_centralizer_iff.mp hc.2 w hwV).symm
    have hcQ' : c ∈ (L ⊔ baum R) ⊓ Subgroup.centralizer (Q : Set G) :=
      ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcQ x hx).symm⟩
    have hcQmem : c ∈ Q := hbase.charTwo hcQ'
    obtain ⟨k, hk⟩ := hQ2 ⟨c, hcQmem⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hCLS : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) ≤ Q := by
    have hC2 : IsPGroup 2 ↥((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) :=
      isPGroup_two_of_odd_eq_one hodd1
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ (L ⊔ baum R)
      inf_le_left ?_ hC2
    have := hLSn
    have := hCn
    exact Subgroup.normal_subgroupOf
  have hK2 : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) = Q :=
    le_antisymm hCLS (le_inf hQLS hQC)
  refine ⟨?_, hK2⟩
  refine le_antisymm ?_ (le_inf le_top hO2C)
  have hC2 : IsPGroup 2 ↥((⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) := by
    refine isPGroup_two_of_odd_eq_one fun c hc hodd => ?_
    have hcL : c ∈ L := Subgroup.subset_closure ⟨Subgroup.mem_top c, hodd⟩
    exact hodd1 c ⟨(le_sup_left : L ≤ L ⊔ baum R) hcL, hc.2⟩ hodd
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ ⊤ le_top ?_ hC2
  have := hCn
  exact Subgroup.normal_subgroupOf

end CFSG.QuasithinUnique.Setup.Lift
