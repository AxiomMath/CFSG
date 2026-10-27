module

public import CFSG.Assembly.Defs
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem perfect_central_two_sylow_eq_bot (J : Subgroup G) [Group.IsPerfect J]
    (P : Sylow 2 J) (hcentral : (P : Subgroup J) ≤ Subgroup.center J) : J = ⊥ := by
  let : IsMulCommutative (P : Subgroup J) := isMulCommutative_iff.mpr
    (fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral x.property)) y).symm)
  have hnormalizer : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J) := by
    intro x _
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact ((Subgroup.mem_center_iff.mp (hcentral hy)) x).symm
  let transfer := MonoidHom.transferSylow P hnormalizer
  have htrivial : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
  have hkernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htrivial
  have hnotTwo : ¬ 2 ∣ Nat.card J := by
    have hnot := MonoidHom.not_dvd_card_ker_transferSylow P hnormalizer
    change ¬ 2 ∣ Nat.card transfer.ker at hnot
    simpa only [hkernel, Subgroup.card_top] using hnot
  have hodd : Odd (Nat.card J) := Nat.coprime_two_left.mp
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnotTwo)
  let : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsubsingleton : Subsingleton J := by
    rcases subsingleton_or_nontrivial J with h | h
    · exact h
    · let : Nontrivial J := h
      exact (Group.IsPerfect.not_isSolvable J inferInstance).elim
  exact J.eq_bot_of_subsingleton

theorem maximal_invariant_two_excludes_perfect (L K S J : Subgroup G) (a : G)
    (hSL : S ≤ L) (htwo : IsPGroup 2 S)
    (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hmaximal : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
      a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T = S)
    [Group.IsPerfect J] (hJL : J ≤ L)
    (hJS : ⁅J, S⁆ = ⊥) (haJ : a ∈ Subgroup.centralizer (J : Set G))
    (hKJ : ⁅K, J⁆ = ⊥) : J = ⊥ := by
  let P : Sylow 2 J := Classical.choice inferInstance
  let T := (P : Subgroup J).map J.subtype
  have hTJ : T ≤ J := Subgroup.map_subtype_le _
  have hTtwo : IsPGroup 2 T := P.isPGroup'.map J.subtype
  have hTS : T ≤ Subgroup.centralizer (S : Set G) :=
    hTJ.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJS)
  have hjoinTwo : IsPGroup 2 (↥(S ⊔ T)) := htwo.to_sup_of_normal_left' hTtwo
    (hTS.trans (Subgroup.centralizer_le_normalizer _))
  have haT : a ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _
      ((Subgroup.centralizer_le hTJ) haJ)
  have hKT : K ≤ Subgroup.normalizer (T : Set G) :=
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJ).trans
      (Subgroup.centralizer_le hTJ)).trans (Subgroup.centralizer_le_normalizer _)
  have haJoin : a ∈ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_sup S T) ⟨haS, haT⟩
  have hKJoin : K ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
    (le_inf hKS hKT).trans (Subgroup.inf_normalizer_le_normalizer_sup S T)
  have hjoin := hmaximal (S ⊔ T) (sup_le hSL (hTJ.trans hJL)) hjoinTwo
    haJoin hKJoin le_sup_left
  have hTSle : T ≤ S := by
    rw [← hjoin]
    exact le_sup_right
  have hcentral : (P : Subgroup J) ≤ Subgroup.center J := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hmemT : x.val ∈ T := Subgroup.mem_map_of_mem J.subtype hx
    have hcommute := Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJS) (hTSle hmemT))
          y.val y.property
    exact Subtype.ext hcommute
  exact perfect_central_two_sylow_eq_bot J P hcentral

end CFSG.ComponentClassification.AschbacherComponentInvolution
