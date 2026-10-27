module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRFi22
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRLift
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.FischerOddCore.Fi23NoComp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

theorem fi22J_centralizer_not_isPGroup
    {u : CFSG.Sporadic.Fi22.J} (hu : u ^ 2 = 1) :
    ¬ IsPGroup 2 ↥(centralizer ({u} : Set CFSG.Sporadic.Fi22.J)) := by
  by_cases h1 : u = 1
  · subst h1
    have htop : centralizer ({1} : Set CFSG.Sporadic.Fi22.J) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [mem_centralizer_singleton_iff, mul_one, one_mul]
    rw [htop]
    exact not_isPGroup_of_three_dvd
      (by rw [Subgroup.card_top, CFSG.Sporadic.Fi22.card_J]; norm_num)
  · have hp2 : orderOf ((fi22PJ.symm u : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hu h1
    obtain ⟨k, hk, r, hr, hrk⟩ := fi22R_involution_conj (fi22P_le_R (fi22PJ.symm u).2) hp2
    have e0 := (fi22CP_conj_equiv (fi22R_le_normalizer hr)
      ((fi22PJ.symm u : fi22P) : Equiv.Perm (Fin 3510))).trans
        (MulEquiv.subgroupCongr (by rw [hrk]))
    have h0 := not_isPGroup_of_mulEquiv e0 (fi22_inf_centralizer_rep_not_isPGroup hk)
    have e1 := infCentralizerEquiv fi22P (fi22PJ.symm u).2
    have e2 := @centralizerMulEquiv fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ
      (fi22PJ.symm u)
    have e3 : ↥(centralizer ({fi22PJ (fi22PJ.symm u)} : Set CFSG.Sporadic.Fi22.J)) ≃*
        ↥(centralizer ({u} : Set CFSG.Sporadic.Fi22.J)) :=
      MulEquiv.subgroupCongr (by rw [MulEquiv.apply_symm_apply])
    exact not_isPGroup_of_mulEquiv ((e1.trans e2).trans e3).symm h0

theorem fi23_inf_centralizer_not_isPGroup
    {s : CFSG.Sporadic.Fi23.J} (hs : s ∈ CFSG.Sporadic.Fi23.Cd) (hs2 : s ^ 2 = 1) :
    ¬ IsPGroup 2 ↥(CFSG.Sporadic.Fi23.Cd ⊓ centralizer ({s} : Set CFSG.Sporadic.Fi23.J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : fi23Kappa ⟨s, hs⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have h2 : (⟨s, hs⟩ : CFSG.Sporadic.Fi23.Cd) ^ 2 = 1 := by
      apply Subtype.ext
      change s ^ 2 = 1
      exact hs2
    rw [h2, map_one]
  have hk2 : IsPGroup 2 ↥(fi23Kappa : CFSG.Sporadic.Fi23.Cd →* CFSG.Sporadic.Fi22.J).ker := by
    apply IsPGroup.of_card (n := 1)
    rw [ker_fi23Kappa, CFSG.Sporadic.Fi23.card_center_C, pow_one]
  exact not_isPGroup_inf_centralizer_of_central CFSG.Sporadic.Fi23.Cd fi23Kappa
    fi23Kappa_surjective ker_fi23Kappa.le hk2 hs (fi22J_centralizer_not_isPGroup hu)

theorem fi23J_centralizer_not_isPGroup
    {v : CFSG.Sporadic.Fi23.J} (hv : v ^ 2 = 1) :
    ¬ IsPGroup 2 ↥(centralizer ({v} : Set CFSG.Sporadic.Fi23.J)) := by
  by_cases h1 : v = 1
  · subst h1
    have htop : centralizer ({1} : Set CFSG.Sporadic.Fi23.J) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [mem_centralizer_singleton_iff, mul_one, one_mul]
    rw [htop]
    exact not_isPGroup_of_three_dvd
      (by rw [Subgroup.card_top, CFSG.Sporadic.Fi23.card_J]; norm_num)
  have hrep : ∀ r ∈ CFSG.Sporadic.Fi23.Cd, r ^ 2 = 1 →
      ¬ IsPGroup 2 ↥(centralizer ({r} : Set CFSG.Sporadic.Fi23.J)) := fun r hr hr2 =>
    not_isPGroup_of_le inf_le_right (fi23_inf_centralizer_not_isPGroup hr hr2)
  have hdCd : CFSG.Sporadic.Fi23.d ∈ CFSG.Sporadic.Fi23.Cd := CFSG.Sporadic.Fi23.mem_Cd.2 rfl
  rcases CFSG.Sporadic.Fi23.involution_cover v hv h1 with h | h | h
  · exact not_isPGroup_centralizer_of_isConj h (hrep _ hdCd CFSG.Sporadic.Fi23.d_sq')
  · exact not_isPGroup_centralizer_of_isConj h (hrep _ (mul_mem hdCd fi23_d1_mem_Cd)
      CFSG.Sporadic.Fi23.d_mul_d1_sq)
  · exact not_isPGroup_centralizer_of_isConj h (hrep _ fi23_t2_mem_Cd
      CFSG.Sporadic.Fi23.t2_sq)

theorem sporNoTwoFix_Fi23 :
    SporNoTwoFix .Fi23 := by
  intro Y _ _ ⟨e⟩
  have e' : Y ≃* ↥CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hs : IsSimpleGroup CFSG.Sporadic.Fi23.J := CFSG.Sporadic.Fi23.isSimpleGroup_J
  have hsY : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ hs e'
  have hZ : center Y = ⊥ := center_eq_bot_of_not_prime hsY
    ((Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.Fi23.card_J) (by norm_num)
  refine forall_of_inner hZ (mulAut_eq_conj_of_mulEquiv e fi23_mulAut_eq_conj) fun t ht => ?_
  have ht' : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have ht2 : e' t ^ 2 = 1 := by rw [← ht', pow_orderOf_eq_one]
  exact @not_isPGroup_of_mulEquiv _ _ _ (Subgroup.toGroup _)
    (@centralizerMulEquiv Y _ _ (Subgroup.toGroup _) e' t) (fi23J_centralizer_not_isPGroup ht2)

end CFSG.ComponentClassification.HarrisLit.L33.SR
