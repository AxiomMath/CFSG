module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

theorem fi22_inf_centralizer_rep_not_isPGroup
    {k : ℕ} (hk : k < 6) :
    ¬ IsPGroup 2 ↥(fi22P ⊓ centralizer ({fi22ExtRep k} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨h0, h1, h3, h4, h5, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  have hH : ∀ c < 5, ¬ IsPGroup 2 ↥(fi22H c) := by
    intro c hc
    apply not_isPGroup_of_three_dvd
    rw [card_fi22H hc]
    interval_cases c <;> simp [fi22CentOrders]
  interval_cases k
  · rw [h0]; exact hH 0 (by norm_num)
  · rw [h1]; exact hH 1 (by norm_num)
  · rw [fi22ExtRep_two]
    exact not_isPGroup_of_mulEquiv fi22CPzEquiv
      (not_isPGroup_centralizer_of_isConj isConj_fi22OuterZP_fi22Ya.symm
        (not_isPGroup_of_three_dvd (by rw [card_centralizer_fi22Ya]; norm_num)))
  · rw [h3]; exact hH 2 (by norm_num)
  · rw [h4]; exact hH 3 (by norm_num)
  · rw [h5]; exact hH 4 (by norm_num)

theorem sporNoTwoFix_Fi22
    : SporNoTwoFix .Fi22 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥fi22P) fi22PermEquiv fun a ha => ?_
  obtain ⟨r, rfl⟩ := fi22RAut.surjective a
  have hr : orderOf (r : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq fi22RAut r]
    exact ha
  rw [← Hin.fixSub_eq_fixedPoints]
  refine not_isPGroup_of_mulEquiv (fixSubRAutEquiv r) ?_
  obtain ⟨k, hk, c, hc, hck⟩ := fi22R_involution_conj r.2 hr
  have e := (fi22CP_conj_equiv (fi22R_le_normalizer hc) (r : Equiv.Perm (Fin 3510))).trans
    (MulEquiv.subgroupCongr (by rw [hck]))
  exact not_isPGroup_of_mulEquiv e (fi22_inf_centralizer_rep_not_isPGroup hk)

end CFSG.ComponentClassification.HarrisLit.L33.SR
