module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWTypes
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormSym

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree Subgroup Equiv

theorem alternatingGroup_le_wSup {n : ℕ} (hn : 5 ≤ n) :
    alternatingGroup (Fin n) ≤ wSup (Perm (Fin n)) := by
  haveI : (alternatingGroup (Fin n)).Normal := alternatingGroup.normal
  exact le_wSup_of_normal_of_isQuasisimple inferInstance
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup hn)))

theorem sign_eq_one_of_odd_orderOf {n : ℕ} {β : Perm (Fin n)} (h : Odd (orderOf β)) :
    Perm.sign β = 1 := by
  have h1 : Perm.sign β ^ orderOf β = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign β) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem oddInnW_perm {n : ℕ} (h2 : CFSG.pCore 2 (Perm (Fin n)) = ⊥) : OddInnW (Perm (Fin n)) := by
  classical
  intro α hα
  have h2' : n ≠ 2 := by rintro rfl; exact pCore_two_perm_ne_bot (Or.inl rfl) h2
  have h4' : n ≠ 4 := by rintro rfl; exact pCore_two_perm_ne_bot (Or.inr rfl) h2
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  ·
    haveI : Subsingleton (Fin n) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hn1)
    refine ⟨1, one_mem _, fun x _ => ?_⟩
    rw [Subsingleton.elim α 1]
    simp
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  ·
    obtain rfl : n = 3 := by omega
    have htop : (⊤ : Subgroup (Perm (Fin 3))) ≤ wSup (Perm (Fin 3)) :=
      le_wSup_of_normal_of_mulEquiv (N := ⊤) inferInstance Subgroup.topEquiv
    obtain ⟨g, hg⟩ := CFSG.Quasithin.SBd.perm_three_aut_inner α
    exact ⟨g, htop (mem_top g), fun x _ => hg x⟩
  ·
    obtain ⟨β, rfl⟩ := CFSG.Permutation.SylowTwoNormalizer.exists_perm_conj_of_odd_orderOf hn5 α hα
    have hk : β ^ orderOf (MulAut.conj β) = 1 := by
      apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
      rw [map_one]
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have h1 := congrArg (fun γ : MulAut (Perm (Fin n)) => γ (x : Perm (Fin n)))
        (pow_orderOf_eq_one (MulAut.conj β))
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      exact h1
    have hβ : Odd (orderOf β) := hα.of_dvd_nat (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨β, alternatingGroup_le_wSup hn5 (Perm.mem_alternatingGroup.mpr
      (sign_eq_one_of_odd_orderOf hβ)), fun x _ => rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
