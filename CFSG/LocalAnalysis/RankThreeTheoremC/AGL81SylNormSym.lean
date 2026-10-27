module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormReduce
public import CFSG.Permutation.SylowTwoNormalizer.Aut
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreRigid

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv

theorem pCore_two_perm_ne_bot {n : ℕ} (hn : n = 2 ∨ n = 4) : CFSG.pCore 2 (Perm (Fin n)) ≠ ⊥ := by
  rcases hn with rfl | rfl
  · exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_two_ne_bot
  · exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_four_ne_bot

theorem mulAut_perm_eq_one_of_wSup {n : ℕ} (h2 : CFSG.pCore 2 (Perm (Fin n)) = ⊥)
    (α : MulAut (Perm (Fin n))) (hα : Odd (orderOf α)) {S : Subgroup (Perm (Fin n))}
    (hSW : S ≤ wSup (Perm (Fin n))) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (wSup (Perm (Fin n)))) (hαS : S.map α.toMonoidHom = S) :
    α = 1 ∨ (n = 5 ∧ 3 ∣ orderOf α) := by
  classical
  have h2' : n ≠ 2 := by rintro rfl; exact pCore_two_perm_ne_bot (Or.inl rfl) h2
  have h4' : n ≠ 4 := by rintro rfl; exact pCore_two_perm_ne_bot (Or.inr rfl) h2
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  ·
    haveI : Subsingleton (Fin n) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hn1)
    exact Or.inl (Subsingleton.elim α 1)
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact absurd rfl h2'
    · rcases Nat.lt_or_ge n 4 with hn4 | hn4
      ·
        obtain rfl : n = 3 := by omega
        have htop : (⊤ : Subgroup (Perm (Fin 3))) ≤ wSup (Perm (Fin 3)) :=
          le_wSup_of_normal_of_mulEquiv (N := ⊤) inferInstance Subgroup.topEquiv
        have hWeq : wSup (Perm (Fin 3)) = ⊤ := le_antisymm le_top htop
        have hUi : ¬ 2 ∣ S.index := by
          rw [← Subgroup.relIndex_top_right S, ← hWeq]
          exact hSi
        exact Or.inl
          (CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_three_eq_one α hα hS hUi hαS)
      · rcases Nat.lt_or_ge n 5 with hn5 | hn5
        · obtain rfl : n = 4 := by omega
          exact absurd rfl h4'
        ·
          have hn5' : 5 ≤ n := hn5
          haveI : (alternatingGroup (Fin n)).Normal := alternatingGroup.normal
          have hAle : alternatingGroup (Fin n) ≤ wSup (Perm (Fin n)) :=
            le_wSup_of_normal_of_isQuasisimple inferInstance
              ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
                ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
                  (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup hn5')))
          have hU2 : IsPGroup 2 ↥(S ⊓ alternatingGroup (Fin n)) := IsPGroup.to_inf_left hS
          have hSN : S ≤ Subgroup.normalizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
            rw [Subgroup.normalizer_eq_top]
            exact le_top
          have hUi : ¬ 2 ∣ (S ⊓ alternatingGroup (Fin n)).relIndex (alternatingGroup (Fin n)) :=
            CFSG.Quasithin.not_two_dvd_relIndex_inf_of_normalizer hSW hAle hSi hSN
          have hfix : (alternatingGroup (Fin n)).map α.toMonoidHom = alternatingGroup (Fin n) :=
            Subgroup.characteristic_iff_map_eq.mp instCharacteristicPermAlternatingGroup α
          have hUmap : (S ⊓ alternatingGroup (Fin n)).map α.toMonoidHom =
              S ⊓ alternatingGroup (Fin n) := by
            rw [Subgroup.map_inf_eq _ _ _ α.injective, hαS, hfix]
          exact CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_eq_one_or hn5' α hα
            inf_le_right hU2 hUi hUmap

theorem kFactSylNormSym : KFactSylNormSym := by
  intro A _ _ P b n he hb hW
  obtain ⟨e⟩ := he
  obtain ⟨α, hαdvd, -, ⟨S, hSW, hS2, hSi, hαS⟩, w, -, hαw⟩ :=
    exists_mulAut_of_sylAct (Q := Perm (Fin n)) e hb hW
  have hodd : Odd (orderOf α) := Odd.of_dvd_nat hb.1 hαdvd
  have h2 : CFSG.pCore 2 (Perm (Fin n)) = ⊥ := pCore_two_eq_bot_of_mulEquiv e
  have hne : α ≠ 1 := by
    intro h
    rw [h] at hαw
    exact hαw rfl
  rcases mulAut_perm_eq_one_of_wSup h2 α hodd hSW hS2 hSi hαS with h | ⟨hn5, h3⟩
  · exact absurd h hne
  · exact ⟨Nat.dvd_trans h3 hαdvd, hn5⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
