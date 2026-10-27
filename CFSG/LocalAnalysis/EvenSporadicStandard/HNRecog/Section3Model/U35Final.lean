module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.Quasithin.H13.ModelsUnitary
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.Assembly.LowTwoRank

theorem psu3_eq_quasithinPSU (p k : ℕ) [Fact p.Prime] :
    CFSG.Open.PSU3 p k = CFSG.Open.quasithinPSU 3 p k := by
  have hJ : CFSG.Open.quasithinAntidiag 3 (GaloisField p (2 * k)) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [CFSG.Open.PSU3, CFSG.Open.quasithinPSU, hJ]

theorem psu3_five_statedClassicalModel [Fact (Nat.Prime 5)] :
    StatedClassicalModel ↥(CFSG.Open.PSU3 5 1) .PSU 3 5 1 := by
  obtain ⟨f⟩ := CFSG.Quasithin.H13.nonempty_statedProj_statedSU_mulEquiv_quasithinPSU 3 5 1
    (by norm_num)
  exact ⟨⟨Nat.prime_five, le_rfl, by norm_num, by decide⟩, GaloisField 5 (2 * 1), inferInstance,
    inferInstance, CFSG.Quasithin.H13.card_galoisField_two_mul 5 1 (by norm_num),
    ⟨(MulEquiv.subgroupCongr (psu3_eq_quasithinPSU 5 1)).trans f.symm⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3Model

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem u35Facts_holds : U35Facts := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hcard, -, -, hconj⟩ :=
    CFSG.RankThree.Classical.unitary_three_five_model ↥(CFSG.Open.PSU3 5 1)
      psu3_five_statedClassicalModel
  refine ⟨fun X _ ⟨e⟩ => ?_, fun X _ ⟨e⟩ s t hs ht hs1 ht1 => ?_⟩
  · rw [Nat.card_congr e.toEquiv, hcard]
  · have h2 : ∀ x : X, x ^ 2 = 1 → x ≠ 1 → orderOf (e x) = 2 := fun x hx hx1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hx hx1
    have := hconj (e s) (e t) (h2 s hs hs1) (h2 t ht ht1)
    simpa using MonoidHom.map_isConj e.symm.toMonoidHom this

end CFSG.EvenSporadicStandard.HNRecog.Section3
