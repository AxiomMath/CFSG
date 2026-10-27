module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusPSU
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem lemma511_input20_27_2_holds : LocalBalance.Lemma511Ns.Input20_27_2 := by
  intro Y _ _ hperf hext hnot B hB _
  rcases hext with ⟨K, _, _, h3, ⟨e⟩⟩ | ⟨K, _, _, q, hcard, hq3, hq8, ⟨e⟩⟩
  · have h4 : Nat.card K ≠ 4 := fun h4 => hnot ⟨K, inferInstance, inferInstance, h4, ⟨e⟩⟩
    exact FixedTorus.of_mulEquiv e (fixedTorus_statedProj_sl h3 h4) B hB
  · have hq2 : q ≠ 2 := by
      rintro rfl
      have hF : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hcard
      have e' : Y ≃* StatedProj (StatedSU 3 (2 ^ 1) K) := e
      have hsolP := CFSG.Quasithin.isSolvable_statedProj_one hF
      have hsolY : Group.IsSolvable Y :=
        Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
      have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hperf
      have : Nontrivial Y := by
        have h72 := CFSG.Quasithin.card_statedProj_one hF
        rw [← Nat.card_congr e'.toEquiv] at h72
        have : Finite Y := inferInstance
        exact Finite.one_lt_card_iff_nontrivial.1 (by rw [h72]; norm_num)
      exact Group.IsPerfect.not_isSolvable Y hsolY
    exact FixedTorus.of_mulEquiv e (fixedTorus_statedProj_su hcard hq3 hq2 hq8) B hB

end CFSG.HardMathSupport.Solomon.Coordinator
