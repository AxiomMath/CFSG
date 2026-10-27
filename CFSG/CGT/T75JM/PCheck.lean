module

public import CFSG.CGT.T75JM.N0Model
public import CFSG.CGT.T75JM.PCheckInputs
public import CFSG.CGT.T75JM.PStruct

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native


theorem tabEq_sound {w w' : List (Fin 6 × Bool)} (h : tabEq w w' = true) : val6 w = val6 w' :=
  n0_eq_of_tab_eq (beq_iff_eq.1 h)

theorem tabEq_of_eq {w w' : List (Fin 6 × Bool)} (h : val6 w = val6 w') : tabEq w w' = true :=
  beq_iff_eq.2 (n0_eq_iff_tab.1 h)

theorem conj_sound {a b r : List (Fin 6 × Bool)} (h : tabEq (a ++ b ++ invWord a) r = true) :
    val6 a * val6 b * (val6 a)⁻¹ = val6 r := by
  have := tabEq_sound h
  rwa [val6_append, val6_append, val6_invWord] at this

theorem e_mul_sound (h : eMulCheck = true) :
    ∀ c d : V3, val6 (vExp (eW c)) * val6 (vExp (eW d)) = val6 (vExp (eW (c + d))) := by
  intro c d
  rw [← val6_append]
  unfold eMulCheck at h
  exact tabEq_sound (of_decide_eq_true h c d)

theorem e_inj_sound (h : eInjCheck = true) :
    ∀ c d : V3, val6 (vExp (eW c)) = val6 (vExp (eW d)) → c = d :=
  fun c d hcd => by
    unfold eInjCheck at h
    exact of_decide_eq_true h c d (tabEq_of_eq hcd)

theorem e_tors_sound (h : eTorsCheck = true) :
    ∃ c : V3, c ≠ 0 ∧ val6 (vExp (eW c)) = val6 [(2, true), (3, true), (4, true)] := by
  simp only [eTorsCheck, Bool.and_eq_true] at h
  exact ⟨Pi.single 0 1, of_decide_eq_true h.2, tabEq_sound h.1⟩

theorem act_v_sound (h : actVCheck = true) :
    (∀ c : V3, val6 (vGen 0) * val6 (vExp (eW c)) * (val6 (vGen 0))⁻¹ =
      val6 (vExp (eW (glAct mV1 c)))) ∧
    (∀ c : V3, val6 (vGen 1) * val6 (vExp (eW c)) * (val6 (vGen 1))⁻¹ =
      val6 (vExp (eW (glAct mV2 c)))) :=
  by
    unfold actVCheck at h
    exact ⟨fun c => conj_sound (of_decide_eq_true h c).1,
      fun c => conj_sound (of_decide_eq_true h c).2⟩

theorem act_g_sound (h : actGCheck = true) :
    ∀ c : V3, val6 (dExp (dW c)) = val6 (vExp (eW c)) ∧
      val6 (thExp (dW c)) = val6 (vExp (eW (glAct mG c))) :=
  by
    unfold actGCheck at h
    exact fun c => ⟨tabEq_sound (of_decide_eq_true h c).1, tabEq_sound (of_decide_eq_true h c).2⟩

theorem theta_sound (h : thetaCheck = true) :
    val6 (dExp uW) = val6 (vExp wA) ∧ val6 (thExp uW) = val6 (vExp wB) := by
  simp only [thetaCheck, Bool.and_eq_true] at h
  exact ⟨tabEq_sound h.1, tabEq_sound h.2⟩

theorem d8_sound (h : d8Check = true) :
    val6 (vExp (sV ++ sV)) = 1 ∧ val6 (vExp (rV ++ rV ++ rV ++ rV)) = 1 ∧
    val6 (vExp (sV ++ rV ++ sV ++ rV)) = 1 ∧
    (∀ c : V3, val6 (vExp sV) * val6 (vExp (eW c)) * (val6 (vExp sV))⁻¹ =
      val6 (vExp (eW (glAct mS c)))) ∧
    (∀ c : V3, val6 (vExp rV) * val6 (vExp (eW c)) * (val6 (vExp rV))⁻¹ =
      val6 (vExp (eW (glAct mR c)))) := by
  simp only [d8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, fun c => ?_, fun c => ?_⟩
  · simpa [val6_nil] using tabEq_sound h1
  · simpa [val6_nil] using tabEq_sound h2
  · simpa [val6_nil] using tabEq_sound h3
  · exact conj_sound (of_decide_eq_true h4 c).1
  · exact conj_sound (of_decide_eq_true h4 c).2

theorem pFacts_of_checks (h1 : eMulCheck = true) (h2 : eInjCheck = true)
    (h3 : ∀ n : PG 6 rels6, (∀ j : Fin 3, n * val6 (vExp (eW (Pi.single j 1))) =
      val6 (vExp (eW (Pi.single j 1))) * n) → ∃ c : V3, n = val6 (vExp (eW c)))
    (h4 : eTorsCheck = true) (h5 : actVCheck = true) (h6 : actGCheck = true)
    (h7 : thetaCheck = true) (h8 : d8Check = true)
    (h9 : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS mR d) c = c) → d = 1)
    (h10 : FinCheck mv pRs pEw pWords) : PFacts := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := d8_sound h8
  exact
    { e_mul := e_mul_sound h1
      e_inj := e_inj_sound h2
      e_cent := h3
      e_tors := e_tors_sound h4
      act_v1 := (act_v_sound h5).1
      act_v2 := (act_v_sound h5).2
      act_g := act_g_sound h6
      theta_rel := theta_sound h7
      d8_sq := d1
      d8_four := d2
      d8_conj := d3
      d8_act_s := d4
      d8_act_r := d5
      d8_dist := h9
      fin := h10 }

end CFSG.CGT.T75JM
