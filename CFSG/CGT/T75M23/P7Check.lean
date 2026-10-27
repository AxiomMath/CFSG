module

public import CFSG.CGT.T75M23.N7Model
public import CFSG.CGT.T75M23.P7CheckInputs

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.CGT.T75JM (V3 glAct matD FinCheck)


theorem tabEq7_sound {w w' : Word6} (h : tabEq7 w w' = true) : n7 w = n7 w' :=
  n7_eq_of_tab_eq (beq_iff_eq.1 h)

theorem tabEq7_of_eq {w w' : Word6} (h : n7 w = n7 w') : tabEq7 w w' = true :=
  beq_iff_eq.2 (n7_eq_iff_tab.1 h)

theorem conj7_sound {a b r : Word6} (h : tabEq7 (a ++ b ++ invWord7 a) r = true) :
    n7 a * n7 b * (n7 a)⁻¹ = n7 r := by
  have := tabEq7_sound h
  rwa [n7_append, n7_append, n7_invWord] at this

theorem allV3V3_spec {f : V3 → V3 → Bool} (h : allV3V3 f = true) : ∀ c d, f c d = true := by
  unfold allV3V3 at h
  exact of_decide_eq_true h

theorem allFin2V3_spec {f g : Fin 2 → V3 → Bool} (h : allFin2V3 f g = true) :
    ∀ k c, f k c = true ∧ g k c = true := by
  unfold allFin2V3 at h
  exact of_decide_eq_true h

theorem e_mul7_sound (h : eMulCheck7 = true) :
    ∀ c d : V3, n7 (vExp7 (eW7 c)) * n7 (vExp7 (eW7 d)) = n7 (vExp7 (eW7 (c + d))) := by
  intro c d
  rw [← n7_append]
  exact tabEq7_sound (allV3V3_spec h c d)

theorem e_inj7_sound (h : eInjCheck7 = true) :
    ∀ c d : V3, n7 (vExp7 (eW7 c)) = n7 (vExp7 (eW7 d)) → c = d :=
  fun c d hcd => by
    unfold eInjCheck7 at h
    exact of_decide_eq_true h c d (tabEq7_of_eq hcd)

theorem e_tors7_sound (h : eTorsCheck7 = true) :
    ∃ c : V3, c ≠ 0 ∧ n7 (vExp7 (eW7 c)) = n7 [(2, true), (5, true)] := by
  simp only [eTorsCheck7, Bool.and_eq_true] at h
  exact ⟨Pi.single 2 1, of_decide_eq_true h.2, tabEq7_sound h.1⟩

theorem act_v7_sound (h : actVCheck7 = true) :
    (∀ c : V3, n7 (vGen7 0) * n7 (vExp7 (eW7 c)) * (n7 (vGen7 0))⁻¹ =
      n7 (vExp7 (eW7 (glAct mV17 c)))) ∧
    (∀ c : V3, n7 (vGen7 1) * n7 (vExp7 (eW7 c)) * (n7 (vGen7 1))⁻¹ =
      n7 (vExp7 (eW7 (glAct mV27 c)))) := by
  unfold actVCheck7 at h
  exact ⟨fun c => conj7_sound (of_decide_eq_true h c).1,
    fun c => conj7_sound (of_decide_eq_true h c).2⟩

theorem act_g7_sound (h : actGCheck7 = true) :
    ∀ (k : Fin 2) (c : V3), n7 (dExp7 (dW7 c)) = n7 (vExp7 (eW7 c)) ∧
      n7 (thExp7 k (dW7 c)) = n7 (vExp7 (eW7 (glAct mG7 c))) := by
  exact fun k c => ⟨tabEq7_sound (allFin2V3_spec h k c).1,
    tabEq7_sound (allFin2V3_spec h k c).2⟩

theorem theta7_sound (h : thetaCheck7 = true) :
    n7 (dExp7 uW7) = n7 (vExp7 wA7) ∧ n7 (thExp7 0 uW7) = n7 (vExp7 wB7) := by
  simp only [thetaCheck7, Bool.and_eq_true] at h
  exact ⟨tabEq7_sound h.1, tabEq7_sound h.2⟩

theorem d0_7_sound (h : d0Check7 = true) : n7 (d0W7 1) = n7 (vExp7 wD07) :=
  tabEq7_sound h

theorem d8_7_sound (h : d8Check7 = true) :
    n7 (vExp7 (sV7 ++ sV7)) = 1 ∧ n7 (vExp7 (rV7 ++ rV7 ++ rV7 ++ rV7)) = 1 ∧
    n7 (vExp7 (sV7 ++ rV7 ++ sV7 ++ rV7)) = 1 ∧
    (∀ c : V3, n7 (vExp7 sV7) * n7 (vExp7 (eW7 c)) * (n7 (vExp7 sV7))⁻¹ =
      n7 (vExp7 (eW7 (glAct mS7 c)))) ∧
    (∀ c : V3, n7 (vExp7 rV7) * n7 (vExp7 (eW7 c)) * (n7 (vExp7 rV7))⁻¹ =
      n7 (vExp7 (eW7 (glAct mR7 c)))) := by
  simp only [d8Check7, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, fun c => ?_, fun c => ?_⟩
  · simpa [n7_nil] using tabEq7_sound h1
  · simpa [n7_nil] using tabEq7_sound h2
  · simpa [n7_nil] using tabEq7_sound h3
  · exact conj7_sound (of_decide_eq_true h4 c).1
  · exact conj7_sound (of_decide_eq_true h4 c).2

theorem pFacts7_of_checks (h1 : eMulCheck7 = true) (h2 : eInjCheck7 = true)
    (h3 : ∀ n : N7, (∀ j : Fin 3, n * n7 (vExp7 (eW7 (Pi.single j 1))) =
      n7 (vExp7 (eW7 (Pi.single j 1))) * n) → ∃ c : V3, n = n7 (vExp7 (eW7 c)))
    (h4 : eTorsCheck7 = true) (h5 : actVCheck7 = true)
    (h6 : actGCheck7 = true) (h7 : thetaCheck7 = true) (h7' : d0Check7 = true)
    (h8 : d8Check7 = true)
    (h9 : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS7 mR7 d) c = c) → d = 1)
    (h10 : FinCheck mv7 pRs7a pEw7 pWords7) (h11 : FinCheck mv7 pRs7b pEw7 [pEw7 0]) :
    PFacts7 := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := d8_7_sound h8
  exact
    { e_mul := e_mul7_sound h1
      e_inj := e_inj7_sound h2
      e_cent := h3
      e_tors := e_tors7_sound h4
      act_v1 := (act_v7_sound h5).1
      act_v2 := (act_v7_sound h5).2
      act_g := act_g7_sound h6
      theta_rel := theta7_sound h7
      d0_rel := d0_7_sound h7'
      d8_sq := d1
      d8_four := d2
      d8_conj := d3
      d8_act_s := d4
      d8_act_r := d5
      d8_dist := h9
      fin0 := h10
      fin1 := h11 }

end CFSG.CGT.T75M23
