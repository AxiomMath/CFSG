module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem trivialOnQuot_of_mem_centralizerModOdd {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {c : Y} (hc : c ∈ centralizerModOdd ⊤ R) : c ∈ Balance.Bootstrap.trivialOnQuot R :=
  ⟨hc.2.1, fun x hx => hc.2.2.2 x hx⟩

theorem aEmpty_of_twinCore {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R)
    {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcm : c ∈ centralizerModOdd ⊤ R) :
    AEmpty (CoreAssembly.conjClass (tightCore (secR R c))) (tightCore (secR R c)) := by
  have hΩ := h.hyp
  have hA := h.aEmpty
  rw [hRc] at hΩ hA
  exact aEmpty_section' hΩ hA (Asc77.isPGroup_zpowers_of_mul_self_eq_one hc2 hc1)
    (trivialOnQuot_of_mem_centralizerModOdd hcm)

theorem twinSecA_proved (n : ℕ) : TwinEdge.TwinSecA n := by
  intro Y _ _ R S t h hRc J hJ u hu hut htu ht
  obtain ⟨hu2, -, hum⟩ := TwinEdge.edge_involution h.datum hRc h.hyp hJ hu hut
  exact Or.inl (aEmpty_of_twinCore h hRc hu2 hu.ne_one hum)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2
