module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Field
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kay_L2 : KAY FL2 := by
  intro Y _ _ hY _ α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  obtain ⟨p0, f0, hp0, hf0, hp02, hlie⟩ := hY
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hlie
  let e : Y ≃* L2 F := e0.trans (L2.equivPSL F).symm
  have hoddF : Odd (Nat.card F) := by
    rw [hFcard]
    exact (hp0.odd_of_ne_two hp02).pow
  have hF3 : 3 < Nat.card F := by
    have h1 : p0 ≤ p0 ^ f0 := Nat.le_self_pow (by omega) p0
    have h2 : 3 ≤ p0 := by
      have := hp0.two_le
      omega
    have h3 : Nat.card F ≠ 3 := by rw [hFcard]; exact hpf3
    have : 3 ≤ Nat.card F := by rw [hFcard]; exact h2.trans h1
    omega
  have hK : KAAll α := kaAll_L2 ⟨hoddF, hF3⟩ e α hα2 hα1
  have hc := hK p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
