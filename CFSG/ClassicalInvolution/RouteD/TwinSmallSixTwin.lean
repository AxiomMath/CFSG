module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallWitt
public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Twin

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem not_commutes_twin_of_adj (hodd : Odd (Nat.card K)) {A B L' : Subgroup (V ≃ₗ[K] V)}
    {iA iB : V ≃ₗ[K] V} (hA : IsFundamental Q A iA) (hB : IsFundamental Q B iB)
    (hL : IsFundamental Q L' iB) (hAB : A ≠ B) (hLB : L' ≠ B) (hnc : ¬ Commutes A B)
    (hBL : Commutes B L') : ¬ Commutes A L' := by
  intro hc
  rcases orth_or_twin hodd hA hL hc with horth | heq
  · apply hnc
    have h2 := IsFundamental.two_ne_zero_of_odd hodd
    obtain ⟨FA, rfl, rfl⟩ := hA
    obtain ⟨FB, rfl, rfl⟩ := hB
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at horth
    rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
    exact commutes_of_span_orth FA FB horth X Y
  · obtain ⟨L'', hL'', hne, hcomm, huniq⟩ := IsFundamental.exists_twin hodd hB
    have hA' : IsFundamental Q A iB := heq ▸ hA
    rcases huniq A hA' with e | e
    · exact absurd e hAB
    · rcases huniq L' hL with e' | e'
      · exact absurd e' hLB
      · apply hnc
        rw [e, ← e'] at *
        exact commutes_symm hBL

end Twin

section Six

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem twin_of_leaves_six (hodd : Odd (Nat.card F))
    {L₂ L₃ L₄ LM : Subgroup (Vm 6 F ≃ₗ[F] Vm 6 F)} {i₂ i₃ i₄ iM : Vm 6 F ≃ₗ[F] Vm 6 F}
    (h₂ : IsFundamental (quadMinus 6 F b c) L₂ i₂) (h₃ : IsFundamental (quadMinus 6 F b c) L₃ i₃)
    (h₄ : IsFundamental (quadMinus 6 F b c) L₄ i₄) (hM : IsFundamental (quadMinus 6 F b c) LM iM)
    (hne23 : L₂ ≠ L₃) (hne24 : L₂ ≠ L₄) (hnc23 : ¬ Commutes L₂ L₃) (hnc24 : ¬ Commutes L₂ L₄)
    (hc34 : Commutes L₃ L₄) (hM2 : Commutes LM L₂) (hM3 : Commutes LM L₃)
    (hM4 : Commutes LM L₄) (hMne3 : LM ≠ L₃) (hMne4 : LM ≠ L₄) : i₄ = i₃ := by
  by_contra hne
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hM3i : iM ≠ i₃ := by
    intro e
    obtain ⟨L'', hL'', hne', hcomm, huniq⟩ := IsFundamental.exists_twin hodd h₃
    have hM' : IsFundamental (quadMinus 6 F b c) LM i₃ := e ▸ hM
    rcases huniq LM hM' with e' | e'
    · exact hMne3 e'
    · exact not_commutes_twin_of_adj hodd h₂ h₃ hM' hne23 hMne3 hnc23 (commutes_symm hM3)
        (commutes_symm hM2)
  have hM4i : iM ≠ i₄ := by
    intro e
    obtain ⟨L'', hL'', hne', hcomm, huniq⟩ := IsFundamental.exists_twin hodd h₄
    have hM' : IsFundamental (quadMinus 6 F b c) LM i₄ := e ▸ hM
    rcases huniq LM hM' with e' | e'
    · exact hMne4 e'
    · exact not_commutes_twin_of_adj hodd h₂ h₄ hM' hne24 hMne4 hnc24 (commutes_symm hM4)
        (commutes_symm hM2)
  obtain ⟨F₃, rfl, rfl⟩ := h₃
  obtain ⟨F₄, rfl, rfl⟩ := h₄
  obtain ⟨FM, rfl, rfl⟩ := hM
  have o34 := span_orth_of_commutes_ne hodd hc34 (fun e => hne e.symm)
  have o3M := span_orth_of_commutes_ne hodd (commutes_symm hM3) (fun e => hM3i e.symm)
  have o4M := span_orth_of_commutes_ne hodd (commutes_symm hM4) (fun e => hM4i e.symm)
  exact false_of_three_frames_minus hirr hodd F₃ F₄ FM o34 o3M o4M

end Six

end CFSG.ClassicalInvolution.RouteD.TwinSmall
