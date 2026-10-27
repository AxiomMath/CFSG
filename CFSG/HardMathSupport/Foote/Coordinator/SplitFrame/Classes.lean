module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Native
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.TauCetiBridge TauCeti
open scoped MatrixGroups


theorem seitzExcAnisotropicF4Class_three_of_frame
    (hC : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      FrameClosing .F4 K (cosetRoots .F4 1 3))
    (hN : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      FrameNormalizerSolvable .F4 K (cosetRoots .F4 1 3)) :
    SeitzExcAnisotropicF4Class 3 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, hX, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have : Fintype K := Fintype.ofFinite K
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    have h2 := q.prime_p.two_le
    have he := q.exponent_pos
    by_contra hlt
    push Not at hlt
    have hle : q.p ^ q.exponent ≤ 2 := by omega
    have h1 : q.exponent = 1 := by
      by_contra hne
      have : q.p ^ 2 ≤ q.p ^ q.exponent := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    have hp2 : q.p = 2 := by
      rw [h1, pow_one] at hle
      omega
    exact hX ⟨hp2, h1⟩
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [hKq]; exact hord
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_F4 K (exists_splitFrame_F4 K) (hC K hK3) (hN K hK3) hp hp5 hordK
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hordK) hg) E₀ hE₀p hE₀c

theorem seitzExcAnisotropicE8Class_five_of_frame
    (hC : ∀ (K : Type) [Field K] [Finite K], FrameClosing .E8 K (cosetRoots .E8 4 5))
    (hN : ∀ (K : Type) [Field K] [Finite K], FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5)) :
    SeitzExcAnisotropicE8Class 5 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨-, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fintype K := Fintype.ofFinite K
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 5 := by rw [hKq]; exact hord
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_E8 K (exists_splitFrame_E8 K) (hC K) (hN K) hp hordK
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hordK) hg) E₀ hE₀p hE₀c

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
