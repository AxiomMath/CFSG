module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Abstract

variable {X : Type} [Group X]

@[expose] def OddEC (t : X) : Prop :=
  ∃ N : Subgroup X, N ≤ Subgroup.centralizer ({t} : Set X) ∧ Odd (Nat.card N) ∧
    (∀ g ∈ Subgroup.centralizer ({t} : Set X), ∀ m ∈ N, g * m * g⁻¹ ∈ N) ∧
    ∀ g ∈ Subgroup.centralizer ({t} : Set X), Odd (orderOf g) → g ∈ N

@[expose] def NoCentFour (K : Subgroup X) (t : X) : Prop :=
  ∀ g : X, g * t * g⁻¹ ≠ t → ∀ k ∈ K, orderOf k = 4 → (g * t * g⁻¹) * k ≠ k * (g * t * g⁻¹)

variable [Finite X]

theorem exists_pow_two_pow_eq_one {C : Subgroup X} (h : ∀ g ∈ C, Odd (orderOf g) → g = 1) {g : X}
    (hg : g ∈ C) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hpos : 0 < 2 ^ a := by positivity
  have hord' : orderOf (g ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd hpos.ne' ⟨m, hord⟩, hord, Nat.mul_div_cancel_left m hpos]
  exact ⟨a, h _ (C.pow_mem hg _) (by rw [hord']; exact hm)⟩

theorem OddEC.two_power {t : X} (hEC : OddEC t)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set X)) = ⊥) :
    ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨N, hNC, hNodd, hNnorm, hNall⟩ := hEC
  have hNle : N ≤ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set X)) := by
    refine Balance.le_oddCoreIn_of_normalizes hNC ?_ hNodd
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · exact hNnorm g hg m hm
    · have := hNnorm g⁻¹ (inv_mem hg) _ hm
      simpa [mul_assoc] using this
  rw [hO, le_bot_iff] at hNle
  have h1 : ∀ g ∈ Subgroup.centralizer ({t} : Set X), Odd (orderOf g) → g = 1 := by
    intro g hg ho
    have := hNall g hg ho
    rw [hNle] at this
    exact Subgroup.mem_bot.mp this
  intro g hg
  exact exists_pow_two_pow_eq_one h1 (Subgroup.mem_centralizer_singleton_iff.mpr hg)

theorem OddEC.two_power_of_mem_normal {t : X} (hEC : OddEC t) (hO : classicalInvolutionOddCore X = ⊥)
    {P : Subgroup X} (hPn : P.Normal) (hP : IsPGroup 2 P) (htP : t ∈ P) :
    ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1 :=
  hEC.two_power (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal
    hO hPn hP htP)

theorem isPGroup_centralizer_of_two_power {t : X}
    (h : ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.centralizer ({t} : Set X)) := by
  intro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := h g (Subgroup.mem_centralizer_singleton_iff.mp hg)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

end Abstract

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
