module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwistedFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ClassLeaves

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section LangPilot

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false



theorem langToralOrParabolic_of_langToralPlane {τ : Tag}
    (h : LangToralPlane τ 3) : LangToralOrParabolic τ := by
  intro K _ _ hK A hA hcard
  left
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := h K hK A hA hcard
  exact ⟨⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩⟩

theorem normalizesRNative_of_unip {τ : Tag} {K : Type} [Field K] {A : Subgroup (adjointGroup τ K)}
    (h : ∃ u : adjointGroup τ K, u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      ∀ x ∈ A, Commute u x) :
    NormalizesRNative τ K A := by
  obtain ⟨u, hu1, ⟨n, hn⟩, hc⟩ := h
  refine ⟨Subgroup.zpowers u, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
      one_zpow]
    rfl
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcomm : ∀ h' ∈ Subgroup.zpowers u, x * h' * x⁻¹ = h' := by
      intro h' hh'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh'
      rw [mul_inv_eq_iff_eq_mul]
      exact ((hc x hx).symm.zpow_right m).eq
    have hcomm2 : ∀ h' ∈ Subgroup.zpowers u, x⁻¹ * h' * x = h' := by
      intro h' hh'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh'
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact ((hc x hx).symm.zpow_right m).eq.symm
    constructor
    · intro hh
      rw [hcomm h hh]
      exact hh
    · intro hh
      have h2 := hcomm2 _ hh
      rw [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at h2
      rwa [← h2] at hh

@[expose] def F4RegularPure (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε → 3 ≤ Nat.card K →
    ∃ z : adjointGroup .F4 K, (∃ X : Subgroup (adjointGroup .F4 K), ClosingFrameAt z X) ∧
      ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        ∀ D : LangPlaneData .F4 K E₀, (∀ α, IsRoot .F4 α → ¬ D.Kills α) →
          ∀ e ∈ E₀, e ≠ 1 → ∃ g : adjointGroup .F4 K, g * e * g⁻¹ = z

theorem f4RegularPure_one_of_pure (h : F4PureSplit) : F4RegularPure 1 := by
  intro K _ _ hres hK3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    have := Nat.card_pos (α := K)
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  obtain ⟨-, -, X, hX⟩ := f4SplitFrame_of K hres ω hω
  exact ⟨zSplit K ω, ⟨X, hX⟩, fun E₀ hexp hcard D hreg e he he1 =>
    h K hres ω hω E₀ hexp hcard D hreg e he he1⟩

theorem f4RegularPure_two_of_pure
    (h : F4PureTwisted) : F4RegularPure 2 := by
  intro K _ _ hres hK3
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag K TwClass.f4Six.w
    (TwClass.w_theta TwClass.f4Six)
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
  obtain ⟨z, hzbc, -, -, X, hX⟩ := f4TwistedFrame_of K hres hK3 D₁ ω hω
  exact ⟨z, ⟨X, hX⟩, fun E₀ hexp hcard D hreg e he he1 =>
    h K hres hK3 D₁ ω hω z hzbc E₀ hexp hcard D hreg e he he1⟩

theorem f4ThreeNative_of_pilot {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (htor : LangToralOrParabolic .F4) (hNR : LangPlaneKillsRoot .F4)
    (h1 : F4RegularPure ε) (h2 : F4RegularSolvable ε) (h3 : ε = 2 → F4ThreeTwo) :
    F4ThreeNative ε := by
  intro K _ _ hres E₀ hexp hcard hn
  by_cases hK2 : Nat.card K = 2
  · exact h3 (by omega) K hK2 E₀ hexp hcard hn
  · have hK3 : 3 ≤ Nat.card K := by
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    have hnd : ¬ 3 ∣ Nat.card K := by omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases htor K hnd E₀ hexp hcard with ⟨⟨D⟩⟩ | hnorm
    · have hreg : ∀ α, IsRoot .F4 α → ¬ D.Kills α := fun α hα hk =>
        hn (normalizesRNative_of_unip (hNR K E₀ D α hα hk))
      obtain ⟨a, ha, b, hb, ha1, hb1, hgen⟩ := exists_gens_of_plane (p := 3) hexp hcard
      obtain ⟨z, ⟨X, hX⟩, hpure⟩ := h1 K hres hK3
      obtain ⟨ga, hga⟩ := hpure E₀ hexp hcard D hreg a ha ha1
      obtain ⟨gb, hgb⟩ := hpure E₀ hexp hcard D hreg b hb hb1
      have hXa : ClosingFrameAt a (X.map (MulAut.conj ga⁻¹).toMonoidHom) := by
        have := hX.conj ga⁻¹
        rwa [show ga⁻¹ * z * ga⁻¹⁻¹ = a by rw [← hga]; group] at this
      have hXb : ClosingFrameAt b (X.map (MulAut.conj gb⁻¹).toMonoidHom) := by
        have := hX.conj gb⁻¹
        rwa [show gb⁻¹ * z * gb⁻¹⁻¹ = b by rw [← hgb]; group] at this
      exact planeCl_eq_top_of_closingFrames ha hb ha1 hb1 hgen hXa hXb
        (h2 K hres E₀ hexp hcard D hreg)
    · exact absurd hnorm hn

end LangPilot

end CFSG.LieType.SeitzGeneration.ExcHighThree
