module

public import CFSG.ClassicalInvolution.Asc77.AscT3YPsi
public import CFSG.ClassicalInvolution.Asc77.AscT3WInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.y_S_norm_X (d : Std20 p f K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) {g : G} (hg : g ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    s * g * s⁻¹ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins
    (d.hSz hs)) g).mp hg

theorem Std20.y_cases (d : Std20 p f K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    s ∈ Subgroup.normalizer (K : Set G) ∨ conjSub s K = K' := by
  rcases d.late_conj_K (d.hSz hs) with h | h
  · exact Or.inl (mem_normalizer_iff_conjSub_eq.mpr h)
  · exact Or.inr h

theorem Std20.y_cyc_of_swapComm (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (hsw : ∀ n ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G), ∀ w ∈ (S : Subgroup G),
      w ∉ Subgroup.normalizer (K : Set G) →
        ⁅n, w⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
      ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  intro x hx y hy
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  by_cases hxN : x ∈ Subgroup.normalizer (K : Set G) <;>
    by_cases hyN : y ∈ Subgroup.normalizer (K : Set G)
  · exact d.y_comm_T c3 c8 ⟨hx, hxN⟩ ⟨hy, hyN⟩
  · exact hsw x ⟨hx, hxN⟩ y hy hyN
  · rw [← commutatorElement_inv]
    exact X.inv_mem (hsw y ⟨hy, hyN⟩ x hx hxN)
  · have hxK : conjSub x K = K' := (d.y_cases hx).resolve_left hxN
    have hyK : conjSub y K = K' := (d.y_cases hy).resolve_left hyN
    have hzN : x⁻¹ * y ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hyK, ← hxK, conjSub_inv_conjSub]
    have hzS : x⁻¹ * y ∈ (S : Subgroup G) := S.mul_mem (S.inv_mem hx) hy
    have h1 := hsw (x⁻¹ * y) ⟨hzS, hzN⟩ x hx hxN
    have h2 : ⁅x, y⁆ = x * ⁅x, x⁻¹ * y⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    have h3 : ⁅x, x⁻¹ * y⁆ ∈ X := by
      rw [← commutatorElement_inv]
      exact X.inv_mem h1
    exact d.y_S_norm_X hx h3

theorem Std20.y_T_norm (d : Std20 p f K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) :
    s * x * s⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) := by
  have hxK : conjSub x K = K := mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp hx).2
  have hxS : x ∈ (S : Subgroup G) := (Subgroup.mem_inf.mp hx).1
  have hxK' : conjSub x K' = K' := (d.late_conj_iff (d.hSz hxS)).mp hxK
  refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), ?_⟩
  rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul]
  rcases d.y_cases (S.inv_mem hs) with hsiN | hsiK
  · have h1 : conjSub s⁻¹ K = K := mem_normalizer_iff_conjSub_eq.mp hsiN
    have h2 : conjSub s K = K := by
      have := congrArg (conjSub s) h1
      rw [conjSub_conjSub_inv] at this
      exact this.symm
    rw [h1, hxK, h2]
  · have h2 : conjSub s K' = K := by
      have := congrArg (conjSub s) hsiK
      rw [conjSub_conjSub_inv] at this
      exact this.symm
    rw [hsiK, hxK', h2]

theorem Std20.y_swapComm_of_sq (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (hsq : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G),
      x * x ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∀ n ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G), ∀ w ∈ (S : Subgroup G),
      w ∉ Subgroup.normalizer (K : Set G) →
        ⁅n, w⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  intro n hn w hw _
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hx' : w * n * w⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) :=
    d.y_T_norm hw hn
  have h0 : ⁅n, w⁆ = n * (w * n * w⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  by_cases hnX : n ∈ X
  · rw [h0]
    have : (w * n * w⁻¹)⁻¹ = w * n⁻¹ * w⁻¹ := by group
    rw [this]
    exact X.mul_mem hnX (d.y_S_norm_X hw (X.inv_mem hnX))
  · have hx'X : w * n * w⁻¹ ∉ X := by
      intro h
      apply hnX
      have := d.y_S_norm_X (S.inv_mem hw) h
      simpa [mul_assoc] using this
    have h1 := d.y_psi_eq c3 c8 hsq hn hx' hnX hx'X
    have h2 : (w * n * w⁻¹)⁻¹ * n ∈ X := by
      have := X.inv_mem h1
      simpa [mul_assoc] using this
    have h3 := d.y_S_norm_X hn.1 h2
    have e : n * ((w * n * w⁻¹)⁻¹ * n) * n⁻¹ = ⁅n, w⁆ := by
      rw [h0]
      group
    rw [← e]
    exact h3

end Std

section Props

variable (p f : ℕ) [Fact p.Prime]


@[expose] def SwapComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∀ n ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G), ∀ w ∈ (S : Subgroup G),
            w ∉ Subgroup.normalizer (K : Set G) →
              ⁅n, w⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K'

theorem res10aCyc_of_swapComm (h : SwapComm p f) : Res10aCyc p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb
  exact d.y_cyc_of_swapComm c3 c8 (h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8)

theorem swapComm_of_res10aCyc (h : Res10aCyc p f) : SwapComm p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 n hn w hw _
  obtain ⟨b, hb⟩ := res10aInv'_proved p f G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  exact h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb n (Subgroup.mem_inf.mp hn).1 w hw

theorem res10aCyc_of_two_mod_four (hf : f % 4 = 2) : Res10aCyc p f := by
  refine res10aCyc_of_swapComm p f ?_
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  exact d.y_swapComm_of_sq c3 c8 (fun x hx => d.y_sq_mem_X c3 c8 hf hx)

end Props

end CFSG.ClassicalInvolution.Asc77.T3CII
