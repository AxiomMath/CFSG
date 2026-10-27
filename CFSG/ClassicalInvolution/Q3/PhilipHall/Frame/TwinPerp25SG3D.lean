module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3A

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Lifts

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem mem_member_of_mem_liftFam (hΦ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J)
    (hex : ExactSylow Φ) {M : Subgroup X} (hM : M ∈ liftFam Φ) {y : X} (hyM : y ∈ M)
    (hy4 : y * y * y * y = 1) : ∃ J ∈ Φ, y ∈ J := by
  obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
  have hJs := isSylow2In_of_le_liftFam hΦ hJ (h2 J hJ) hM hJM
  have h4 : y ^ 4 = 1 := by
    calc y ^ 4 = y * y * y * y := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := hy4
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (by simpa using orderOf_dvd_of_pow_eq_one h4 : orderOf y ∣ 2 ^ 2)
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hio])
  obtain ⟨V, hV, hyV⟩ := IsSylow2In.exists_ge hy2 (Subgroup.zpowers_le.mpr hyM)
  have hVJ : V = J := hex M hM V J hV hJs
  exact ⟨J, hJ, hVJ ▸ hyV (Subgroup.mem_zpowers y)⟩

end Lifts

section Lie

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem liftFam_conj (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) :
    ∀ J ∈ liftFam (TwinDisc.secFam Ω a),
      ∀ y : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a),
        conjSub y J ∈ liftFam (TwinDisc.secFam Ω a) :=
  fun J hJ y => conjInvariant_liftFam (layer_q8Section hyp ha2).hyp.conjInvariant y J hJ

theorem orderOf_eq_four_of {X : Type} [Group X] {y : X} (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1) :
    orderOf y = 4 := by
  have h4 : y ^ 2 ^ (1 + 1) = 1 := by
    have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
    rw [this]
    exact hy4
  have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  simpa using this

theorem layerSq_of_ae5 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hAE : AE5SqModel) (h5 : LayerAE5 Ω a) : LayerSq Ω a := by
  obtain ⟨I, hI⟩ := h5
  exact hAE _ _ (layer_q8Section hyp ha2) I hI

end Lie

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
