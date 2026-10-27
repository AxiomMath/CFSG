module

public import CFSG.ClassicalInvolution.Balance.BootstrapDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapMember
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isQuasisimple_of_deltaCore_eq_bot_layer {C K F : Subgroup G} (hKC : IsSubnormal K C)
    (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hF : IsElemAbelian 2 F) (hFC : F ≤ C) (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hΔ : deltaCore F = ⊥) (hsub : IsSubnormal K (C ⊓ Subgroup.centralizer (F : Set G)))
    (hB : ∀ f ∈ F, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f K⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaCore_eq_bot hKC hKperf hKq hKF hΔ fun f hf hf1 =>
    commutator_oddCoreIn_normalClosureIn_le_of_l2PrimeBalance l2PrimeBalance hF hf hFC
      (le_inf (isSubnormal_le hKC) hKF) hsub hKperf hKq (hB f hf hf1)

theorem exactMembers_of_deltaCore_eq_bot [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K : Subgroup G} {z : G} (hKΩ : K ∈ Ω) (hz : IsClassicalMember p f K z) {F : Subgroup G}
    (hF : IsElemAbelian 2 F) (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hΔ : deltaCore F = ⊥) : ExactMembers Ω := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hW : WeakMember (GaloisField p f) K z :=
    ⟨hz.orderOf_eq_two, hz.mem, hz.perfect, hz.subnormal, hz.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hzF : ∀ x ∈ F, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hKF hz.mem) x hx).symm
  have hFC : F ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzF x hx).symm
  have hsub : IsSubnormal K (C ⊓ Subgroup.centralizer (F : Set G)) := by
    have h := isSubnormal_inf hz.subnormal (C ⊓ Subgroup.centralizer (F : Set G))
    rwa [inf_eq_left.mpr (le_inf (isSubnormal_le hz.subnormal) hKF),
      inf_eq_right.mpr inf_le_left] at h
  have hq' : CFSG.Open.IsQuasisimple K := by
    refine isQuasisimple_of_deltaCore_eq_bot_layer hz.subnormal hmem.perfect hmem.quasisimple hF
      hFC hKF hΔ hsub ?_
    intro f₀ hf₀ hf₀1 M hM
    exact hB_of_localLieSystems hp2 h0 hA1 hΩ hIH hKΩ hz.isCentralInvolution
      (not_subset_center_of_ne_one hnab hf₀1)
      (hKF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₀))) (hzF f₀ hf₀) M hM
  exact exactMembers_of_isQuasisimple hp2 hf h9 hΩ hsingle hKΩ hq'

theorem exactMembers_of_centralizer_generated [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) {K : Subgroup G} {z : G}
    (hKΩ : K ∈ Ω) (hz : IsClassicalMember p f K z) (hKA : K ≤ Subgroup.centralizer (A : Set G))
    (hS : CentralizedDelta A) (h2 : TwoBalancedWrt A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) :
    ExactMembers Ω := by
  obtain ⟨F, hF⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2 Nat.prime_two A
    hA (by simpa using h4)
  obtain ⟨f₀, hf₀, hf₀1⟩ := exists_ne_one_of_card_eq_two_pow (by norm_num) hF.2
  have hΔ := deltaCore_eq_bot_of_four_centralizer_generated
    (componentClassificationOddCore_eq_bot_of_simple hnab) ⟨f₀, hF.1 hf₀, hf₀1⟩ hS h2 hgen F hF
  exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH hKΩ hz
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hF.1)
    (hKA.trans (Subgroup.centralizer_le hF.1)) hΔ

end CFSG.ClassicalInvolution.Balance.Bootstrap
