module

public import CFSG.ClassicalInvolution.Asc77.AscC22P16
public import CFSG.ClassicalInvolution.Asc77.AscC22P14

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace C22P

set_option linter.unusedSectionVars false

section Proved

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem mem_tqMembers_of_twin (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') : M ∈ tqMembers Ω (u₁ * u₂) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet hs.hz hM
  have h1 : u₁ ∈ trivialOnQuot M :=
    T7J.twin_le_trivialOnQuot hΩ hs.stand.mem hM.1 (Ne.symm hMK) hs.hz hzM hs.hu₁.1
  have h2 : u₂ ∈ trivialOnQuot M :=
    T7J.twin_le_trivialOnQuot hΩ hs.hK'.1 hM.1 (Ne.symm hMK') hs.hzK' hzM hs.hu₂.1
  exact ⟨hM.1, Subgroup.mul_mem _ h1 h2⟩

theorem c22_gen_frame [IsSimpleGroup G] (hq1 : p ^ f % 4 = 1)
    (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W)
    (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    {R R' : Subgroup G} {b b' y : G} (hF : FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y) :
    rLayer Ω (u₁ * u₂) ≤
      (conjSub y K₄ ⊔ K₃ ⊔ conjSub y K₃ ⊔ K₄) ⊔ oddCoreOf (rLayer Ω (u₁ * u₂)) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hπ : piSign p f = true := by unfold piSign; simp [hq1]
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  have hrL : rLayer Ω u = exactLayer Ω u := rLayer_eq_exactLayer hp hq hΩ hu2
  obtain ⟨K₄', hK₄', -, -, -, hV'⟩ := fourTwins_S hs hW
  have hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄ := by
    intro M hM
    have hK₄eq : K₄ = K₄' := by
      rcases hV' K₄ hK₄ with h | h | h | h
      · exact absurd h h41
      · exact absurd h h42
      · exact absurd h h43
      · exact h
    rcases hV' M hM with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (h.trans hK₄eq.symm)))
  have hK₃t : K₃ ∈ tqMembers Ω u := mem_tqMembers_of_twin hs hs.hK₃ hs.hK₃K hs.hK₃K'
  have hK₄t : K₄ ∈ tqMembers Ω u := mem_tqMembers_of_twin hs hK₄ h41 h42
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u hF.hy
  have hJt : conjSub y K₃ ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₃t
  have hJ't : conjSub y K₄ ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₄t
  have hu₂K : u₂ ∈ trivialOnQuot K :=
    T7J.twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hz hs.hu₂.1
  have hu₁K' : u₁ ∈ trivialOnQuot K' :=
    T7J.twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hz hzK' hs.hu₁.1
  have hnotK : K ∉ tqMembers Ω u :=
    T7J.not_mem_tqMembers_of_mul hp hq hΩ hKΩ hz hs.hu₁.1 hs.hu₁.2 hu₂K hu
  have hnotK' : K' ∉ tqMembers Ω u :=
    T7J.not_mem_tqMembers_of_mul hp hq hΩ hK'Ω hzK' hs.hu₂.1 hs.hu₂.2 hu₁K'
      (by rw [hu]; exact hs.comm₁₂)
  have hperp : ∀ J ∈ tqMembers Ω u, J ∈ KPerp Ω K₃ → J = K₃ ∨ J = K₄ := by
    intro J hJt₀ hJperp
    rw [T7S22.perp_of_twin hs hs.hK₃, twinSet_eq_of_mem_twinSet hz hs.hK₃] at hJperp
    rcases hV J hJperp with h | h | h | h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK'
    · exact Or.inl h
    · exact Or.inr h
  have hex₃ : IsSylow2In R (exactCore u K₃) :=
    (isSylow2In_exactCore_iff hΩ hc2' hK₃Ω hK₃t.2).mpr ⟨hF.hR, hF.hRc⟩
  have hex₄ : IsSylow2In R' (exactCore u K₄) :=
    (isSylow2In_exactCore_iff hΩ hc2' hK₄Ω hK₄t.2).mpr ⟨hF.hR', hF.hR'c⟩
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  have hperp' : ∀ J ∈ tqMembers Ω u, J ∈ KPerp Ω K₄ → J = K₄ ∨ J = K₃ := by
    intro J hJt₀ hJperp
    rw [T7S22.perp_of_twin hs hK₄, twinSet_eq_of_mem_twinSet hz hK₄] at hJperp
    rcases hV J hJperp with h | h | h | h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK'
    · exact Or.inr h
    · exact Or.inl h
  have hBelow : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hMz : IsClassicalMember p f K₃ z := isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hu1 : u ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (exists_noncomm_of_isClassicalMember hMz) hu1
  have hLay : LayerOrthType p f Ω u 6 true := by
    have h := T7J.layer_orth_six_weak_proved hp hq hΩ hBelow hu2 hnc hK₃t hK₄t hJt hzK₃ hzK₄
      hperp hperp' htJ hF.hzt hF.htz hex₃ hex₄ hF.hRR' (hex₃.1 hF.hbR) (hex₄.1 hF.hb'R') hF.hbz
      hF.hb'z rfl
    rwa [hπ] at h
  have hgen := layer_gen hp hq hΩ hu2 hLay hK₃t hK₄t hJt hJ't hzK₃ hzK₄ hperp htJ htJ' hF.hzt
    hF.htz hex₃ hex₄ hF.hRR' (hex₃.1 hF.hbR) (hex₄.1 hF.hb'R') hF.hbz rfl hF.hy rfl rfl
  rw [hrL]
  exact hgen.trans (sup_le_sup_right le_sup_left _)

theorem c22_genY_proved : C22_genY p f := by
  intro hq1 G _ _ _ Ω K K' K₃ K₄ z u₁ u₂ u₃ hs hW _ hK₄ h41 h42 h43 R R' b b' y hF
  exact c22_gen_frame hq1 hs hW hK₄ h41 h42 h43 hF

end Proved

end C22P

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem c22_chainPos_proved : R31.C22_chainPos p f :=
  c22_chainPos_of_genY C22P.c22_genY_proved

end Final

end CFSG.ClassicalInvolution.Asc77
