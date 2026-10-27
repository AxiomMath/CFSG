module

public import CFSG.ClassicalInvolution.Asc77.AscT7TInv
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Basic

variable {G : Type} [Group G]

theorem eq_one_of_mem_isPGroup_of_mem_odd [Finite G] {R N : Subgroup G} (hR : IsPGroup 2 R)
    (hN : Odd (Nat.card N)) {x : G} (hxR : x ∈ R) (hxN : x ∈ N) : x = 1 := by
  have h2 : IsPGroup 2 (R ⊓ N : Subgroup G) := hR.to_le inf_le_left
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdvd : Nat.card ↥(R ⊓ N) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have hodd : Odd (Nat.card ↥(R ⊓ N)) := hN.of_dvd_nat hdvd
  have hn0 : n = 0 := by
    rcases n with _ | n
    · rfl
    · exfalso
      rw [hn] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (by simp [pow_succ])
  have hcard : Nat.card ↥(R ⊓ N) = 1 := by rw [hn, hn0]; simp
  have hbot : (R ⊓ N : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  have hx : x ∈ R ⊓ N := ⟨hxR, hxN⟩
  rw [hbot] at hx
  simpa using hx

end Basic

section Fusion

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


theorem conjSub_pair_of_central (hs : Hyp23Setting p f Ω K K' z) {c : G}
    (hc : c * z * c⁻¹ = z) :
    (conjSub c K = K ∧ conjSub c K' = K') ∨ (conjSub c K = K' ∧ conjSub c K' = K) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hKc : conjSub c K = K ∨ conjSub c K = K' := by
    have hmem : conjSub c K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K hs.stand.mem, z, hz, by simpa [hc] using hz.conj c⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hK'c : conjSub c K' = K ∨ conjSub c K' = K' := by
    have hmem : conjSub c K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K' hs.hK'.1, z, hz, by simpa [hc] using hz'.conj c⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hne : conjSub c K ≠ conjSub c K' := fun h => hs.hne (conjSub_injective c h).symm
  rcases hKc with h1 | h1 <;> rcases hK'c with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem trivialOnQuot_pair_conj (hs : Hyp23Setting p f Ω K K' z) {a c : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K') (hc : c * z * c⁻¹ = z) :
    c * a * c⁻¹ ∈ trivialOnQuot K ∧ c * a * c⁻¹ ∈ trivialOnQuot K' := by
  have h1 := trivialOnQuot_conjSub haK c
  have h2 := trivialOnQuot_conjSub haK' c
  rcases conjSub_pair_of_central hs hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h1, h2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h2, h1⟩

variable {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}

theorem conjSub_R_eq_of_mem_normalizer (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : s ∈ Subgroup.normalizer (K : Set G)) :
    conjSub s R = R := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  rcases T7T.perm_R_of_hyp hyp hsS (Or.inl rfl : R = R ∨ R = R') with h | h
  · exact h
  · exfalso
    have hsK' : conjSub s K = K := mem_normalizer_iff_conjSub_eq.mp hsK
    have hR'K : R' ≤ K := by
      rw [← h, ← hsK']
      exact conjSub_mono hyp.hR.2.1
    have hR'2 : IsPGroup 2 R' := S.isPGroup'.to_le hyp.hR'.2.2
    have h1 := hΩ.card_le_two_of_le_inf hs.stand.mem hs.hK'.1 hs.hne.symm hR'2 hR'K hyp.hR'.2.1
    have h2 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR'.1).eight_le
    omega

theorem conjSub_R'_eq_of_mem_normalizer (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : s ∈ Subgroup.normalizer (K' : Set G)) :
    conjSub s R' = R' := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  rcases T7T.perm_R_of_hyp hyp hsS (Or.inr rfl : R' = R ∨ R' = R') with h | h
  · exfalso
    have hsK' : conjSub s K' = K' := mem_normalizer_iff_conjSub_eq.mp hsK
    have hRK' : R ≤ K' := by
      rw [← h, ← hsK']
      exact conjSub_mono hyp.hR'.2.1
    have hR2 : IsPGroup 2 R := S.isPGroup'.to_le hyp.hR.2.2
    have h1 := hΩ.card_le_two_of_le_inf hs.stand.mem hs.hK'.1 hs.hne.symm hR2 hyp.hR.2.1 hRK'
    have h2 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
    omega
  · exact h

theorem comm_of_normalizes_of_trivialOnQuot {M T : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ M)
    {s : G} (hsM : s ∈ trivialOnQuot M) (hsT : conjSub s T = T) {r : G} (hr : r ∈ T) :
    s * r = r * s := by
  have hrT : s * r * s⁻¹ ∈ T := by
    rw [← hsT]
    exact conj_mem_conjSub hr
  have hcomm : ⁅s, r⁆ ∈ T := by
    have : ⁅s, r⁆ = (s * r * s⁻¹) * r⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact T.mul_mem hrT (T.inv_mem hr)
  have hodd : ⁅s, r⁆ ∈ oddCoreIn M := hsM.2 r (hTM hr)
  have h1 := eq_one_of_mem_isPGroup_of_mem_odd hT2 (odd_card_oddCoreIn M) hcomm hodd
  have h2 : s * r * s⁻¹ * r⁻¹ = 1 := by
    simpa [commutatorElement_def] using h1
  calc s * r = (s * r * s⁻¹ * r⁻¹) * (r * s) := by group
    _ = r * s := by rw [h2, one_mul]

theorem conj_mem_Csub (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a c : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K') (hc : c * z * c⁻¹ = z)
    (hcaS : c * a * c⁻¹ ∈ (S : Subgroup G)) :
    c * a * c⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  obtain ⟨h1, h2⟩ := trivialOnQuot_pair_conj hs haK haK' hc
  refine ⟨hcaS, ?_⟩
  have hR : R ≤ Subgroup.centralizer ({c * a * c⁻¹} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_normalizes_of_trivialOnQuot (S.isPGroup'.to_le hyp.hR.2.2) hyp.hR.2.1 h1
        (conjSub_R_eq_of_mem_normalizer hyp hcaS h1.1) hr).symm
  have hR' : R' ≤ Subgroup.centralizer ({c * a * c⁻¹} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_normalizes_of_trivialOnQuot (S.isPGroup'.to_le hyp.hR'.2.2) hyp.hR'.2.1 h2
        (conjSub_R'_eq_of_mem_normalizer hyp hcaS h2.1) hr).symm
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (sup_le hR hR' hx)

end Fusion

end C25Y

end CFSG.ClassicalInvolution.Asc77
