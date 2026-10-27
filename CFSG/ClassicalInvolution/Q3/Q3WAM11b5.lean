module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11b3
public import CFSG.ClassicalInvolution.Q3.Q3WASTAsm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)


section Pair

variable {X : Type} [Group X]

theorem dvd_card_linear_pair {W U V : Subgroup X}
    (h : LinearBlockStandardPair (GaloisField 3 1) W U V) : 27 ∣ Nat.card W := by
  obtain ⟨θ, hrange, hker, -, -⟩ := WeakCT.pair_normalize h
  have hker' : θ.ker = ⊥ :=
    le_bot_iff.mp (hker.trans (Asc77.T3CII.center_sl3_eq_bot card_gf3).le)
  have h1 := Gaps.card_eq_range_mul_ker θ
  rw [hker', Subgroup.card_bot, mul_one, hrange] at h1
  rw [← h1, Gaps.card_SL_three, card_gf3]
  exact ⟨8 * 26, by norm_num⟩

theorem dvd_card_unitary_pair {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W U V) : 27 ∣ Nat.card W := by
  obtain ⟨θ, hrange, hker, -, -⟩ := Phan.pair_normalize h
  have hK9 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hker' : θ.ker = ⊥ := le_bot_iff.mp (hker.trans
    (Asc77.T3CII.center_su3_eq_bot (p := 3) (f := 1) hK9 (by norm_num)).le)
  have h1 := Gaps.card_eq_range_mul_ker θ
  rw [hker', Subgroup.card_bot, mul_one, hrange] at h1
  rw [← h1, Gaps.card_Su_three (p := 3) (f := 1) hK9]
  exact ⟨8 * 28, by norm_num⟩

theorem dvd_card_sup_of_pair {U V : Subgroup X}
    (h : (∃ W, LinearBlockStandardPair (GaloisField 3 1) W U V) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W U V) :
    27 ∣ Nat.card ↥(U ⊔ V) := by
  rcases h with ⟨W, hW⟩ | ⟨W, hW⟩
  · rw [← Gaps.linear_eq_sup hW]
    exact dvd_card_linear_pair hW
  · have hK9 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 2 (by norm_num)]
      norm_num
    rw [← Gaps.unitary_eq_sup hK9 (by norm_num) hW]
    exact dvd_card_unitary_pair hW

end Pair

section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem card_eq_locImg_mul {H : Subgroup G} (hH : H ≤ locLayer Ω x) :
    ∃ k : ℕ, Nat.card ↥H = Nat.card ↥(locImg Ω x H) * k ∧
      k ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x)) := by
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup ↥(locLayer Ω x), H' = H.subgroupOf (locLayer Ω x) :=
    ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥H' →* locQuot Ω x, θ =
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).comp H'.subtype :=
    ⟨_, rfl⟩
  have h1 := Gaps.card_eq_range_mul_ker θ
  have hrange : θ.range = locImg Ω x H := by
    rw [hθ, hH']
    unfold locImg
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardH : Nat.card ↥H' = Nat.card ↥H := by
    rw [hH']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  refine ⟨Nat.card θ.ker, ?_, ?_⟩
  · rw [← hcardH, h1, hrange]
  · have hθapp : ∀ y : ↥H', θ y = (QuotientGroup.mk (y : ↥(locLayer Ω x)) :
        locQuot Ω x) := fun y => by rw [hθ]; rfl
    have hmem : ∀ k : θ.ker, ((k : ↥H') : ↥(locLayer Ω x)) ∈
        classicalInvolutionOddCore ↥(locLayer Ω x) := by
      intro k
      have hk : θ (k : ↥H') = 1 := k.2
      rw [hθapp] at hk
      exact (QuotientGroup.eq_one_iff ((k : ↥H') : ↥(locLayer Ω x))).mp hk
    let f : θ.ker →* classicalInvolutionOddCore ↥(locLayer Ω x) :=
      MonoidHom.codRestrict ((H'.subtype).comp θ.ker.subtype) _ hmem
    have hf : Function.Injective f := by
      intro a b hab
      have h' := congrArg (fun y : classicalInvolutionOddCore ↥(locLayer Ω x) =>
        (y : ↥(locLayer Ω x))) hab
      exact Subtype.ext (Subtype.ext h')
    exact Subgroup.card_dvd_of_injective f hf

theorem M11Pic.not_dvd_sup (c : LocOK Ω x) (P : M11Pic Ω x) {K β : Subgroup G}
    (hK : K ∈ compMembers3 Ω x P.D P.i₁) (hβ : β ∈ compMembers3 Ω x P.D P.i₁) :
    ¬ 27 ∣ Nat.card ↥(K ⊔ β) := by
  intro h27
  have hH : K ⊔ β ≤ locLayer Ω x :=
    sup_le (le_centralizingLayer hK.1) (le_centralizingLayer hβ.1)
  obtain ⟨k, hk, hkO⟩ := card_eq_locImg_mul (Ω := Ω) (x := x) hH
  have hcop : Nat.Coprime 27 k := by
    have h3k : ¬ 3 ∣ k := fun h => c.hO3 (h.trans hkO)
    have h3 : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3k
    simpa using Nat.Coprime.pow_left 3 h3
  have h27' : 27 ∣ Nat.card ↥(locImg Ω x (K ⊔ β)) := by
    rw [hk] at h27
    exact hcop.dvd_of_dvd_mul_right h27
  have hle : locImg Ω x (K ⊔ β) ≤ (P.D.hom P.i₁).range := by
    rw [locImg_sup3 (le_centralizingLayer hK.1) (le_centralizingLayer hβ.1)]
    exact sup_le hK.2 hβ.2
  have h7920 : Nat.card ↥(locImg Ω x (K ⊔ β)) ∣ 7920 := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Gaps.card_eq_range_mul_ker (P.D.hom P.i₁)
    rw [m11_card_gen P.k₁] at h2
    exact h1.trans (Dvd.intro _ h2.symm)
  have := h27'.trans h7920
  norm_num at this

theorem M11Pic.false_of_std_pair (c : LocOK Ω x) (P : M11Pic Ω x) {K β : Subgroup G}
    (hK : K ∈ compMembers3 Ω x P.D P.i₁) (hβ : β ∈ compMembers3 Ω x P.D P.i₁) {y : G}
    (hKy : K ∈ centralizingMembers Ω {y}) (hβy : β ∈ centralizingMembers Ω {y})
    (h : (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω y K) (locImg Ω y β)) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω y K) (locImg Ω y β)) :
    False := by
  have h27 := dvd_card_sup_of_pair h
  rw [← locImg_sup3 (le_centralizingLayer hKy) (le_centralizingLayer hβy)] at h27
  obtain ⟨k, hk, -⟩ := card_eq_locImg_mul (Ω := Ω) (x := y)
    (sup_le (le_centralizingLayer hKy) (le_centralizingLayer hβy))
  exact P.not_dvd_sup c hK hβ (h27.trans (Dvd.intro _ hk.symm))

end Local

end CFSG.ClassicalInvolution.Q3.Q3W
