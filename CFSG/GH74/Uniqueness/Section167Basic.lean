module

public import CFSG.GH74.Uniqueness.Section16Conf
public import CFSG.GH74.Uniqueness.Section5Prop53
public import CFSG.GH74.Uniqueness.Section12Theorem6

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.nonempty_conf16
    (S : ZDSetup X Z M) : Nonempty (Conf16 Z M) := by
  obtain ⟨t, ht, htM⟩ := S.exists_mem_not_mem
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  by_cases hodd : Odd (Nat.card ↥(M ⊓ conjugate M t))
  · exact (S.false_of_odd_card ht htM hodd).elim
  · exact S.exists_conf16 ⟨t, z, ht, htM, hz, hzM, Nat.not_odd_iff_even.mp hodd⟩

omit [Finite X] in
theorem card_conjugate_eq (Y : Subgroup X) (g : X) : Nat.card (conjugate Y g) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem IsMaxFixingThree.twoTransitive (hD : DoublyTransitive M) {p : ℕ} (hp : p.Prime)
    {W : Subgroup X} (hW : IsMaxFixingThree M p W) :
    ∀ a ∈ omegaFix M (W : Set X), ∀ b ∈ omegaFix M (W : Set X), a ≠ b →
      ∀ c ∈ omegaFix M (W : Set X), ∀ d ∈ omegaFix M (W : Set X), c ≠ d →
        ∃ n ∈ normalizer (W : Set X), conjugate a n = c ∧ conjugate b n = d := by
  have htwo : MulAction.IsMultiplyPretransitive X (omega M) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := hD a a.2 b b.2 (fun h => hab (Subtype.ext h)) c c.2 d d.2
      (fun h => hcd (Subtype.ext h))
    refine ⟨g⁻¹, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [omegaMulAction_smul_coe, inv_inv]
      exact hg1
    · rw [omegaMulAction_smul_coe, inv_inv]
      exact hg2
  have hmax : Maximal (fun U : Subgroup X => IsPGroup p U ∧
      2 < Nat.card {ω : omega M //
        ω ∈ CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) U}) W := by
    refine ⟨⟨hW.1.1, ?_⟩, fun Q hQ hle => hW.2 ⟨hQ.1, ?_⟩ hle⟩
    · rw [card_fixedPointsOfSubgroup_omega]
      exact hW.1.2
    · have := hQ.2
      rw [card_fixedPointsOfSubgroup_omega] at this
      exact this
  have h2 := CFSG.BenderSuzuki.chapter1_bender_normalizer_two_pretransitive hp htwo W hmax
  have hmem : ∀ γ (hγ : γ ∈ omegaFix M (W : Set X)),
      (⟨γ, hγ.1⟩ : omega M) ∈
        CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) W := by
    intro γ hγ x hx
    apply Subtype.ext
    show conjugate γ x⁻¹ = γ
    exact hγ.2 _ (W.inv_mem hx)
  intro a ha b hb hab c hc d hd hcd
  obtain ⟨f, hf1, hf2⟩ := h2 (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
    (fun h => hab (congrArg Subtype.val h)) (fun h => hcd (congrArg Subtype.val h))
  refine ⟨(f : X)⁻¹, (normalizer (W : Set X)).inv_mem f.2, ?_, ?_⟩
  · have := congrArg (fun γ : omega M => (γ : Subgroup X)) hf1
    simpa [omegaMulAction_smul_coe] using this
  · have := congrArg (fun γ : omega M => (γ : Subgroup X)) hf2
    simpa [omegaMulAction_smul_coe] using this

theorem ZDSetup.theorem4b_omega
    (S : ZDSetup X Z M) {s : X} (hs : s ∈ Z) {Y : Subgroup X}
    (hY : Odd (Nat.card Y)) (hsN : s ∈ normalizer (Y : Set X)) {β : Subgroup X}
    (hβ : β ∈ omega M) (hsβ : conjugate β s = β) (hYβ : Y ≤ β) :
    (∀ y ∈ Y, s * y = y * s) ∨ ∀ δ ∈ omegaFix M (Y : Set X), δ = β := by
  obtain ⟨g, rfl⟩ := hβ
  have hβΩ : conjugate M g ∈ omega M := ⟨g, rfl⟩
  have hsβ' : s ∈ conjugate M g := (S.prodDisc.conjugate_eq_iff_mem hβΩ).mp hsβ
  have hs₁ : g * s * g⁻¹ ∈ Z := by
    have := S.invariant.2 s hs g⁻¹
    rwa [inv_inv] at this
  have hs₁M : g * s * g⁻¹ ∈ M := by
    rwa [mem_conjugate_iff] at hsβ'
  have hY₁M : conjugate Y g⁻¹ ≤ M := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := hYβ hx
    rw [mem_conjugate_iff] at h1
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rwa [e] at h1
  have hsY : conjugate Y s = Y := conjugate_eq_iff_mem_normalizer.mpr hsN
  have hs₁N : g * s * g⁻¹ ∈ normalizer ((conjugate Y g⁻¹ : Subgroup X) : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, conjugate_conjugate]
    have e : g⁻¹ * (g * s * g⁻¹) = s * g⁻¹ := by group
    rw [e, ← conjugate_conjugate, hsY]
  have hodd₁ : Odd (Nat.card (conjugate Y g⁻¹)) := by
    rw [card_conjugate_eq]
    exact hY
  rcases S.theorem4.2 (g * s * g⁻¹) hs₁ hs₁M (conjugate Y g⁻¹) hodd₁ hY₁M hs₁N with h | h
  · left
    intro y hy
    have hyY : g * y * g⁻¹ ∈ conjugate Y g⁻¹ := by
      rw [mem_conjugate_iff]
      have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [e]
      exact hy
    have := h _ hyY
    have e : g * s * g⁻¹ * (g * y * g⁻¹) = g * (s * y) * g⁻¹ := by group
    have e' : g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
    rw [e, e'] at this
    have := mul_left_cancel (mul_right_cancel this)
    exact this
  · right
    intro δ hδ
    have hδ' : conjugate δ g⁻¹ ∈ omegaFix M ((conjugate Y g⁻¹ : Subgroup X) : Set X) := by
      rw [omegaFix_conjugate]
      exact ⟨δ, hδ, rfl⟩
    have := h _ hδ'
    have e : δ = conjugate (conjugate δ g⁻¹) g := by
      rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
    rw [e, this]

theorem le_of_isPGroup_of_normal_complement {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N₁ O R : Subgroup X} (hON : O ≤ N₁) (hOn : (O.subgroupOf N₁).Normal) {k : ℕ}
    (hk : Nat.card N₁ = Nat.card O * 2 ^ k) (hR : IsPGroup p R) (hRN : R ≤ N₁) : R ≤ O := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx
  let x' : ↥N₁ := ⟨x, hRN hx⟩
  have hOcard : Nat.card ↥(O.subgroupOf N₁) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv
  have hQcard : Nat.card (↥N₁ ⧸ O.subgroupOf N₁) = 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf N₁)
    rw [hk, hOcard] at h1
    have hpos : 0 < Nat.card O := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1, mul_comm])).symm
  have h1 : orderOf (QuotientGroup.mk x' : ↥N₁ ⧸ O.subgroupOf N₁) ∣ 2 ^ k := by
    rw [← hQcard]
    exact orderOf_dvd_natCard _
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hx⟩
  have hxm : orderOf x' = p ^ m := by
    have : orderOf x' = orderOf (⟨x, hx⟩ : ↥R) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥R)]
    rw [this, hm]
  have h2 : orderOf (QuotientGroup.mk x' : ↥N₁ ⧸ O.subgroupOf N₁) ∣ p ^ m := by
    rw [← hxm]
    exact orderOf_map_dvd (QuotientGroup.mk' (O.subgroupOf N₁)) x'
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h3 : orderOf (QuotientGroup.mk x' : ↥N₁ ⧸ O.subgroupOf N₁) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : (QuotientGroup.mk x' : ↥N₁ ⧸ O.subgroupOf N₁) = 1 := orderOf_eq_one_iff.mp h3
  have h5 : x' ∈ O.subgroupOf N₁ := (QuotientGroup.eq_one_iff x').mp h4
  exact Subgroup.mem_subgroupOf.mp h5

end CFSG.GH74.Uniqueness
