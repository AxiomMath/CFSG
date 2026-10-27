module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.AGLEmbedding

theorem inf_eq_bot_of_isPGroup_three_of_coprime {H : Type} [Group H] [Finite H]
    {A Y : Subgroup H} (hA : IsPGroup 3 A) (hY : Nat.Coprime 3 (Nat.card Y)) :
    A ⊓ Y = ⊥ := by
  have hK : IsPGroup 3 (A ⊓ Y : Subgroup H) := hA.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hK
  have hdvd : Nat.card (A ⊓ Y : Subgroup H) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd
  have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) := Nat.Coprime.pow_left k hY
  have h1 : 3 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hcard : Nat.card (A ⊓ Y : Subgroup H) = 1 := by
    rw [hk, h1]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem isPGroup_three_barM {G : Type} [Group G] {M Q : Subgroup G} (hQ : IsPGroup 3 Q) :
    IsPGroup 3 ↥(barM M Q) := by
  have hQM' : IsPGroup 3 (Q.subgroupOf M) := by
    intro x
    obtain ⟨n, hn⟩ := hQ ⟨x.1, (Subgroup.mem_subgroupOf).1 x.2⟩
    refine ⟨n, ?_⟩
    ext
    have := congrArg Subtype.val hn
    simpa using this
  exact hQM'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

theorem commutator_self_le {H : Type} [Group H] (K : Subgroup H) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  simp only [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hg₁ hg₂) (K.inv_mem hg₁)) (K.inv_mem hg₂)

theorem commutator_inf_centre_eq_bot_of_coprime {G : Type} [Group G] [Finite G]
    {M L Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hcop : Nat.Coprime 3 (Nat.card ↥(barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))))) :
    ⁅barM M Q, barM M Q⁆ ⊓
      (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥ := by
  have hA : IsPGroup 3 ↥⁅barM M Q, barM M Q⁆ :=
    (isPGroup_three_barM (M := M) hQ).to_le (commutator_self_le (barM M Q))
  exact inf_eq_bot_of_isPGroup_three_of_coprime hA hcop

end CFSG.HardMathSupport.Curtis.Proving

end
