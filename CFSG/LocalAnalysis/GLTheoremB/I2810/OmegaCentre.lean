module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaCard

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCentre

@[expose] def OmegaNoOddCover : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (G : Type) [Group G] [Finite G], commutator G = ⊤ →
    ∀ (Z : Subgroup G) [Z.Normal], Z ≤ Subgroup.center G → Odd (Nat.card ↥Z) →
      (Nonempty ((G ⧸ Z) ≃* ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)))) ∨
        Nonempty ((G ⧸ Z) ≃* ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))) → Z = ⊥

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem centre_odd (h : Setup28 W K S) : Odd (Nat.card ↥(Subgroup.center ↥(bar W K))) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(bar W K)) :=
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set c : ↥(bar W K) := (x : ↥(bar W K)) with hc
  have hcc : c ∈ Subgroup.center ↥(bar W K) := x.2
  have hco : orderOf c = 2 := by rw [hc, Subgroup.orderOf_coe]; exact hx
  have hnorm : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hcc)
  have hp : IsPGroup 2 ↥(Subgroup.zpowers c) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco]; norm_num)
  have hle : Subgroup.zpowers c ≤ CFSG.pCore 2 ↥(bar W K) := le_sSup ⟨hnorm, hp⟩
  rw [h.hO] at hle
  have : c = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  rw [this, orderOf_one] at hco
  exact absurd hco (by norm_num)

theorem centre_trivial_of_cover (hM : OmegaNoOddCover) (h : Setup28 W K S) (hR : Red28 W K S)
    {a : X} {U₁ U₂ : Subgroup X} {n : ℕ} (hn : 2 ≤ n) (hΩ : OmegaAny W K a U₁ U₂ n) :
    Subgroup.center ↥(bar W K) = ⊥ := by
  obtain ⟨ε, hε⟩ := OmegaCard.isOmegaTwo_quot hR hn hΩ
  refine hM n hn ↥(bar W K) hR.quasi.1.commutator_eq_top (Subgroup.center ↥(bar W K)) le_rfl
    (centre_odd h) ?_
  cases ε
  · exact Or.inr hε
  · exact Or.inl hε

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCentre
