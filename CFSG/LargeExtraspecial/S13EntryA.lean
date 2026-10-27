module

public import CFSG.LargeExtraspecial.S5Five
public import CFSG.LargeExtraspecial.S13Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

section P

variable {P : Subgroup S.O} (hPM : P ≤ S.Mbar) (hP1 : P ≠ ⊥) (hP3 : IsPGroup 3 P)
  (hPn : ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
include hPM hP1 hP3 hPn

theorem card_eq_three_of (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hn : 4 < S.width) : Nat.card P = 3 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := S5.card_oddCore_dvd_three H hNo C hn
  set P' : Subgroup S.Mbar := P.subgroupOf S.Mbar with hP'
  have hcard : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv
  have hN : P'.Normal := ⟨fun p hp x => by
    rw [hP', mem_subgroupOf] at hp ⊢
    simpa using hPn x x.2 p hp⟩
  have hodd : Odd (Nat.card P') := by
    obtain ⟨k, hk⟩ := (hP3.of_equiv (subgroupOfEquivOfLe hPM).symm).exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hle := S5.le_timmesfeldOddCore hN hodd
  have h1 := (Subgroup.card_dvd_of_le hle).trans hdvd
  rw [hcard] at h1
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq P h) hP1
  · exact h

omit hPM hP3 in
theorem fixFree_of (hirr : ¬ S.IsReducible) : FixFree S P := by
  intro v hv
  set U := fixSub S P with hU
  have hinv : ∀ m : S.M, ∀ u ∈ U, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
    intro m u hu k hk
    have hm : S.ρ m ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨m, rfl⟩
    have hk' := hPn _ (inv_mem hm) k hk
    rw [inv_inv] at hk'
    have e := hu _ hk'
    have e' := congrArg ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e
    simpa [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply_O] using e'
  by_contra hv0
  have hUne : U ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot (ZMod 2)).mp (h ▸ hv))
  by_cases hUt : U = ⊤
  · apply hP1
    rw [eq_bot_iff]
    intro k hk
    rw [mem_bot]
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    have hw : w ∈ U := hUt ▸ Submodule.mem_top
    simpa using hw k hk
  · exact hirr ⟨U, hUne, hUt, hinv⟩

end P

end CFSG.LargeExtraspecial.S13
