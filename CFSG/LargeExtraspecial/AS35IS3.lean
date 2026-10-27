module

public import CFSG.LargeExtraspecial.AS35IProd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77

variable {G : Type} [Group G] {N U P : Subgroup G} {z : G}

theorem card_range_conjAct : Nat.card (conjAct z N).range = Nat.card (Gbar N z) :=
  (Nat.card_congr (QuotientGroup.quotientKerEquivRange (conjAct z N)).toEquiv).symm

namespace Hyp

variable (h : Hyp N U P z)
include h

omit h in
theorem card_conjIn_dvd [Finite G] : Nat.card (conjIn z N) ∣ Nat.card (conjAct z N).range := by
  rw [card_conjIn, ← index_ker]
  apply index_dvd_of_le
  intro n hn
  rw [mem_subgroupOf]
  exact kerV_le_M (mem_kerK.1 hn)

theorem exists_orderOf_two_range [Finite G] :
    ∃ σ ∈ (conjAct z N).range, orderOf σ = 2 := by
  obtain ⟨a, ha, haK⟩ := h.exists_not_mem_kerV
  have haN := h.sup_le_N ha
  refine ⟨conjAct z N ⟨a, haN⟩, ⟨_, rfl⟩, orderOf_eq_prime ?_ ?_⟩
  · rw [pow_two, ← map_mul, ← MonoidHom.mem_ker, mem_kerK]
    exact h.sq_mem_kerV ha
  · intro h1
    exact haK (mem_kerK.1 (MonoidHom.mem_ker.2 h1))

theorem isSThreeAt_of_card_two [Finite G] (h2 : Nat.card (barOf N z (U ⊔ P)) = 2) :
    IsSThreeAt z N := by
  have hA := h.card_commutator_sup_le_of_card_two h2
  obtain ⟨g, hgN, hgz⟩ : ∃ g ∈ N, g ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact h.notcen hcon
  have hgM : g ∉ cenM N z := fun hg => hgz (mem_inf.1 hg).2
  have hV := h.card_genV_mul_le hgN hgM
  have hΩ := h.card_conjIn_add_one_mul_le
  have hodd := h.odd_card_conjIn
  have h1 := h.one_lt_card_conjIn
  have hCpos : 0 < Nat.card (Asc77.centerIn z N) := Nat.card_pos
  have hV4 : Nat.card (genV N z) ≤ 4 * Nat.card (Asc77.centerIn z N) := by
    have h3 : Nat.card (genV N z) * Nat.card (Asc77.centerIn z N) ≤
        (4 * Nat.card (Asc77.centerIn z N)) * Nat.card (Asc77.centerIn z N) := by
      calc Nat.card (genV N z) * Nat.card (Asc77.centerIn z N)
          ≤ Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) *
              Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) := hV
        _ ≤ (2 * Nat.card (Asc77.centerIn z N)) * (2 * Nat.card (Asc77.centerIn z N)) :=
            Nat.mul_le_mul hA hA
        _ = (4 * Nat.card (Asc77.centerIn z N)) * Nat.card (Asc77.centerIn z N) := by ring
    exact Nat.le_of_mul_le_mul_right h3 hCpos
  have hΩ3 : Nat.card (conjIn z N) = 3 := by
    have h4 : (Nat.card (conjIn z N) + 1) * Nat.card (Asc77.centerIn z N) ≤
        4 * Nat.card (Asc77.centerIn z N) := hΩ.trans hV4
    have h5 := Nat.le_of_mul_le_mul_right h4 hCpos
    obtain ⟨k, hk⟩ := hodd
    omega
  have hVeq : Nat.card (genV N z) = 4 * Nat.card (Asc77.centerIn z N) := by
    rw [hΩ3] at hΩ
    omega
  refine ⟨?_, fun a ha b hb => h.comm_conjIn ha hb, hVeq, ?_⟩
  · rw [← Nat.card_coe_set_eq, hΩ3]
  · have : Finite (conjIn z N) := Nat.finite_of_card_ne_zero (by rw [hΩ3]; norm_num)
    rw [← MonoidHom.range_eq_top]
    apply eq_top_of_card_eq
    rw [Nat.card_perm, hΩ3]
    have hdvd3 := card_conjIn_dvd (N := N) (z := z)
    rw [hΩ3] at hdvd3
    obtain ⟨σ, hσ, hσ2⟩ := h.exists_orderOf_two_range
    have hdvd2 : 2 ∣ Nat.card (conjAct z N).range := by
      rw [← hσ2, ← orderOf_mk σ hσ]
      exact orderOf_dvd_natCard _
    have hle : Nat.card (conjAct z N).range ≤ Nat.card (Equiv.Perm (conjIn z N)) :=
      card_le_card_group _
    rw [Nat.card_perm, hΩ3] at hle
    have h6 : 6 ∣ Nat.card (conjAct z N).range :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hdvd2 hdvd3
    have hpos : 0 < Nat.card (conjAct z N).range := Nat.card_pos
    obtain ⟨k, hk⟩ := h6
    have : Nat.factorial 3 = 6 := rfl
    rw [this] at hle ⊢
    rcases k with _ | _ | k
    · omega
    · omega
    · omega

end Hyp

end CFSG.LargeExtraspecial.Asc22
