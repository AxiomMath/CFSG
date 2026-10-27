module

public import CFSG.GH74.Generic.S1.TPairFacts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GroupTheory

open Subgroup

theorem odd_orderOf_of_mem_center_of_surjective {Q H : Type} [Group Q] [Finite Q] [Group H]
    (ψ : Q →* H) (hψ : Function.Surjective ψ)
    (hQ : CFSG.Open.IsQuasisimple Q) (hO2 : CFSG.pCore 2 Q = ⊥)
    {t : H} (htc : t ∈ Subgroup.center H) : Odd (orderOf t) := by
  have hQ' : CFSG.IsQuasisimple Q :=
    ⟨⟨hQ.1⟩, hQ.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩
  by_cases htop : ψ.ker = ⊤
  · have ht1 : t = 1 := by
      obtain ⟨x, rfl⟩ := hψ t
      have hx : x ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top x
      simpa using hx
    rw [ht1]
    simp
  · have hker : ψ.ker ≤ Subgroup.center Q := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ' (MonoidHom.normal_ker ψ) with h | h
      · exact absurd h htop
      · exact h
    have hoddZ : Odd (Nat.card (Subgroup.center Q)) := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      obtain ⟨z, hz⟩ :=
        exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 (even_iff_two_dvd.mp hev)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hzQ : (z : Q) ∈ Subgroup.center Q := z.2
      have hzmem : (z : Q) ∈ Subgroup.zpowers (z : Q) := Subgroup.mem_zpowers _
      have hzpow : Subgroup.zpowers (z : Q) ≤ CFSG.pCore 2 Q := by
        refine le_sSup ⟨?_, ?_⟩
        · refine Subgroup.normal_of_le_center ?_
          intro y hy
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact (Subgroup.center Q).zpow_mem hzQ i
        · apply IsPGroup.of_card (n := 1)
          rw [Nat.card_zpowers, Subgroup.orderOf_coe z, hz]
          norm_num
      have hz1 : (z : Q) = 1 := by
        have := hzpow hzmem
        rwa [hO2, Subgroup.mem_bot] at this
      have hz1' : z = 1 := Subtype.ext hz1
      rw [hz1'] at hz
      simp at hz
    obtain ⟨-, hodd⟩ :=
      CFSG.GH74.Generic.S1.quasisimple_range_center_odd hQ' hoddZ ψ hker
    exact hodd t (by rw [MonoidHom.range_eq_top.2 hψ]; exact Subgroup.mem_top t)
      (fun w _ => (Subgroup.mem_center_iff.1 htc w).symm)

theorem not_mem_center_of_orderOf_eq_two_of_quasisimple {Q H : Type} [Group Q] [Finite Q]
    [Group H] (ψ : Q →* H) (hψ : Function.Surjective ψ)
    (hQ : CFSG.Open.IsQuasisimple Q) (hO2 : CFSG.pCore 2 Q = ⊥)
    {t : H} (ht : orderOf t = 2) : t ∉ Subgroup.center H := by
  intro htc
  have hodd := odd_orderOf_of_mem_center_of_surjective ψ hψ hQ hO2 htc
  rw [ht] at hodd
  exact (by norm_num : ¬ Odd 2) hodd

end CFSG.GroupTheory
