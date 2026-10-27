module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec87b
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec87d
import CFSG.Goldschmidt.Steps.Sec87e
import CFSG.Goldschmidt.Steps.Sec87h
import CFSG.Goldschmidt.Steps.Sec87i
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter Sec8

theorem G87_of (h86 : S_G86) : S_G87 := by
  intro G _ _ S A hset h4 hS
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  obtain ⟨H, hH⟩ := G73.benderM_nonempty hset ha1
  obtain ⟨p, hp, hp2, hinv, hrank, huniqH⟩ := h86 G S A hset h4 hS a ha ha1 H hH
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hca, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  have hbA : n * a * n⁻¹ ∈ A := conj_mem hn ha
  have hb1 : n * a * n⁻¹ ≠ 1 := conj_ne_one ha1
  have hz2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1]
  have hbz : n * a * n⁻¹ ∉ Subgroup.zpowers a := fun h =>
    (mem_two hz2 (Subgroup.mem_zpowers a) ha1 h).elim hb1 hca
  have hSH : (S : Subgroup G) ≤ H := le_of_mem_benderM hset h4 ha hH
  have hSP : (S : Subgroup G) ≤ Subgroup.normalizer (qCoreOf H p : Set G) :=
    hSH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p))
  have huniq : ∀ t ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (qCoreOf H p : Set G),
      t ^ 2 = 1 → t = 1 ∨ t = a := fun t ht ht2 => huniqH t ⟨hSH ht.1, ht.2⟩ ht2
  obtain ⟨hC1, hC2, hC3⟩ := key87 hset h4 hbA hp hp2 (qCoreOf_isPGroup H p) hSP
    (hinv _ hbA hbz) hrank huniq ha
  have hΩZ := eq_omega1_center hset h4 hC1
  have hAD := le_commutator hset h4 hS hΩZ
  have hab := isMulCommutative_commutator hset h4 ha ha1 hbA hb1 hca hSP huniq hAD hC2 hC3
  exact ⟨le_antisymm (pRank_le_three h4 hC1) (three_le_pRank hset), hab,
    card_eq_exponent_sq hset h4 hAD hC2 hab, hΩZ, eq_omega1_commutator hset hAD hC2⟩

end CFSG.Goldschmidt
