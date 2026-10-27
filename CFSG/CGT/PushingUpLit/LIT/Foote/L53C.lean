module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L53

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem centralizer_le_of_mem {t : G} (ht : t ∈ J) (h2 : ∃ n : ℕ, t ^ 2 ^ n = 1) (h1 : t ≠ 1) :
    Subgroup.centralizer ({t} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨n, hn⟩ := h2
    have : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hA1 : Subgroup.zpowers t ≠ ⊥ := fun h => h1 (Subgroup.zpowers_eq_bot.1 h)
  obtain ⟨m, hm, hne⟩ := c.exists_conj_ne
  have hcomm := c.commutator_conj_eq_bot hm hne
  rw [Subgroup.commutator_comm] at hcomm
  have hJm : rightConjugate J m ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hN : rightConjugate J m ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_zpowers (Subgroup.mem_centralizer_iff.1 (hJm hy) t ht).symm
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  exact c.normalizer_le hA hA1 hm hN (mem_normalizer_zpowers hk)

theorem centralizer_le_conj {h t : G} (ht : t ∈ rightConjugate J h) (h2 : ∃ n : ℕ, t ^ 2 ^ n = 1)
    (h1 : t ≠ 1) : Subgroup.centralizer ({t} : Set G) ≤ rightConjugate M h := by
  rw [mem_rightConjugate_iff] at ht
  have h1' : h * t * h⁻¹ ≠ 1 := fun e => h1 (by simpa using e)
  have h2' : ∃ n : ℕ, (h * t * h⁻¹) ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := h2
    exact ⟨n, by rw [conj_pow, hn]; group⟩
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hw
  rw [mem_rightConjugate_iff]
  apply c.centralizer_le_of_mem ht h2' h1'
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * w * h⁻¹ * (h * t * h⁻¹) = h * (w * t) * h⁻¹ := by group
    _ = h * (t * w) * h⁻¹ := by rw [hw]
    _ = h * t * h⁻¹ * (h * w * h⁻¹) := by group

theorem normalizes_of_le_conj (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀) {h : G} (hh : h ∉ M)
    {W : Subgroup G} (hW : W ≤ rightConjugate J h ⊓ M) (hW2 : CFSG.Open.IsElemAbelian 2 W)
    (hW4 : Nat.card W = 4) : W ≤ Subgroup.normalizer (J : Set G) :=
  c.lemma_5_3 hA hz₀ (hW.trans inf_le_right) hW2 hW4 hh fun w hw hw1 =>
    c.centralizer_le_conj (hW hw).1 ⟨1, by rw [pow_one]; exact hW2.2 w hw⟩ hw1

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
