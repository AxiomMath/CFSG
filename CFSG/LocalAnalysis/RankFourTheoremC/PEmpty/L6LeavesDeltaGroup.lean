module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta

variable {K : Type} [Group K] [Finite K]

theorem sylow_sup_normal_eq_top {p : ℕ} [hp : Fact p.Prime] (N : Subgroup K) [N.Normal]
    (hq : IsPGroup p (K ⧸ N)) (S : Sylow p K) :
    (S : Subgroup K) ⊔ N = ⊤ := by
  classical
  have hTS : ((S : Subgroup K) ⊔ N).index ∣ (S : Subgroup K).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hTN : ((S : Subgroup K) ⊔ N).index ∣ N.index :=
    Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hq)
  have hNidx : N.index = p ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  rw [hNidx] at hTN
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 hTN
  have hSp : ¬ p ∣ (S : Subgroup K).index := S.not_dvd_index
  have hi0 : i = 0 := by
    by_contra hne
    apply hSp
    have hdiv : p ^ i ∣ (S : Subgroup K).index := by
      rw [← hi]
      exact hTS
    exact (dvd_pow_self p hne).trans hdiv
  have h1 : ((S : Subgroup K) ⊔ N).index = 1 := by
    rw [hi, hi0, pow_zero]
  exact Subgroup.index_eq_one.mp h1

theorem centralizes_of_normalizer {p : ℕ} [Fact p.Prime] (N : Subgroup K) [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (S : Sylow p K)
    (hSN : (S : Subgroup K) ⊔ N = ⊤)
    (hS : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a)
    (n : K) (hn : n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K)) :
    ∀ s ∈ (S : Subgroup K), s * n = n * s := by
  classical
  have hbot : (S : Subgroup K) ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgS, hgN⟩
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, hgS⟩
    have hgk : g ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hd1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgk
    have hd2 : orderOf g ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨g, hgN⟩ : N)
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) := Nat.Coprime.pow_left k hN
    have h1 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  intro s hs
  have hnTop : n ∈ (S : Subgroup K) ⊔ N := by
    rw [hSN]
    exact Subgroup.mem_top n
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hnTop
  have hz_comm : ∀ t ∈ (S : Subgroup K), z * t = t * z := by
    intro t ht
    have hnt : n * t * n⁻¹ ∈ (S : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
    have hzt : z * t * z⁻¹ ∈ (S : Subgroup K) := by
      have heq : z * t * z⁻¹ = y⁻¹ * (n * t * n⁻¹) * y := by
        rw [← hyz]
        group
      rw [heq]
      refine (S : Subgroup K).mul_mem ?_ hy
      exact (S : Subgroup K).mul_mem ((S : Subgroup K).inv_mem hy) hnt
    have hzN : z * t * z⁻¹ * t⁻¹ ∈ N := by
      have h1 : t * z⁻¹ * t⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› z⁻¹ (N.inv_mem hz) t
      have heq : z * t * z⁻¹ * t⁻¹ = z * (t * z⁻¹ * t⁻¹) := by group
      rw [heq]
      exact N.mul_mem hz h1
    have hc : z * t * z⁻¹ * t⁻¹ ∈ (S : Subgroup K) ⊓ N :=
      ⟨(S : Subgroup K).mul_mem hzt ((S : Subgroup K).inv_mem ht), hzN⟩
    rw [hbot, Subgroup.mem_bot] at hc
    calc z * t = z * t * z⁻¹ * t⁻¹ * t * z := by group
      _ = t * z := by rw [hc]; group
  calc s * n = s * (y * z) := by rw [hyz]
    _ = s * y * z := (mul_assoc s y z).symm
    _ = y * s * z := by rw [hS s hs y hy]
    _ = y * (s * z) := mul_assoc y s z
    _ = y * (z * s) := by rw [hz_comm s hs]
    _ = y * z * s := (mul_assoc y z s).symm
    _ = n * s := by rw [hyz]

theorem hasNormalPComplement_of_normalizer_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G)
    (h : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Q : Subgroup G) : Set G)) :
    CFSG.HasNormalPComplement p G := by
  obtain ⟨M, hMn, hMp, hMidx, -, -, -, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement Q h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp Q.isPGroup')
  have hpq : IsPGroup p (G ⧸ M) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [← Subgroup.index_eq_card, hMidx]
    exact hn
  unfold CFSG.HasNormalPComplement
  refine ⟨M, hMn, ?_, hpq⟩
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hMp

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta
