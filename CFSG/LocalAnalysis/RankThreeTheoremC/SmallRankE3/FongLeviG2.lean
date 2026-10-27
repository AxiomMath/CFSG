module

public import CFSG.LieType.SeitzGeneration.ExcParabolicCard
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.K128.SylowShapeRank
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section



theorem zpow_eq_one_or_self_of_sq_eq_one {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1) (n : ℤ) :
    g ^ n = 1 ∨ g ^ n = g := by
  have h2 : g ^ (2 : ℤ) = 1 := by simpa using hg
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem parabolicSum_singleton_eq (τ : Tag) [Fintype (WeylGroup τ)] (i : Fin τ.rank) (q : ℕ) :
    CFSG.Timmesfeld.ExceptionalOrders.parabolicSum τ {i} q = 1 + q := by
  classical
  have hfilt : (Finset.univ.filter fun w : WeylGroup τ =>
      w ∈ (coxeterSystem τ).parabolic ({i} : Set (Fin τ.rank))) =
      ({1, (coxeterSystem τ).simple i} : Finset (WeylGroup τ)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hw
      rw [CFSG.Timmesfeld.ExceptionalOrders.parabolic_eq_parabolicWeylGroup] at hw
      simp only [parabolicWeylGroup, Set.image_singleton] at hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hw
      exact zpow_eq_one_or_self_of_sq_eq_one ((coxeterSystem τ).simple_sq i) n
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact (coxeterSystem τ).simple_mem_parabolic (Set.mem_singleton i)
  unfold CFSG.Timmesfeld.ExceptionalOrders.parabolicSum
  rw [hfilt, Finset.sum_pair]
  · rw [(coxeterSystem τ).length_one, (coxeterSystem τ).length_simple i, pow_zero, pow_one]
  · intro h
    have hl := (coxeterSystem τ).length_simple i
    rw [← h, (coxeterSystem τ).length_one] at hl
    exact absurd hl (by norm_num)

theorem card_parabolic_G2_eq {F : Type} [Field F] [Finite F] [Fintype (WeylGroup Tag.G2)]
    (J : Set (Fin Tag.G2.rank)) :
    Nat.card (parabolicSubgroup Tag.G2 F J) =
      (Nat.card F - 1) ^ 2 * Nat.card F ^ 6 *
        CFSG.Timmesfeld.ExceptionalOrders.parabolicSum Tag.G2 J (Nat.card F) := by
  rw [(standard_parabolic_cells Tag.G2 F).2.2.2.2.2.2 J,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2,
    CFSG.LieType.SeitzGeneration.finsum_parabolicWeylGroup_eq]

theorem g2_core {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKr : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.G2 F)) ≤ 1)
    (J : Set (Fin Tag.G2.rank)) (hJ : J ≠ Set.univ)
    {z : (Module.End F (RootModule Tag.G2 F))ˣ} (hz : z ∈ parabolicSubgroup Tag.G2 F J)
    (hzp : orderOf z = p) : False := by
  haveI : Fintype (WeylGroup Tag.G2) := Fintype.ofFinite _
  have hchar : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  haveI := hchar
  have hm1 : 1 ≤ m := by omega
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hdvdP : p ∣ Nat.card (parabolicSubgroup Tag.G2 F J) := by
    have h := Subgroup.orderOf_dvd_natCard _ hz
    rwa [hzp] at h
  rw [card_parabolic_G2_eq] at hdvdP
  have hS : CFSG.Timmesfeld.ExceptionalOrders.parabolicSum Tag.G2 J (Nat.card F) = 1 ∨
      CFSG.Timmesfeld.ExceptionalOrders.parabolicSum Tag.G2 J (Nat.card F) = 1 + Nat.card F := by
    have hex : ∀ i : Fin Tag.G2.rank, ∃ j : Fin Tag.G2.rank, ∀ k, k ≠ i → k = j := by
      decide
    obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
    obtain ⟨j, hj⟩ := hex i
    have hsub : J ⊆ ({j} : Set (Fin Tag.G2.rank)) :=
      fun k hk => hj k (fun h => hi (h ▸ hk))
    rcases Set.subset_singleton_iff_eq.1 hsub with h | h
    · left
      rw [h, CFSG.Timmesfeld.ExceptionalOrders.parabolicSum_empty]
    · right
      rw [h, parabolicSum_singleton_eq]
  have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hd : p ∣ Nat.card F ^ 2 - 1 := by
    rw [hsq]
    rcases hS with hS | hS <;> rw [hS] at hdvdP
    · rw [mul_one] at hdvdP
      rcases (Nat.Prime.dvd_mul hp).1 hdvdP with h | h
      · exact Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h) _
      · exact absurd (hp.dvd_of_dvd_pow h) hpq
    · rcases (Nat.Prime.dvd_mul hp).1 hdvdP with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · exact Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h') _
        · exact absurd (hp.dvd_of_dvd_pow h') hpq
      · rw [add_comm] at h
        exact Dvd.dvd.mul_left h _
  have hne : Nat.card F ^ 2 - 1 ≠ 0 := by
    have h16 : 4 ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq4 2
    norm_num at h16
    omega
  have he : 1 ≤ (Nat.card F ^ 2 - 1).factorization p := hp.factorization_pos_of_dvd hne hd
  have hrank := CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he
    (CFSG.RankThree.PartOne.K128.sylowShape_G2 F hp hp5 hF (by omega) hd)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  have h := le_trans hrank hKr
  omega

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
