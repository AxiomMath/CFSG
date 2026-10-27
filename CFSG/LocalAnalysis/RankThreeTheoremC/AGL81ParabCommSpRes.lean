module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.AGLEmbedding.LeviBlock CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
  (normal_eq_top_or_le_center not_isSolvable_of_isQuasisimple)

theorem le_center_of_card_dvd_two {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal]
    (h : Nat.card N ∣ 2) : N ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  have hcard : Nat.card N = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact absurd (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp h1 ▸ hz)) hz1
    · exact h2
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hcard
  have h1 : (⟨z, hz⟩ : N) = y := hy _ fun h => hz1 (congrArg Subtype.val h)
  have h2 : (⟨g * z * g⁻¹, hc⟩ : N) = y := hy _ fun h => hz1 (by
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    rw [mul_inv_eq_one, mul_eq_left] at h'
    exact h')
  have hz' : g * z * g⁻¹ = z := congrArg Subtype.val (h2.trans h1.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hz']

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_statedSp_eq_bot (m : ℕ) : Subgroup.center (StatedSp m K) = ⊥ :=
  (CFSG.LieType.Universal.Symplectic.center_eq m K).trans
    (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot m)

theorem subsingleton_statedSp_zero : Subsingleton (StatedSp 0 K) :=
  ⟨fun _ _ => Subtype.ext (Units.ext (Matrix.ext fun i _ => by
    rcases i with i | i <;> exact i.elim0))⟩

theorem card_statedSp_one_of_card_two (hK : Nat.card K = 2) : Nat.card (StatedSp 1 K) = 6 := by
  rw [SymplecticFlag.card_statedSp, hK]
  decide

theorem card_statedSp_two_of_card_two (hK : Nat.card K = 2) : Nat.card (StatedSp 2 K) = 720 := by
  rw [SymplecticFlag.card_statedSp, hK]
  decide

theorem center_commutator_statedSp_two (hK : Nat.card K = 2) :
    Subgroup.center ↥(commutator (StatedSp 2 K)) = ⊥ := by
  obtain ⟨-, h360⟩ := spFlag_spFour_comm (K := K) hK
  set G' : Subgroup (StatedSp 2 K) := commutator (StatedSp 2 K) with hG'
  set Z : Subgroup ↥G' := Subgroup.center ↥G' with hZ
  have hcard : Nat.card ↥G' = 360 * Nat.card ↥Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, h360]
  have hdvd : Nat.card ↥G' ∣ 720 := by
    rw [← card_statedSp_two_of_card_two hK]
    exact Subgroup.card_subgroup_dvd_card G'
  have hZ2 : Nat.card ↥Z ∣ 2 := by
    rw [hcard] at hdvd
    have h1 : 360 * Nat.card ↥Z ∣ 360 * 2 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 360) h1
  set Zg : Subgroup (StatedSp 2 K) := Z.map G'.subtype with hZg
  have hZgcard : Nat.card ↥Zg = Nat.card ↥Z :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective G')
  haveI hZgn : Zg.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨z, hz, rfl⟩ g
    have hmem : g * (z : StatedSp 2 K) * g⁻¹ ∈ G' :=
      Subgroup.Normal.conj_mem inferInstance (z : StatedSp 2 K) z.2 g
    refine ⟨⟨g * (z : StatedSp 2 K) * g⁻¹, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hgw : g⁻¹ * (w : StatedSp 2 K) * g ∈ G' :=
      Subgroup.Normal.conj_mem inferInstance (w : StatedSp 2 K) w.2 g⁻¹
    have hc := Subgroup.mem_center_iff.mp hz ⟨_, hgw⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc' ⊢
    calc (w : StatedSp 2 K) * (g * z * g⁻¹)
        = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc']
      _ = g * z * g⁻¹ * w := by group
  have hle := le_center_of_card_dvd_two (N := Zg) (hZgcard ▸ hZ2)
  rw [center_statedSp_eq_bot] at hle
  rw [eq_bot_iff]
  intro z hz
  have : (z : StatedSp 2 K) ∈ (⊥ : Subgroup (StatedSp 2 K)) := hle ⟨z, hz, rfl⟩
  rw [Subgroup.mem_bot] at this ⊢
  exact Subtype.ext this

theorem isQuasisimple_statedSp_of_not_small {m : ℕ} (hm : 1 ≤ m) (h1 : ¬(m = 1 ∧ Nat.card K = 2))
    (h2 : ¬(m = 2 ∧ Nat.card K = 2)) : CFSG.Open.IsQuasisimple (StatedSp m K) := by
  refine spFlag_isQuasisimple_Sp hm ?_
  rcases spFlag_card_eq_two_or_four_le (K := K) with hK | hK
  · right
    by_contra hlt
    exact (by omega : m = 1 ∨ m = 2) |>.elim (fun h => h1 ⟨h, hK⟩) fun h => h2 ⟨h, hK⟩
  · exact Or.inl hK

theorem eq_one_of_commute_spResBlock (m : ℕ) {γ : StatedSp m K}
    (hγ : γ ∈ commutator (StatedSp m K)) (h : ∀ c ∈ spResBlock K m, γ * c = c * γ) :
    γ = 1 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI := subsingleton_statedSp_zero (K := K)
    exact Subsingleton.elim _ _
  by_cases hs : m = 1 ∧ Nat.card K = 2
  · have hγc : γ ∈ Subgroup.center (StatedSp m K) := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact (h c (by rw [spResBlock, if_pos hs]; trivial)).symm
    rw [center_statedSp_eq_bot] at hγc
    exact Subgroup.mem_bot.mp hγc
  have hres : spResBlock K m = commutator (StatedSp m K) := by rw [spResBlock, if_neg hs]
  by_cases h22 : m = 2 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := h22
    have hmem : (⟨γ, hγ⟩ : commutator (StatedSp 2 K)) ∈
        Subgroup.center ↥(commutator (StatedSp 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact (h c.1 (by rw [hres]; exact c.2)).symm
    rw [center_commutator_statedSp_two hK] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  · have hq := isQuasisimple_statedSp_of_not_small (K := K) hm hs h22
    have hγc : γ ∈ Subgroup.center (StatedSp m K) := by
      rw [Subgroup.mem_center_iff]
      intro c
      refine (h c ?_).symm
      rw [hres, hq.1]
      trivial
    rw [center_statedSp_eq_bot] at hγc
    exact Subgroup.mem_bot.mp hγc

theorem eq_bot_of_isPGroup_normal_statedSp (m : ℕ) {N : Subgroup (StatedSp m K)} [hN : N.Normal]
    (hP : IsPGroup 2 N) : N = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI := subsingleton_statedSp_zero (K := K)
    exact Subsingleton.elim _ _
  by_cases hs : m = 1 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := hs
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hdvd : Nat.card N ∣ 6 := by
      rw [← card_statedSp_one_of_card_two hK]
      exact Subgroup.card_subgroup_dvd_card N
    have h2 : Nat.card N ∣ 2 := by
      rw [hn] at hdvd ⊢
      have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left _ (by norm_num)
      have h6 : 2 ^ n ∣ 2 * 3 := hdvd
      have := hcop.dvd_of_dvd_mul_right h6
      exact this
    have := le_center_of_card_dvd_two h2
    rw [center_statedSp_eq_bot] at this
    exact le_bot_iff.mp this
  by_cases h22 : m = 2 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := h22
    obtain ⟨hq, h360⟩ := spFlag_spFour_comm (K := K) hK
    set G' : Subgroup (StatedSp 2 K) := commutator (StatedSp 2 K) with hG'
    have hZ := center_commutator_statedSp_two hK
    have hG'card : Nat.card ↥G' = 360 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥G'), h360, hZ,
        Subgroup.card_bot, mul_one]
    have hNG : ∀ x ∈ N, x ∈ G' → x = 1 := by
      intro x hxN hxG
      have hnorm : (N.subgroupOf G').Normal := hN.subgroupOf G'
      have hpg : IsPGroup 2 ↥(N.subgroupOf G') :=
        hP.comap_of_injective G'.subtype (Subgroup.subtype_injective G')
      rcases normal_eq_top_or_le_center hq hnorm with htop | hc
      · exfalso
        have hP' : IsPGroup 2 ↥G' := by
          rw [htop] at hpg
          exact hpg.of_equiv Subgroup.topEquiv
        haveI := hP'.isNilpotent
        exact not_isSolvable_of_isQuasisimple hq inferInstance
      · have hx : (⟨x, hxG⟩ : ↥G') ∈ N.subgroupOf G' := hxN
        have := hc hx
        rw [hZ, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
    have hcardG := card_statedSp_two_of_card_two hK
    have hindex : Nat.card (StatedSp 2 K ⧸ G') = 2 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup G'
      rw [hcardG, hG'card] at this
      omega
    let π : ↥N →* StatedSp 2 K ⧸ G' := (QuotientGroup.mk' G').comp N.subtype
    have hπ : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : StatedSp 2 K) ∈ G' := (QuotientGroup.eq_one_iff _).mp hx
      exact Subtype.ext (hNG x x.2 hx')
    have hle : Nat.card ↥N ≤ 2 := by
      have := Nat.card_le_card_of_injective (⇑π) hπ
      rwa [hindex] at this
    have h2 : Nat.card ↥N ∣ 2 := by
      have hpos := Nat.card_pos (α := ↥N)
      interval_cases h : Nat.card ↥N
      · exact one_dvd _
      · exact dvd_refl _
    have := le_center_of_card_dvd_two h2
    rw [center_statedSp_eq_bot] at this
    exact le_bot_iff.mp this
  · have hq := isQuasisimple_statedSp_of_not_small (K := K) hm hs h22
    rcases normal_eq_top_or_le_center hq hN with htop | hc
    · exfalso
      have hP' : IsPGroup 2 (StatedSp m K) := by
        rw [htop] at hP
        exact hP.of_equiv Subgroup.topEquiv
      haveI := hP'.isNilpotent
      exact not_isSolvable_of_isQuasisimple hq inferInstance
    · rw [center_statedSp_eq_bot] at hc
      exact le_bot_iff.mp hc

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
