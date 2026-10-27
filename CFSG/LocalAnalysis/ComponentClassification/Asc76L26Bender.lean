module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Hull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_bender (hO : CFSG.oddCore G = ⊥)
    (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {H : Subgroup G} (hH : H ≠ ⊤) {z : G}
    (hz : orderOf z = 2) (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) :
    (involutionPointHull z).Normal ∧ fusionIsBenderGroup (involutionPointHull z) ∧
      fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z)) ∧
      CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo (involutionPointHull z) ∧
      z ∈ involutionPointHull z := by
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity H z hz hH huniq
  have h2 := h12 h1
  have hrank := two_le_twoRank_hull hz hH huniq h2.1 hO
  rcases h23 h2 with hlow | ⟨u, hu2, hucen, -, -, hse, hclass⟩
  · omega
  have hLn : (involutionPointHull z).Normal := minimalLocalFailure_hull_normal z
  have hcoreL : CFSG.oddCore (involutionPointHull z) = ⊥ :=
    Lemma34.oddCore_eq_bot_of_normal' hO (involutionPointHull z)
  let q := QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z))
  have hinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcoreL
  have hcomm : ∀ y ∈ involutionPointHull z, Commute (u : G) y := by
    intro y hy
    have h1' : q ⟨y, hy⟩ * q u = q u * q ⟨y, hy⟩ := mem_center_iff.mp hucen _
    rw [← map_mul, ← map_mul] at h1'
    exact (congrArg Subtype.val (hinj h1')).symm
  have hu2' : (u : G) * u = 1 := by
    have : ((u ^ 2 : involutionPointHull z) : G) = 1 := by rw [hu2]; rfl
    rwa [Subgroup.coe_pow, sq] at this
  have hKn : ⁅involutionPointHull z, involutionPointHull z⁆.Normal :=
    commutator_normal (involutionPointHull z) (involutionPointHull z)
  have hgen := Lemma34.commutator_hull_odd_index hz u.2 hcomm hu2' hclass
  obtain ⟨t, ht, hzt, hne⟩ : ∃ t ∈ involutionPointClass z, Commute z t ∧ t ≠ z := by
    by_contra hcon
    have hzc := mem_center_of_isolated hO hz h2.1 (fun t ht hzt => by
      by_contra hne
      exact hcon ⟨t, ht, hzt, hne⟩)
    exact hZ z hzc hz
  have hKne : ⁅involutionPointHull z, involutionPointHull z⁆ ≠ ⊥ := by
    intro hbot
    apply hse.1
    rw [eq_top_iff]
    intro x _
    have hx1 : x = 1 := Subtype.ext (mem_bot.mp ((le_of_eq hbot) x.2))
    rw [hx1]
    exact one_mem _
  have hnc : ∀ {t₀ : G}, t₀ ∈ involutionPointClass z → t₀ ≠ u := by
    intro t₀ ht₀ heq
    apply hKne
    refine Lemma34.commutator_hull_eq_bot_of_central ht₀ fun y hy => ?_
    rw [heq]
    exact hcomm y hy
  have hzK := hclass z (distinguished_mem_pointClass z)
  have htK := hclass t ht
  have hzL : z ∈ involutionPointHull z := subset_closure (distinguished_mem_pointClass z)
  have htL : t ∈ involutionPointHull z := subset_closure ht
  have hzz : z * z = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hz).1
  have htt : t * t = 1 := class_mul_self hz ht
  have huinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_left hu2'
  have hsq : ∀ {s : G}, s ∈ involutionPointHull z → s * s = 1 →
      (u : G)⁻¹ * s * ((u : G)⁻¹ * s) = 1 := by
    intro s hs hss
    rw [huinv, mul_assoc, ← mul_assoc s, ← (hcomm s hs).eq, mul_assoc, ← mul_assoc (u : G),
      hu2', one_mul, hss]
  have hne1 : ∀ {s : G}, s ≠ (u : G) → (u : G)⁻¹ * s ≠ 1 := by
    intro s hs h1''
    apply hs
    calc s = (u : G) * ((u : G)⁻¹ * s) := by group
      _ = u := by rw [h1'', mul_one]
  set k₁ : ↥(⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) :=
    ⟨(u : G)⁻¹ * z, hzK⟩ with hk₁
  set k₂ : ↥(⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) :=
    ⟨(u : G)⁻¹ * t, htK⟩ with hk₂
  have hk₁1 : k₁ ≠ 1 := fun h =>
    hne1 (hnc (distinguished_mem_pointClass z)) (congrArg Subtype.val h)
  have hk₂1 : k₂ ≠ 1 := fun h => hne1 (hnc ht) (congrArg Subtype.val h)
  have hk₁k₁ : k₁ * k₁ = 1 := Subtype.ext (hsq hzL hzz)
  have hk₂k₂ : k₂ * k₂ = 1 := Subtype.ext (hsq htL htt)
  have hk₁2 : orderOf k₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hk₁k₁) hk₁1
  have hk₂2 : orderOf k₂ = 2 := orderOf_eq_prime (by rw [sq]; exact hk₂k₂) hk₂1
  have hk12 : Commute k₁ k₂ := by
    apply Subtype.ext
    change (u : G)⁻¹ * z * ((u : G)⁻¹ * t) = (u : G)⁻¹ * t * ((u : G)⁻¹ * z)
    have hc1 : Commute (u : G)⁻¹ z := (hcomm z hzL).inv_left
    have hc2 : Commute (u : G)⁻¹ t := (hcomm t htL).inv_left
    calc (u : G)⁻¹ * z * ((u : G)⁻¹ * t) = (u : G)⁻¹ * (z * (u : G)⁻¹) * t := by group
      _ = (u : G)⁻¹ * ((u : G)⁻¹ * z) * t := by rw [← hc1.eq]
      _ = (u : G)⁻¹ * (u : G)⁻¹ * (z * t) := by group
      _ = (u : G)⁻¹ * (u : G)⁻¹ * (t * z) := by rw [hzt.eq]
      _ = (u : G)⁻¹ * ((u : G)⁻¹ * t) * z := by group
      _ = (u : G)⁻¹ * (t * (u : G)⁻¹) * z := by rw [hc2.eq]
      _ = (u : G)⁻¹ * t * ((u : G)⁻¹ * z) := by group
  have hk12ne : k₁ ≠ k₂ := by
    intro heq
    apply hne
    have := congrArg Subtype.val heq
    change (u : G)⁻¹ * z = (u : G)⁻¹ * t at this
    exact (mul_left_cancel this).symm
  have hKB : fusionIsBenderGroup (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) :=
    fusionIsBenderGroup_of_stronglyEmbedded
      (Lemma34.oddCore_eq_bot_of_normal' hO ⁅involutionPointHull z, involutionPointHull z⁆)
      hgen hse hk₁2 hk₂2 hk12 hk12ne
  have hKrank : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo
      (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) := by
    refine ⟨commutingPairSubgroup k₁ k₂ hk₁k₁ hk₂k₂ hk12, ?_, fun x => ?_⟩
    · rw [commutingPairSubgroup_card hk₁1 hk₂1 hk12ne]
      norm_num
    · exact Subtype.ext (commutingPairSubgroup_sq x.property)
  have hLK : involutionPointHull z ≤
      zpowers (u : G) ⊔ ⁅involutionPointHull z, involutionPointHull z⁆ := by
    refine (closure_le _).mpr fun t' ht' => ?_
    have : t' = (u : G) * ((u : G)⁻¹ * t') := by group
    rw [SetLike.mem_coe, this]
    exact mul_mem_sup (mem_zpowers _) (hclass t' ht')
  have hKsimple : IsSimpleGroup (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hKB
  have hZK : ∀ k ∈ ⁅involutionPointHull z, involutionPointHull z⁆,
      (∀ y ∈ involutionPointHull z, Commute k y) → k = 1 := by
    intro k hk hkc
    have hcen : (⟨k, hk⟩ : (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G)) ∈
        center (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((hkc y (commutator_le_left _ _ y.2)).eq.symm)
    have := hKsimple
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (center (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G)) with hbot | htop
    · rw [hbot, mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      have hcomm' : IsMulCommutative (⁅involutionPointHull z, involutionPointHull z⁆ :
          Subgroup G) := ⟨⟨fun a b => (mem_center_iff.mp (htop ▸ mem_top b) a)⟩⟩
      have hp := (Group.is_simple_iff_prime_card.mp hKsimple)
      obtain ⟨E, hE4, -⟩ := hKrank
      have h4 : 4 ∣ Nat.card (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) :=
        hE4 ▸ Subgroup.card_subgroup_dvd_card E
      have h2 := (Nat.Prime.eq_one_or_self_of_dvd hp 2 (dvd_trans (by norm_num) h4))
      rcases h2 with h2 | h2
      · omega
      · rw [← h2] at h4
        omega
  have hcen_le : ∀ c ∈ involutionPointHull z, (∀ y ∈ involutionPointHull z, Commute c y) →
      c ∈ zpowers (u : G) := by
    intro c hc hcc
    have hcm : c ∈ ((zpowers (u : G) : Subgroup G) : Set G) *
        ((⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G) : Set G) := by
      rw [← mul_normal]
      exact hLK hc
    obtain ⟨y, hy, k, hk, rfl⟩ := hcm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hyc : ∀ w ∈ involutionPointHull z, Commute ((u : G) ^ n) w := fun w hw =>
      (hcomm w hw).zpow_left n
    have hk1 : k = 1 := hZK k hk fun w hw => by
      have h1 := (hcc w hw)
      have h2 := hyc w hw
      have hk' : k = ((u : G) ^ n)⁻¹ * ((u : G) ^ n * k) := by group
      rw [hk']
      exact h2.inv_left.mul_left h1
    change (u : G) ^ n * k ∈ zpowers (u : G)
    rw [hk1, mul_one]
    exact mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hu1 : (u : G) = 1 := by
    by_contra hu1
    have hucentG : (u : G) ∈ center G := by
      rw [mem_center_iff]
      intro g
      have hgu : g * u * g⁻¹ ∈ zpowers (u : G) := by
        refine hcen_le _ (hLn.conj_mem _ u.2 g) fun y hy => ?_
        have hy' : g⁻¹ * y * g ∈ involutionPointHull z := by
          simpa using hLn.conj_mem y hy g⁻¹
        have h := (hcomm _ hy').eq
        show g * u * g⁻¹ * y = y * (g * u * g⁻¹)
        calc g * u * g⁻¹ * y = g * ((u : G) * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by rw [h]
          _ = y * (g * u * g⁻¹) := by group
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hgu
      have hu2z : (u : G) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu2'
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
      · have : (u : G) ^ n = 1 := by
          rw [hk, zpow_mul, hu2z, one_zpow]
        rw [this] at hn
        exfalso
        apply hu1
        have : (u : G) = g⁻¹ * (g * u * g⁻¹) * g := by group
        rw [this, ← hn]
        group
      · have : (u : G) ^ n = u := by
          rw [hk, zpow_add, zpow_mul, hu2z, one_zpow, one_mul, zpow_one]
        rw [this] at hn
        calc g * (u : G) = g * u * g⁻¹ * g := by group
          _ = u * g := by rw [← hn]
    exact hZ _ hucentG (orderOf_eq_prime (by rw [sq]; exact hu2') hu1)
  have hLeq : ⁅involutionPointHull z, involutionPointHull z⁆ = involutionPointHull z := by
    refine le_antisymm (commutator_le_left _ _) ?_
    have := hLK
    rwa [hu1, zpowers_one_eq_bot, bot_sup_eq] at this
  rw [hLeq] at hKB hse hKrank
  exact ⟨hLn, hKB, hse, hKrank, hzL⟩

end CFSG.ComponentClassification.Asc76.L26
