module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.DerV7

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section V7Swap

variable {G : Type} [Group G] [Finite G]

theorem v7_of_swap {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G} (hpair : Stage1Pair G z S q L₁ L₂)
    (htwo : TwoClassData G z S L₁ L₂ q x) {t : G} (htS : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) :
    ∃ (V : Subgroup G) (kk : G), V7 z S V ∧ kk ∈ Cen z ∧ kk⁻¹ * t * kk ∈ S ∧
      ∀ v ∈ V, (kk⁻¹ * t * kk) * v = v * (kk⁻¹ * t * kk) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := ctx.sylow
  have hSC : S ≤ Cen z := hSsyl.le
  obtain ⟨-, -, -, V₀, hV₀L, hV₀4, hV₀3, hV₀c⟩ := htwo.swap_conseq t htS htc hsw
  have htne : t ≠ z := by
    intro htz
    apply hpair.ne
    obtain ⟨ht, h1, h2⟩ := hsw
    have hcen : toBar z ⟨t, ht⟩ ∈ Subgroup.center (CentralizerBar z) := by
      have : (⟨t, ht⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext htz
      rw [this]
      exact toBar_z_mem_center z
    exact (h1.symm.trans (conjugate_of_center hcen L₁)).symm
  have hV₀C : V₀ ≤ Cen z := hV₀L.trans (LC_le_Cen z)
  have htC : t ∈ Cen z := hSC htS
  have hWC : V₀ ⊔ zpowers t ≤ Cen z := sup_le hV₀C (Subgroup.zpowers_le.mpr htC)
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a t from (hV₀c a ha).symm) n).eq
  have hW2 : IsPGroup 2 ↥(V₀ ⊔ zpowers t) := by
    obtain ⟨a, ha⟩ := orderOf_mem_S ctx htS
    have : IsElementaryAbelian 2 ↥V₀ := hV₀4.1
    intro w
    obtain ⟨v, hv, u, hu, hwvu⟩ := exists_mul_of_mem_sup_of_commute hcomm w.2
    refine ⟨a + 1, ?_⟩
    apply Subtype.ext
    have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have ht0 : t ^ (2 ^ a) = 1 := by rw [← ha]; exact pow_orderOf_eq_one t
    have hu1 : (t ^ m) ^ (2 ^ a) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht0, one_zpow]
    have hc : Commute v (t ^ m) := hcomm v hv _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) m)
    have hv' : v ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, hv2, one_pow]
    have hu' : (t ^ m) ^ 2 ^ (a + 1) = 1 := by rw [pow_succ, pow_mul, hu1, one_pow]
    show ((w : G)) ^ (2 ^ (a + 1)) = 1
    rw [hwvu, hc.mul_pow, hv', hu', one_mul]
  have hW' : IsPGroup 2 ↥((V₀ ⊔ zpowers t).subgroupOf (Cen z)) := hW2.comap_subtype
  obtain ⟨Q, hWQ⟩ := hW'.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥(Cen z)).map (Cen z).subtype) (Cen z) :=
    ⟨Q, rfl⟩
  obtain ⟨kk, hkk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSsyl hP'
  have hWP' : ∀ w ∈ V₀ ⊔ zpowers t, kk⁻¹ * w * kk ∈ S := fun w hw =>
    (hconj w).mp ⟨⟨w, hWC hw⟩, hWQ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hV₀W : V₀ ≤ V₀ ⊔ zpowers t := le_sup_left
  have htW : t ∈ V₀ ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hV4 : IVK.IsFourSubgroup (conjugate V₀ kk) := isFour_conjugate kk hV₀4
  have hV3 : 3 ∣ AutOrd (Cen z) (conjugate V₀ kk) := by
    rw [autOrd_conjugate hkk]
    rcases hV₀3 with h | h
    · rw [h]
    · rw [h]; decide
  have hVL : conjugate V₀ kk ≤ LC z := conjugate_le_LC hkk hV₀L
  have hconjV := conj_of_three_dvd hV4 hV3
  have hcommV : ∀ v ∈ conjugate V₀ kk, (kk⁻¹ * t * kk) * v = v * (kk⁻¹ * t * kk) := by
    intro v hv
    rw [mem_conjugate_iff] at hv
    have h1 := hV₀c _ hv
    calc kk⁻¹ * t * kk * v = kk⁻¹ * (t * (kk * v * kk⁻¹)) * kk := by group
      _ = kk⁻¹ * ((kk * v * kk⁻¹) * t) * kk := by rw [h1]
      _ = v * (kk⁻¹ * t * kk) := by group
  refine ⟨conjugate V₀ kk, kk, ⟨?_, hVL, hV4, hV3, hconjV, ?_⟩, hkk, hWP' t htW, hcommV⟩
  · intro v hv
    rw [mem_conjugate_iff] at hv
    have h1 := hWP' (kk * v * kk⁻¹) (hV₀W hv)
    have e : kk⁻¹ * (kk * v * kk⁻¹) * kk = v := by group
    rwa [e] at h1
  · intro hC
    obtain ⟨q', L₁', L₂', x', hpair', htwo'⟩ := hC
    refine ⟨?_, kk⁻¹ * t * kk, hWP' t htW, ?_, ?_, hcommV⟩
    · intro v hv hv2 hvz
      have hvL : v ∈ LC z := hVL hv
      have hvne : v ≠ z := by
        intro hvz'
        have hzV : z ∈ conjugate V₀ kk := hvz' ▸ hv
        have hz1 : z ≠ 1 := by
          intro h
          have := ctx.orderOf_z
          rw [h, orderOf_one] at this
          omega
        obtain ⟨x1, hx1, y1, hy1, hx1o, hy1o, hxy⟩ := exists_two_involutions_of_isFour hV4
        have hx1z : x1 = z := by
          obtain ⟨c, hc, hcz⟩ := hconjV z hzV hz1 x1 hx1 (fun h => by rw [h, orderOf_one] at hx1o; omega)
          have := Subgroup.mem_centralizer_singleton_iff.mp hc
          rw [← hcz, this]; group
        have hy1z : y1 = z := by
          obtain ⟨c, hc, hcz⟩ := hconjV z hzV hz1 y1 hy1 (fun h => by rw [h, orderOf_one] at hy1o; omega)
          have := Subgroup.mem_centralizer_singleton_iff.mp hc
          rw [← hcz, this]; group
        exact hxy (hx1z.trans hy1z.symm)
      have hxv : IsConj x' v := (htwo'.invol_L v hvL hv2 hvne).1
      have hzx : IsConj z x' := hvz.trans hxv.symm
      exact htwo'.x_nonCentral (isCentralInvolution_of_isConj' ctx.central hzx)
    · obtain ⟨c, hc⟩ := isConj_iff.1 htc
      refine isConj_iff.2 ⟨kk⁻¹ * c, ?_⟩
      calc kk⁻¹ * c * z * (kk⁻¹ * c)⁻¹ = kk⁻¹ * (c * z * c⁻¹) * kk := by group
        _ = kk⁻¹ * t * kk := by rw [hc]
    · intro h
      apply htne
      have hkz : kk * z * kk⁻¹ = z := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hkk
        rw [this]; group
      calc t = kk * (kk⁻¹ * t * kk) * kk⁻¹ := by group
        _ = z := by rw [h, hkz]

end V7Swap

end CFSG.GH74.GLS.Stage2.Bender.Thm1
