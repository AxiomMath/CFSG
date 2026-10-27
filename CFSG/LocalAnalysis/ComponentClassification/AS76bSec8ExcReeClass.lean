module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeCoords
public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore
public import CFSG.Quasithin.Background.SmithB42F4Base

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fam_8_eq sylowL_zero')


section Groups

variable (m : ℕ) (K : Type) [Field K]

@[expose] noncomputable def zK :
    Subgroup (ModGL F4.tag K) :=
  closure (Set.range (centralZ K m))

@[expose] noncomputable def tK :
    Subgroup (ModGL F4.tag K) :=
  closure (Set.range (sylowL m K))

end Groups

theorem mem_closure_range_iff {X : Type*} [Group X] {K : Type*} [Field K] [CharP K 2]
    {ζ : K → X} (h0 : ζ 0 = 1) (hmul : ∀ s t, ζ s * ζ t = ζ (s + t)) {g : X} :
    g ∈ closure (Set.range ζ) ↔ ∃ c, ζ c = g := by
  constructor
  · intro hg
    induction hg using closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, h0⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, (hmul c d).symm⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      refine ⟨c, (inv_eq_of_mul_eq_one_right ?_).symm⟩
      rw [hmul, CharTwo.add_self_eq_zero, h0]
  · rintro ⟨c, rfl⟩
    exact subset_closure ⟨c, rfl⟩

section Model

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem mem_zK
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K} :
    g ∈ zK m K ↔ ∃ c, centralZ K m c = g := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact mem_closure_range_iff centralZ_zero (centralZ_mul hK)

theorem mem_tK
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K} :
    g ∈ tK m K ↔ ∃ c, sylowL m K c = g := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact mem_closure_range_iff sylowL_zero' (sylowL_mul hK)

theorem card_zK
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {Γ : Subgroup (ModGL F4.tag K)} (hΓ : zK m K ≤ Γ) :
    Nat.card ((zK m K).subgroupOf Γ) = 2 ^ (2 * m + 1) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hΓ).toEquiv, ← hK]
  set φ : K → zK m K := fun c => ⟨centralZ K m c, (mem_zK hK).2 ⟨c, rfl⟩⟩ with hφ
  have hinj : Function.Injective φ := by
    intro c d h
    have h1 : centralZ K m c = centralZ K m d := by
      have := congrArg Subtype.val h
      simpa [hφ] using this
    exact centralZ_injective h1
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨c, hc⟩ := (mem_zK hK).1 g.2
    exact ⟨c, Subtype.ext hc⟩
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

theorem card_tK
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {Γ : Subgroup (ModGL F4.tag K)} (hΓ : tK m K ≤ Γ) :
    Nat.card ((tK m K).subgroupOf Γ) = 2 ^ (2 * m + 1) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hΓ).toEquiv, ← hK]
  set φ : K → tK m K := fun c => ⟨sylowL m K c, (mem_tK hK).2 ⟨c, rfl⟩⟩ with hφ
  have hinj : Function.Injective φ := by
    intro c d h
    have h1 : sylowL m K c = sylowL m K d := by
      have := congrArg Subtype.val h
      simpa [hφ] using this
    exact sylowL_injective h1
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨c, hc⟩ := (mem_tK hK).1 g.2
    exact ⟨c, Subtype.ext hc⟩
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

end Model

section Classes

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem zK_le
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) : zK m K ≤ F4.reeGamma K m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzc, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact (mem_inf.1 (hzc c).1).1

theorem tK_le
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) : tK m K ≤ F4.reeGamma K m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htc, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact (mem_inf.1 (htc c).1).1

omit [Finite K] [CharP K F4.prime] in
theorem odd_card_units (hK : Nat.card K = 2 ^ (2 * m + 1)) : Odd (Nat.card Kˣ) := by
  rw [Nat.card_units, hK]
  have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have h2 : Even (2 ^ (2 * m + 1)) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨r, hr⟩ := h2
  exact ⟨r - 1, by omega⟩

omit [CharP K F4.prime] in
theorem exists_generator_units : ∃ g : Kˣ, ∀ x : Kˣ, ∃ k : ℕ, g ^ k = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, fun x => (mem_powers_iff_mem_zpowers.2 (hg x))⟩

theorem centreData_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m) :
    CentreData (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m)
      ((zK m K).subgroupOf (F4.reeGamma K m)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hzC, -, -, -, -, hzc, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  refine centreData_of_inf hz ((mem_zK hK).2 ⟨1, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · intro h
    exact one_ne_zero (centralZ_injective (h.trans centralZ_zero.symm))
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := (mem_zK hK).1 ha
    obtain ⟨d, rfl⟩ := (mem_zK hK).1 hb
    rw [centralZ_mul hK, centralZ_mul hK, add_comm]
  · intro a ha
    obtain ⟨c, rfl⟩ := (mem_zK hK).1 ha
    rw [centralZ_mul hK, CharTwo.add_self_eq_zero, centralZ_zero]
  · intro w hw c hc hcz
    obtain ⟨d, rfl⟩ := (mem_zK hK).1 hw
    exact (mem_centralizer_singleton_iff.1
      ((hzc d).2 (mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hcz⟩))).symm
  · intro w hw hwz hwc _
    have hwC : w ∈ F4.reeGamma K m ⊓ centralizer {centralZ K m 1} :=
      mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwz⟩
    have hwV : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
      have h1 : (⟨w, hwC⟩ : ↥(F4.reeGamma K m ⊓ centralizer {centralZ K m 1})) ∈
          centralizer (((F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩).subgroupOf
            (F4.reeGamma K m ⊓ centralizer {centralZ K m 1}) : Subgroup _) : Set _) := by
        rw [mem_centralizer_iff]
        intro v _
        exact Subtype.ext (hwc v (mem_inf.1 v.2).1
          (mem_centralizer_singleton_iff.1 (mem_inf.1 v.2).2)).symm
      exact mem_subgroupOf.1 (hzC h1)
    have hwU := reeFixedOrbitComplementUnipotent_le _ hwV
    have hcen : (⟨w, hwU⟩ : F4.reeFixedPosUnipotent K m) ∈
        center (F4.reeFixedPosUnipotent K m) := by
      rw [mem_center_iff]
      intro u
      exact Subtype.ext (hwc u (reeFixedPosUnipotent_le_reeGamma' u.2)
        (commute_centralZ hm hK u.2 1)).symm
    have h2 : w ∈ ((center (F4.reeFixedPosUnipotent K m)).map
        (F4.reeFixedPosUnipotent K m).subtype : Set (ModGL F4.tag K)) := ⟨_, hcen, rfl⟩
    rw [coe_center_eq_range_centralZ hm hK] at h2
    obtain ⟨c, hc⟩ := h2
    exact (mem_zK hK).2 ⟨c, hc⟩

theorem centreData_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    CentreData (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)
      ((tK m K).subgroupOf (F4.reeGamma K m)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨-, -, -, -, -, ht1, -, -, -, -, -, -, -, -, htC, -, -, -, htc, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  have hR₁C : rankOneGroupOne K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_right
  have hAR : sylowA m K 1 ∈ rankOneGroupOne K m :=
    subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (sylowA_mem_U1 hK 1)))
  have hnR : weylOne K ∈ rankOneGroupOne K m := subset_closure (Set.mem_union_right _ rfl)
  refine centreData_of_inf ht ((mem_tK hK).2 ⟨1, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · intro h
    exact one_ne_zero (sylowL_injective (h.trans sylowL_zero'.symm))
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := (mem_tK hK).1 ha
    obtain ⟨d, rfl⟩ := (mem_tK hK).1 hb
    rw [sylowL_mul hK, sylowL_mul hK, add_comm]
  · intro a ha
    obtain ⟨c, rfl⟩ := (mem_tK hK).1 ha
    rw [sylowL_mul hK, CharTwo.add_self_eq_zero, sylowL_zero']
  · intro w hw c hc hct
    obtain ⟨d, rfl⟩ := (mem_tK hK).1 hw
    exact (mem_centralizer_singleton_iff.1
      ((htc d).2 (mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hct⟩))).symm
  · intro w hw hwt hwc _
    have hwC : w ∈ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} :=
      mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwt⟩
    have hwQ : w ∈ tKernel K m := by
      have h1 : (⟨w, hwC⟩ : ↥(F4.reeGamma K m ⊓ centralizer {sylowL m K 1})) ∈
          centralizer (((tKernel K m).subgroupOf
            (F4.reeGamma K m ⊓ centralizer {sylowL m K 1}) : Subgroup _) : Set _) := by
        rw [mem_centralizer_iff]
        intro v _
        exact Subtype.ext (hwc v (mem_inf.1 v.2).1
          (mem_centralizer_singleton_iff.1 (mem_inf.1 v.2).2)).symm
      exact mem_subgroupOf.1 (htC h1)
    have hc : ∀ r ∈ rankOneGroupOne K m, w * r = r * w := fun r hr =>
      hwc r (mem_inf.1 (hR₁C hr)).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 (hR₁C hr)).2)
    obtain ⟨l, hl⟩ := eq_sylowL_of_commute hK hwQ (hc _ hAR) (hc _ hnR).symm
    exact (mem_tK hK).2 ⟨l, hl⟩

theorem regular_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∃ u : F4.reeGamma K m, Regular ((zK m K).subgroupOf (F4.reeGamma K m)) u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzc, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨g, hgen⟩ := exists_generator_units (K := K)
  have hu : LargeReeCover.torusPair m (g, 1) ∈ F4.reeGamma K m :=
    LargeReeCover.torusPair_mem_reeGamma m hK (g, 1)
  refine ⟨⟨_, hu⟩, regular_of_scalar (ζ := centralZ K m) centralZ_injective centralZ_zero
    (fun _ => mem_zK hK) (zK_le hm hK) hu (l := (g : K) ^ 2 ^ m) ?_
    (fun c => torusPair_conj_centralZ hK g 1 c) ?_ ?_⟩
  · intro c hc
    have hσ : largeReeSigma m c ≠ 0 := (largeReeSigma_eq_zero_iff c).not.2 hc
    obtain ⟨k, hk⟩ := hgen (Units.mk0 _ hσ)
    refine ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk, Units.val_mk0,
      largeReeSigma_pow_two_pow hK]
  · have h1 : orderOf (LargeReeCover.torusPair m (g, 1)) ∣ orderOf ((g, 1) : Kˣ × Kˣ) :=
      orderOf_map_dvd _ _
    have h2 : orderOf ((g, 1) : Kˣ × Kˣ) ∣ Nat.card (Kˣ × Kˣ) := orderOf_dvd_natCard _
    have h3 : Odd (Nat.card (Kˣ × Kˣ)) := by
      rw [Nat.card_prod]
      exact (odd_card_units hK).mul (odd_card_units hK)
    exact h3.of_dvd_nat (h1.trans h2)
  · intro a ha haz c
    exact mem_centralizer_singleton_iff.1
      ((hzc c).2 (mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 haz⟩))

theorem regular_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∃ u : F4.reeGamma K m, Regular ((tK m K).subgroupOf (F4.reeGamma K m)) u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htc, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨g, hgen⟩ := exists_generator_units (K := K)
  have hu : LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 1) (LargeReeCover.f4i 2) g ∈
      F4.reeGamma K m := by
    rw [← rankOneTorusPair_right]
    exact LargeReeCover.torusPair_mem_reeGamma m hK (1, g)
  refine ⟨⟨_, hu⟩, regular_of_scalar (ζ := sylowL m K) sylowL_injective sylowL_zero'
    (fun _ => mem_tK hK) (tK_le hm hK) hu (l := ((g ^ ((1 : ℤ) - 2 ^ m) : Kˣ) : K)) ?_
    (fun c => torusTwo_conj_sylowL hK g c) ?_ ?_⟩
  · intro c hc
    obtain ⟨k, hk⟩ := hgen ((Units.mk0 c hc) ^ ((2 : ℤ) * 2 ^ m + 2))
    refine ⟨k, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hk, zpow_one_sub_surj hK, Units.val_mk0]
  · have h1 : orderOf (LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 1)
        (LargeReeCover.f4i 2) g) ∣ orderOf g := orderOf_map_dvd _ _
    exact (odd_card_units hK).of_dvd_nat (h1.trans (orderOf_dvd_natCard g))
  · intro a ha hat c
    exact mem_centralizer_singleton_iff.1
      ((htc c).2 (mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 hat⟩))

theorem sylowData_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m) :
    SylowData (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m)
      ((zK m K).subgroupOf (F4.reeGamma K m)) := by
  obtain ⟨hz1, hz2, hz3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨hR₂s, hR₂nc⟩ := isSimpleGroup_rankOneGroupTwo hm hK
  have hR₂C : rankOneGroupTwo K m ≤ F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
    rw [hz1]
    exact le_sup_right
  have hVC : F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ≤
      F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
    rw [hz1]
    exact le_sup_left
  have hR₂Γ : rankOneGroupTwo K m ≤ F4.reeGamma K m := hR₂C.trans inf_le_left
  set n := weylOne K * weylTwo K * weylOne K with hn
  have hnΓ : n ∈ F4.reeGamma K m := mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  have hB : n * sylowB m K 0 1 * n⁻¹ = centralZ K m 1 := by
    rw [hn, weyl_conj_sylowB_zero, sylowH_zero_eq_centralZ]
  have hBR : sylowB m K 0 1 ∈ rankOneGroupTwo K m :=
    subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (sylowB_mem_U2 hK 0 1)))
  have hB10 : sylowB m K 1 0 ∈ rankOneGroupTwo K m :=
    subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (sylowB_mem_U2 hK 1 0)))
  have hn₂ : weylTwo K ∈ rankOneGroupTwo K m := subset_closure (Set.mem_union_right _ rfl)
  have hB1 : sylowB m K 0 1 ≠ 1 := fun h =>
    one_ne_zero (sylowB_injective hK (h.trans sylowB_zero_zero.symm)).2
  have hA1U : sylowA m K 1 ∈ F4.reeFixedPosUnipotent K m :=
    reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1)
  have hB01U : sylowB m K 0 1 ∈ F4.reeFixedPosUnipotent K m :=
    reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 0 1)
  refine sylowData_of_inf hz fun w hw hwz hwc _ => ?_
  have hcommR : ∀ r ∈ rankOneGroupTwo K m, w * r = r * w := by
    refine commute_of_simple (S := {s | ∃ b ∈ F4.reeGamma K m, b * centralZ K m 1 * b⁻¹ = s})
      ?_ ⟨n⁻¹, inv_mem hnΓ, by rw [← hB]; group⟩ hBR hB1 ?_
    · rintro r hr s ⟨b, hb, rfl⟩
      exact ⟨r * b, mul_mem (hR₂Γ hr) hb, by group⟩
    · rintro s ⟨b, hb, rfl⟩ hsR
      exact hwc b hb (mem_centralizer_singleton_iff.1 (mem_inf.1 (hR₂C hsR)).2)
  have hwV : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
    refine mem_of_commute_of_sup (le_normalizer_of_normal_subgroupOf hz3 hVC hR₂C) hz2
      (center_eq_bot_of_simple hR₂nc) ?_ hcommR
    rw [← hz1]
    exact mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwz⟩
  have h₃ : w * (sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹) =
      sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹ * w := by
    have hb : sylowA m K 1 * n⁻¹ ∈ F4.reeGamma K m :=
      mul_mem (reeFixedPosUnipotent_le_reeGamma' hA1U) (inv_mem hnΓ)
    have he : sylowA m K 1 * n⁻¹ * centralZ K m 1 * (sylowA m K 1 * n⁻¹)⁻¹ =
        sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹ := by
      rw [← hB]
      group
    have hmem : sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹ ∈ F4.reeFixedPosUnipotent K m :=
      mul_mem (mul_mem hA1U hB01U) (inv_mem hA1U)
    have h1 := hwc _ hb (by rw [he]; exact commute_centralZ hm hK hmem 1)
    rwa [he] at h1
  obtain ⟨i, hi⟩ := eq_centralZ_of_commute hK hwV (hcommR _ hBR) (hcommR _ hB10) h₃
    (hcommR _ hn₂).symm
  exact (mem_zK hK).2 ⟨i, hi⟩

theorem sylowData_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    SylowData (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)
      ((tK m K).subgroupOf (F4.reeGamma K m)) := by
  obtain ⟨-, -, -, -, -, ht1, ht2, ht3, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨hR₁s, hR₁nc⟩ := isSimpleGroup_rankOneGroupOne hm hK
  have hR₁C : rankOneGroupOne K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_right
  have hQC : tKernel K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_left
  have hR₁Γ : rankOneGroupOne K m ≤ F4.reeGamma K m := hR₁C.trans inf_le_left
  set n := weylTwo K * weylOne K * weylTwo K with hn
  have hnΓ : n ∈ F4.reeGamma K m := mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem
  have hA : n * sylowA m K 1 * n⁻¹ = sylowL m K 1 := weyl_conj_sylowA_one
  have hAR : sylowA m K 1 ∈ rankOneGroupOne K m :=
    subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (sylowA_mem_U1 hK 1)))
  have hn₁ : weylOne K ∈ rankOneGroupOne K m := subset_closure (Set.mem_union_right _ rfl)
  have hA1 : sylowA m K 1 ≠ 1 := fun h => one_ne_zero (sylowA_injective (h.trans sylowA_zero.symm))
  refine sylowData_of_inf ht fun w hw hwt hwc _ => ?_
  have hcommR : ∀ r ∈ rankOneGroupOne K m, w * r = r * w := by
    refine commute_of_simple (S := {s | ∃ b ∈ F4.reeGamma K m, b * sylowL m K 1 * b⁻¹ = s})
      ?_ ⟨n⁻¹, inv_mem hnΓ, by rw [← hA]; group⟩ hAR hA1 ?_
    · rintro r hr s ⟨b, hb, rfl⟩
      exact ⟨r * b, mul_mem (hR₁Γ hr) hb, by group⟩
    · rintro s ⟨b, hb, rfl⟩ hsR
      exact hwc b hb (mem_centralizer_singleton_iff.1 (mem_inf.1 (hR₁C hsR)).2)
  have hwQ : w ∈ tKernel K m := by
    refine mem_of_commute_of_sup (le_normalizer_of_normal_subgroupOf ht3 hQC hR₁C) ht2
      (center_eq_bot_of_simple hR₁nc) ?_ hcommR
    rw [← ht1]
    exact mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwt⟩
  obtain ⟨l, hl⟩ := eq_sylowL_of_commute hK hwQ (hcommR _ hAR) (hcommR _ hn₁).symm
  exact (mem_tK hK).2 ⟨l, hl⟩

theorem classesCover_ree
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m)
    (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    ClassesCover [(⟨centralZ K m 1, hz⟩ : F4.reeGamma K m), ⟨sylowL m K 1, ht⟩] := by
  intro x hx2 hx1
  have hx2' : (x : ModGL F4.tag K) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, hx2, Subgroup.coe_one]
  have hx1' : (x : ModGL F4.tag K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases (large_Ree_every_involution_fuses m hm K hK).1 x x.2 hx2' hx1' with
    ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
  · rw [sylowH_zero_eq_centralZ] at hgx
    refine ⟨_, List.mem_cons_self, isConj_iff.2 ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hgx]
    group
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      isConj_iff.2 ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hgx]
    group

theorem charTwo_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m) :
    CharTwo (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hzP, hzC, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  refine charTwo_of_inf _ ?_
  unfold CFSG.IsCharacteristicP
  rw [hzP]
  exact hzC

theorem charTwo_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    CharTwo (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, htP, htC, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  refine charTwo_of_inf _ ?_
  unfold CFSG.IsCharacteristicP
  rw [htP]
  exact htC

theorem fusion_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    ∃ a : F4.reeGamma K m, FusionData ((zK m K).subgroupOf (F4.reeGamma K m)) a ∧
      OtherClass ((zK m K).subgroupOf (F4.reeGamma K m)) a
        {w | ∃ y' ∈ [(⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)], IsConj y' w} := by
  set n := weylOne K * weylTwo K * weylOne K with hn
  have hnΓ : n ∈ F4.reeGamma K m := mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  have hconj : ∀ c, n⁻¹ * centralZ K m c * n = sylowB m K 0 c := fun c => by
    rw [hn, ← sylowH_zero_eq_centralZ, ← weyl_conj_sylowB_zero c]
    group
  have hBU : ∀ c, sylowB m K 0 c ∈ F4.reeFixedPosUnipotent K m := fun c =>
    reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 0 c)
  have hval : ∀ (z z' : F4.reeGamma K m) (i j : K), centralZ K m i = z → centralZ K m j = z' →
      ((z * (⟨n, hnΓ⟩⁻¹ * z' * (⟨n, hnΓ⟩⁻¹)⁻¹) : F4.reeGamma K m) : ModGL F4.tag K) =
        centralZ K m i * sylowB m K 0 j := by
    intro z z' i j hi hj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hi, ← hj, hconj]
  refine ⟨⟨n, hnΓ⟩⁻¹, ⟨fun z hz z' hz' => ?_, fun z hz z' hz' h => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz)
    obtain ⟨j, hj⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz')
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hi, ← hj, hconj]
    exact (commute_centralZ hm hK (hBU j) i).symm
  · obtain ⟨i, hi⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz)
    obtain ⟨j, hj⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz')
    have h0 := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h0
    have h1 : centralZ K m i = sylowB m K 0 j := by
      rw [hi, h0, ← hj, hconj]
    have heq : sylowVec m K ![0, 0, 0, 0, 0, 0, 0, 0, i, 0, 0, 0] =
        sylowVec m K ![0, 0, j, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
      show sylowV m K 0 0 0 0 0 0 0 0 i 0 0 0 = sylowV m K 0 0 j 0 0 0 0 0 0 0 0 0
      rw [← CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.fam_8_eq,
        ← CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.fam_2_eq]
      show sylowH m K 0 i = sylowB m K 0 j
      rw [sylowH_zero_eq_centralZ, h1]
    have h8 := congrFun ((bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _) heq) 8
    simp only [Matrix.cons_val] at h8
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hi, h8, centralZ_zero]
  · intro z hz hz1 z' hz' hz'1
    obtain ⟨i, hi⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz)
    obtain ⟨j, hj⟩ := (mem_zK hK).1 (mem_subgroupOf.1 hz')
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hz1 (Subtype.ext (by rw [← hi, centralZ_zero, Subgroup.coe_one]))
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hz'1 (Subtype.ext (by rw [← hj, centralZ_zero, Subgroup.coe_one]))
    obtain ⟨g, hg, hgt⟩ := CFSG.Quasithin.B42F4.isTConj_sylowB_mul_sylowH hK hj0 hi0
    refine ⟨_, List.mem_singleton_self _, isConj_iff.2 ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩⟩
    rw [hval z z' i j hi hj]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hgt, sylowH_zero_eq_centralZ, commute_centralZ hm hK (hBU j) i]
    group

end Classes

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
