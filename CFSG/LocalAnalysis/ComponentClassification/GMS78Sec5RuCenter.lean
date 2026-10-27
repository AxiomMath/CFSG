module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSylow

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

theorem le_of_isSylowOf_normalizer {R S : Subgroup G} (hR : IsPGroup 2 R)
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) : R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S ⊔ R : Subgroup G) := hSN.isPGroup.to_sup_of_normal_right' hR hSN.le
  exact le_sup_right.trans (hSN.eq_of_le le_sup_left (sup_le hSN.le le_normalizer) hP).le

theorem card_le_card_mul_card {H K P : Subgroup G} (hKH : K ≤ H) (f : G → G)
    (hf : ∀ a ∈ H, f a ∈ P) (hinj : ∀ a ∈ H, ∀ b ∈ H, f a = f b → a⁻¹ * b ∈ K) :
    Nat.card H ≤ Nat.card P * Nat.card K := by
  have hinj' : Function.Injective
      (fun q : H ⧸ K.subgroupOf H => (⟨f ((q.out : H) : G), hf _ (q.out).2⟩ : P)) := by
    intro q q' h
    have h1 : f ((q.out : H) : G) = f ((q'.out : H) : G) := congrArg Subtype.val h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, mem_subgroupOf]
    exact hinj _ (q.out).2 _ (q'.out).2 h1
  have hidx : (K.subgroupOf H).index ≤ Nat.card P := Nat.card_le_card_of_injective _ hinj'
  have h1 := (K.subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ hidx

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {y d : G}

theorem card_sylow_normalizer
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) {S : Subgroup G}
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) : Nat.card S = 2 ^ 14 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Nat.card R = 2 ^ 11 := by
    rw [hS.card_R hR₂, card_T_eq hS h4]
    norm_num
  have hN : Nat.card (normalizer (R : Set G)) = 2 ^ 14 * 21 := by
    have h1 := (R.subgroupOf (normalizer (R : Set G))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv] at h1
    have h2 : (R.subgroupOf (normalizer (R : Set G))).index = 168 :=
      relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
    rw [h2, hR] at h1
    rw [← h1]
    norm_num
  rw [hSN.card_eq, hN, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21), add_zero]

theorem exists_center_eq
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) {S : Subgroup G}
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) :
    ∃ f ∈ gmsA L T, f ≠ 1 ∧ S ⊓ centralizer (S : Set G) = zpowers f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRS : R ≤ S := le_of_isSylowOf_normalizer hS.isR.isPGroup hSN
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hAS : gmsA L T ≤ S := hAR.trans hRS
  have hCA := centralizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL
  obtain ⟨hAel, h8⟩ := hS.isElemAbelian_gmsA_and_card
  have hSA : ∀ s ∈ S, s ∈ normalizer (gmsA L T : Set G) := fun s hs =>
    hS.normalizer_le_normalizer_gmsA hR₂ (hSN.le hs)
  set Z := S ⊓ centralizer (S : Set G) with hZdef
  have hZA : Z ≤ gmsA L T := by
    intro z hz
    obtain ⟨-, hzc⟩ := mem_inf.mp hz
    have hzR : z ∈ R := by
      rw [← hCA]
      exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hzc b (hAS hb)
    exact hS.mem_gmsA_of_forall_commute hR₂ hzR fun r hr => mem_centralizer_iff.mp hzc r (hRS hr)
  have hZc : ∀ z ∈ Z, ∀ s ∈ S, s * z * s⁻¹ = z := by
    intro z hz s hs
    rw [mem_centralizer_iff.mp (mem_inf.mp hz).2 s hs]
    group
  obtain ⟨f, hfZ, hf1⟩ : ∃ f ∈ Z, f ≠ 1 := by
    have hSnt : Nontrivial S := by
      obtain ⟨a, ha, ha1⟩ : ∃ a ∈ gmsA L T, a ≠ 1 := by
        by_contra h
        push Not at h
        have h1 : gmsA L T = ⊥ := (eq_bot_iff_forall _).mpr h
        rw [h1, card_bot] at h8
        exact absurd h8 (by norm_num)
      exact ⟨⟨⟨a, hAS ha⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have := hSN.isPGroup.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center S)
    refine ⟨((c : S) : G), mem_inf.mpr ⟨(c : S).2, mem_centralizer_iff.mpr fun h hh => ?_⟩,
      fun h => hc (Subtype.ext (Subtype.ext h))⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  have hcardS := card_sylow_normalizer hS h34 hR₂ h4 hCV hNS hSN
  have hR : Nat.card R = 2 ^ 11 := by
    rw [hS.card_R hR₂, card_T_eq hS h4]
    norm_num
  have hZ2 : Nat.card Z ≤ 2 := by
    have hdvd : Nat.card Z ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8]
      exact Subgroup.card_dvd_of_le hZA
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    by_contra hlt
    interval_cases k
    · rw [hk] at hlt
      norm_num at hlt
    · rw [hk] at hlt
      norm_num at hlt
    ·
      obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ gmsA L T, a₀ ∉ Z := by
        by_contra h
        push Not at h
        have : Nat.card (gmsA L T) ≤ Nat.card Z := Subgroup.card_le_of_le h
        rw [h8, hk] at this
        norm_num at this
      have hidx : (Z.subgroupOf (gmsA L T)).index = 2 := by
        have h1 := (Z.subgroupOf (gmsA L T)).card_mul_index
        rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hk, h8] at h1
        omega
      have hcos : ∀ b ∈ gmsA L T, b ∉ Z → a₀⁻¹ * b ∈ Z := by
        intro b hb hbZ
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a₀, ha₀⟩ : gmsA L T)⁻¹)
          (b := ⟨b, hb⟩)).mpr (by
            simp only [mem_subgroupOf, inv_mem_iff]
            exact ⟨fun h => absurd h ha₀Z, fun h => absurd h hbZ⟩)
        simpa [mem_subgroupOf] using h1
      have hf' : ∀ s ∈ S, a₀⁻¹ * (s * a₀ * s⁻¹) ∈ Z := by
        intro s hs
        have hsa : s * a₀ * s⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp (hSA s hs) a₀).mp ha₀
        refine hcos _ hsa fun h => ha₀Z ?_
        have h1 := hZc _ h s⁻¹ (inv_mem hs)
        rw [show s⁻¹ * (s * a₀ * s⁻¹) * s⁻¹⁻¹ = a₀ by group] at h1
        rw [← h1] at h
        exact h
      have hcount := card_le_card_mul_card hRS (fun s => a₀⁻¹ * (s * a₀ * s⁻¹)) hf'
        (fun s hs s' hs' h => by
          rw [← hCA]
          refine mem_centralizer_iff.mpr fun b hb => ?_
          have hs1 : s * a₀ * s⁻¹ = s' * a₀ * s'⁻¹ := mul_left_cancel h
          have hca : (s⁻¹ * s') * a₀ * (s⁻¹ * s')⁻¹ = a₀ := by
            calc (s⁻¹ * s') * a₀ * (s⁻¹ * s')⁻¹ = s⁻¹ * (s' * a₀ * s'⁻¹) * s := by group
              _ = s⁻¹ * (s * a₀ * s⁻¹) * s := by rw [hs1]
              _ = a₀ := by group
          have hcz : ∀ z ∈ Z, (s⁻¹ * s') * z * (s⁻¹ * s')⁻¹ = z := fun z hz =>
            hZc z hz _ (mul_mem (inv_mem hs) hs')
          have hcb : (s⁻¹ * s') * b * (s⁻¹ * s')⁻¹ = b := by
            by_cases hbZ : b ∈ Z
            · exact hcz b hbZ
            · have h2 := hcz _ (hcos b hb hbZ)
              calc (s⁻¹ * s') * b * (s⁻¹ * s')⁻¹ =
                  ((s⁻¹ * s') * a₀ * (s⁻¹ * s')⁻¹) *
                    ((s⁻¹ * s') * (a₀⁻¹ * b) * (s⁻¹ * s')⁻¹) := by group
                _ = a₀ * (a₀⁻¹ * b) := by rw [hca, h2]
                _ = b := by group
          calc b * (s⁻¹ * s') = ((s⁻¹ * s') * b * (s⁻¹ * s')⁻¹) * (s⁻¹ * s') := by rw [hcb]
            _ = (s⁻¹ * s') * b := by group)
      rw [hcardS, hk, hR] at hcount
      norm_num at hcount
    ·
      apply hNS
      have hZA' : Z = gmsA L T := (Subgroup.eq_of_le_of_card_ge hZA (by rw [h8, hk]; norm_num))
      have hSR : S = R := by
        refine le_antisymm (fun s hs => ?_) hRS
        rw [← hCA]
        refine mem_centralizer_iff.mpr fun b hb => ?_
        rw [← hZA'] at hb
        exact (mem_centralizer_iff.mp (mem_inf.mp hb).2 s hs).symm
      rw [hSR] at hSN
      exact hSN
  have hf2 : orderOf f = 2 := by
    refine orderOf_eq_prime ?_ hf1
    exact hAel.2 f (hZA hfZ)
  refine ⟨f, hZA hfZ, hf1, (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hfZ) ?_).symm⟩
  rw [Nat.card_zpowers, hf2]
  exact hZ2

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
