module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalAbs
public import CFSG.HardMathSupport.Dickson.Bal207.SzNorm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoF

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Generic

variable {K : Type*} [Group K] {p : ℕ}

theorem coreFreeAt_of_coprime_inner (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hO : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g ∈ innerAut K) {x : MulAut K}
    (hN : NoNormalPPrime p (fixSub x)) : CoreFreeAt p x := by
  refine ⟨hN, fun g hg hgx hfix => ?_⟩
  obtain ⟨k, rfl⟩ := hO g hg
  have hk : k ∈ fixSub x := mem_fixSub_of_commute hinj hgx.symm
  have hcomm : ∀ t ∈ fixSub x, t * k = k * t := by
    intro t ht
    have h1 : k * t * k⁻¹ = t := hfix t ht
    calc t * k = k * t * k⁻¹ * k := by rw [h1]
      _ = k * t := by group
  have hle : Subgroup.zpowers k ≤ fixSub x := (Subgroup.zpowers_le (H := fixSub x)).2 hk
  have hnorm : ∀ f ∈ fixSub x, ∀ n ∈ Subgroup.zpowers k, f * n * f⁻¹ ∈ Subgroup.zpowers k := by
    intro f hf n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute f k := hcomm f hf
    rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers k m
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers k)) := by
    rw [Nat.card_zpowers, ← orderOf_injective _ hinj k]
    exact hg
  have hbot := hN _ hle hnorm hcop
  have hk1 : k = 1 := by
    have h := Subgroup.mem_zpowers k
    rw [hbot, Subgroup.mem_bot] at h
    exact h
  rw [hk1, map_one]

theorem mem_innerAut_of_coprime_of_hom {M : Type*} [Group M] (Θ : MulAut K →* M)
    (hΘ : ∀ α : MulAut K, Θ α = 1 → α ∈ innerAut K) {n : ℕ} (hM : ∀ y : M, y ^ p ^ n = 1)
    {g : MulAut K} (hg : Nat.Coprime p (orderOf g)) : g ∈ innerAut K := by
  apply hΘ
  have h1 : orderOf (Θ g) ∣ orderOf g := orderOf_map_dvd Θ g
  have h2 : orderOf (Θ g) ∣ p ^ n := orderOf_dvd_of_pow_eq_one (hM _)
  exact orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left n hg)) h1)

theorem mem_innerAut_of_pow_eq_one_of_hom {M : Type*} [Group M] (Θ : MulAut K →* M)
    (hΘ : ∀ α : MulAut K, Θ α = 1 → α ∈ innerAut K) {m : ℕ} (hM : ∀ y : M, y ^ m = 1)
    (hpm : Nat.Coprime p m) {g : MulAut K} (hg : g ^ p = 1) : g ∈ innerAut K := by
  apply hΘ
  have h1 : orderOf (Θ g) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
  have h2 : orderOf (Θ g) ∣ m := orderOf_dvd_of_pow_eq_one (hM _)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hpm) h2)

theorem isLocallyBalancedAbs_one_of_good [Finite K] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (h : ∀ x : MulAut K, x ^ p = 1 → x ≠ 1 → FieldCoreAt p x ∨ CoreFreeAt p x) :
    IsLocallyBalancedAbs p 1 K := by
  intro D hD hcard H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime hp hcard
  rcases h d (hD.2 d hdD) hd1 with hfc | hcf
  · exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hdD hd1 hfc
  · exact localDeltaIn_eq_bot_of_coreFree hp hinj hH hdD hd1 hcf

theorem isLocallyBalancedAbs_one_of_hom_pGroup [Finite K] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {M : Type*} [Group M]
    (Θ : MulAut K →* M) (hΘ : ∀ α : MulAut K, Θ α = 1 → α ∈ innerAut K) {n : ℕ}
    (hM : ∀ y : M, y ^ p ^ n = 1)
    (h : ∀ x : MulAut K, x ^ p = 1 → x ≠ 1 → FieldCoreAt p x ∨ NoNormalPPrime p (fixSub x)) :
    IsLocallyBalancedAbs p 1 K :=
  isLocallyBalancedAbs_one_of_good hp hinj fun x hx hx1 =>
    (h x hx hx1).imp id fun hN =>
      coreFreeAt_of_coprime_inner hinj (fun _ hg => mem_innerAut_of_coprime_of_hom Θ hΘ hM hg) hN

theorem mem_normalizer_of_mem_fixSub {x : MulAut K} {N : Subgroup K}
    (hNn : ∀ f ∈ fixSub x, ∀ n ∈ N, f * n * f⁻¹ ∈ N) {y : K} (hy : y ∈ fixSub x) :
    y ∈ Subgroup.normalizer (N : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨hNn y hy n, fun h => ?_⟩
  have h1 := hNn y⁻¹ (inv_mem hy) _ h
  have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
  rwa [e] at h1

theorem center_eq_bot_of_involution {G : Type*} [Group G] [IsSimpleGroup G] {t : G}
    (ht : orderOf t = 2) (hG : Nat.card G ≠ 2) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    haveI hn : (Subgroup.zpowers t).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hc : g * n = n * g := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top n) g
      rw [hc, mul_inv_cancel_right]
      exact hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers t) with h' | h'
    · have h1 : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [h', Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · apply hG
      rw [← Subgroup.card_top (G := G), ← h', Nat.card_zpowers, ht]

end Generic

section Suzuki

theorem card_of_suzukiModel_two_five {S : Type} [Group S]
    (hM : CFSG.Blueprint.SuzukiModel S 2 5) : Nat.card S = 32537600 := by
  obtain ⟨-, a, -, F, _, _, hf, hF, ⟨e'⟩⟩ := hM
  have ha : a = 2 := by omega
  subst ha
  rw [Nat.card_congr e'.toEquiv, CFSG.LieType.Ree.suzuki_order hF]
  norm_num

theorem isLocallyBalancedAbs_five_one_of_suzukiModel
    (S : Type) [Group S]
    (hM : CFSG.Blueprint.SuzukiModel S 2 5) : IsLocallyBalancedAbs 5 1 S := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  haveI : Finite S := CFSG.LieType.Simplicity.fam_suzuki_finiteness S 2 5 hM
  haveI : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_2b2_simplicity S 2 5 hM).2
  have hcard : Nat.card S = 32537600 := card_of_suzukiModel_two_five hM
  have hZ : Subgroup.center S = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hcard]; norm_num)
    exact center_eq_bot_of_involution ht (by rw [hcard]; norm_num)
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hZ
  have hZc : Nat.Coprime 5 (Nat.card (Subgroup.center S)) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have h5 : 5 ∣ Nat.card S := by
    rw [hcard]
    norm_num
  have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 5 :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 5 hM).1.2.1
  refine isLocallyBalancedAbs_one_of_hom_pGroup (n := 1) hp hinj
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S))
    (fun α hα => (QuotientGroup.eq_one_iff α).1 hα)
    (fun y => by
      rw [pow_one]
      exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard y).trans hO))
    fun x hx hx1 => Or.inr ?_
  obtain ⟨y, hyfix, hy5, hy1⟩ : ∃ y ∈ fixSub x, y ^ 5 = 1 ∧ y ≠ 1 := by
    by_cases hin : x ∈ innerAut S
    · obtain ⟨k, rfl⟩ := hin
      refine ⟨k, ?_, ?_, ?_⟩
      · rw [mem_fixSub, MulAut.conj_apply]
        group
      · apply hinj
        rw [map_pow, hx, map_one]
      · rintro rfl
        exact hx1 (map_one _)
    · obtain ⟨y, hy5, hyx, hyn⟩ := rankAux_fix_outer hp hZc h5 x hx hin
      refine ⟨y, hyx, hy5, ?_⟩
      rintro rfl
      exact hyn (by rw [map_one]; exact one_mem _)
  intro N _ hNn hNc
  exact bal207SzNorm S hM y hy5 hy1 N hNc (mem_normalizer_of_mem_fixSub hNn hyfix)

theorem isLocallyBalancedAbs_five_one_sz32
    (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid) :
    IsLocallyBalancedAbs 5 1 (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group :=
  isLocallyBalancedAbs_five_one_of_suzukiModel _ (szAux_suzukiModel (MulEquiv.refl _))

end Suzuki

section F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem isLocallyBalancedAbs_three_one_adjointF4_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : IsLocallyBalancedAbs 3 1 ↥(adjointGroup Tag.F4 K) := by
  haveI : CharP K 2 := SmallQ3.charP_two_of_card_two hK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK]; norm_num)
  refine isLocallyBalancedAbs_one_of_inner_outer_at Nat.prime_three
    (SmallQ3.innerOneBalanceThree_F4_two hK) fun δ hδ hδo => absurd ?_ hδo
  refine mem_innerAut_of_pow_eq_one_of_hom Θ (fun α hα => ?_)
    (by decide : ∀ y : Multiplicative (ZMod (2 * 1)), y ^ 2 = 1) (by norm_num) hδ
  have h : α ∈ Θ.ker := hα
  rw [hΘker] at h
  exact h

theorem isLocallyBalancedAbs_three_one_F4_two {q : TauCeti.PrimePower} (hq : IsTwoPow q 1)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hKq : Nat.card (GaloisField 2 1) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq.1 (GaloisField 2 1) hKq
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact IsLocallyBalancedAbs.of_mulEquiv
    (eB.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
    (isLocallyBalancedAbs_three_one_adjointF4_two _ hK)

end F4Two

end CFSG.HardMathSupport.Dickson.Bal207
