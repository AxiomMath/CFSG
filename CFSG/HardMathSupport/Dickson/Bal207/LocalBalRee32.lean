module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.Bal207.ExcReeShape
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section Ree32


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem noNormalPPrime_centralizer_reeGamma_two_five (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    {y : ReeTag.F4.reeGamma K 2} (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) :
    NoNormalPPrime 5 (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 2))) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  have hEp : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hEel : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  obtain ⟨A, N, -, hAcard, -, hcomm, -, hsup, hNcard, ⟨eN⟩, -⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_centralizer_decomp hK P _ hEP hEel y
      (Subgroup.mem_zpowers y) hy1
  have hNC : N ≤ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 2)) := by
    rw [← hsup]
    exact le_sup_right
  obtain ⟨hsimp, hnc⟩ := excRee_suzuki_simple hK
  haveI : IsSimpleGroup ↥N := eN.isSimpleGroup
  have hncN : ∃ a b : ↥N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eN.symm a, eN.symm b, fun h => hab (by simpa using congrArg eN h)⟩
  have hZN : Subgroup.center ↥N = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncN
  intro R hRC hRn hRc
  have hRN : R ⊓ N = ⊥ := by
    have hN : ((R ⊓ N).subgroupOf N).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : ReeTag.F4.reeGamma K 2) ∈ R ⊓ N := Subgroup.mem_subgroupOf.1 hn
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
        ⟨hRn g (hNC g.2) n (Subgroup.mem_inf.1 hn').1, (g * n * g⁻¹).2⟩)
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ N).subgroupOf N) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : ↥N) ∈ (R ⊓ N).subgroupOf N :=
        Subgroup.mem_subgroupOf.2 hx
      rw [h] at hxN
      exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hxN))
    · exfalso
      have hNR : N ≤ R := fun s hs => by
        have hmem : (⟨s, hs⟩ : ↥N) ∈ (R ⊓ N).subgroupOf N := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
      have h5N : 5 ∣ Nat.card N := by
        rw [hNcard]
        norm_num
      exact absurd (Nat.Coprime.eq_one_of_dvd hRc (h5N.trans (Subgroup.card_dvd_of_le hNR)))
        (by norm_num)
  have hRcent : ∀ r ∈ R, ∀ s ∈ N, r * s = s * r := by
    intro r hr s hs
    have hrAN : r ∈ A ⊔ N := by
      rw [hsup]
      exact hRC hr
    obtain ⟨a, ha, s₀, hs₀, hr'⟩ :=
      CFSG.HardMathSupport.Malle.LocalAction.mem_sup_of_commute hcomm hrAN
    have hs₁ : s₀ * s * s₀⁻¹ ∈ N := N.mul_mem (N.mul_mem hs₀ hs) (N.inv_mem hs₀)
    have h1 : r * s * r⁻¹ ∈ N := by
      rw [← hr']
      have hc1 : a * (s₀ * s * s₀⁻¹) = (s₀ * s * s₀⁻¹) * a := hcomm a ha _ hs₁
      have e : a * s₀ * s * (a * s₀)⁻¹ = s₀ * s * s₀⁻¹ := by
        calc a * s₀ * s * (a * s₀)⁻¹ = a * (s₀ * s * s₀⁻¹) * a⁻¹ := by group
          _ = (s₀ * s * s₀⁻¹) * a * a⁻¹ := by rw [hc1]
          _ = s₀ * s * s₀⁻¹ := by group
      rw [e]
      exact hs₁
    have h2 : r * s * r⁻¹ * s⁻¹ ∈ R ⊓ N := by
      refine Subgroup.mem_inf.2 ⟨?_, N.mul_mem h1 (N.inv_mem hs)⟩
      have h3 : s * r⁻¹ * s⁻¹ ∈ R := hRn s (hNC hs) r⁻¹ (R.inv_mem hr)
      have e : r * s * r⁻¹ * s⁻¹ = r * (s * r⁻¹ * s⁻¹) := by group
      rw [e]
      exact R.mul_mem hr h3
    rw [hRN] at h2
    have h4 : r * s * r⁻¹ * s⁻¹ = 1 := Subgroup.mem_bot.1 h2
    calc r * s = (r * s * r⁻¹ * s⁻¹) * (s * r) := by group
      _ = s * r := by rw [h4, one_mul]
  refine eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 ?_
  have hrAN : r ∈ A ⊔ N := by
    rw [hsup]
    exact hRC hr
  obtain ⟨a, ha, s₀, hs₀, rfl⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.mem_sup_of_commute hcomm hrAN
  have hs₀Z : (⟨s₀, hs₀⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show (t : ReeTag.F4.reeGamma K 2) * s₀ = s₀ * t
    have h1 := hRcent (a * s₀) hr t t.2
    have h2 := hcomm a ha t t.2
    have h3 : a * (s₀ * t) = a * (t * s₀) := by
      calc a * (s₀ * t) = a * s₀ * t := by group
        _ = t * (a * s₀) := h1
        _ = (t * a) * s₀ := by group
        _ = (a * t) * s₀ := by rw [h2]
        _ = a * (t * s₀) := by group
    exact (mul_left_cancel h3).symm
  rw [hZN] at hs₀Z
  have hs₀1 : s₀ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hs₀Z)
  subst hs₀1
  rw [mul_one] at hr ⊢
  have ha25 : orderOf a ∣ 5 ^ 2 := by
    have h := Subgroup.orderOf_dvd_natCard A ha
    rwa [hAcard] at h
  have hco : Nat.Coprime (orderOf a) 5 :=
    (hRc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R hr)).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco) ha25)


theorem isLocallyBalancedAbs_five_one_reeGamma_two (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    IsLocallyBalancedAbs 5 1 (ReeTag.F4.reeGamma K 2) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (ReeTag.large_Ree_fixed_group_center_trivial 2 K hK)
  obtain ⟨-, -, -, -, hOut, -⟩ := large_Ree_full_inner_field_automorphism_normal_form 2
    (by norm_num) K hK
  refine isLocallyBalancedAbs_one_of_hom_pGroup (n := 1) Nat.prime_five hinj
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _))
    (fun α hα => (QuotientGroup.eq_one_iff α).1 hα) (fun y => ?_) (fun x hx hx1 => ?_)
  · have h := pow_card_eq_one' (x := y)
    rw [hOut] at h
    rw [pow_one]
    exact h
  · by_cases hin : x ∈ innerAut (ReeTag.F4.reeGamma K 2)
    · obtain ⟨y, rfl⟩ := hin
      right
      have hfix : fixSub (MulAut.conj y) =
          Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 2)) := by
        ext g
        rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
        constructor
        · intro h
          calc g * y = (y * g * y⁻¹) * y := by rw [h]
            _ = y * g := by group
        · intro h
          calc y * g * y⁻¹ = (g * y) * y⁻¹ := by rw [h]
            _ = g := by group
      rw [hfix]
      exact noNormalPPrime_centralizer_reeGamma_two_five hK
        (hinj (by rw [map_pow, hx, map_one])) (fun h => hx1 (by rw [h, map_one]))
    · left
      exact fieldCoreAt_reeGamma (by norm_num) hK Nat.prime_five (by norm_num) (by norm_num) x hx
        hin

omit [Field K] [Finite K] [CharP K ReeTag.F4.prime] in
theorem isLocallyBalancedAbs_five_one_ree32
    (hv : (TauCeti.LieTypeIndex.reeF4 2).Valid) :
    IsLocallyBalancedAbs 5 1 (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group := by
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 2 hv
    (MulEquiv.refl _)
  obtain ⟨-, a, -, hfa, K', _, _, _, hK', ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have ha2 : a = 2 := by omega
  subst ha2
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_five_one_reeGamma_two hK')

omit [Field K] [Finite K] [CharP K ReeTag.F4.prime] in
theorem bal207LocalBalRow_ree32 :
    Bal207LocalBalRow fun p d => p = 5 ∧ IsExcRee32 d := by
  rintro p ⟨d, hv⟩ ⟨rfl, hd⟩
  cases d with
  | reeF4 m =>
    change m = 2 at hd
    subst hd
    exact isLocallyBalancedAbs_five_one_ree32 hv
  | _ => exact False.elim hd

end Ree32

end CFSG.HardMathSupport.Dickson.Bal207

end
