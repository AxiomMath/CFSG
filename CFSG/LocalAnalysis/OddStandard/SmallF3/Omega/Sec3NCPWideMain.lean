module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3NCPWideBad
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3NCPBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutWW2

public section

namespace CFSG.OddStandard.SmallF3.Omega.NCPWide

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.Omega CFSG.LocalAnalysis.ComponentInitial
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.ThmU

variable {G : Type} [Group G]

@[expose] def StarUnp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ J : Subgroup G, Unp J → ComponentAtCentralInvolutions J →
      ∀ g : G, ⁅J, CFSG.conjugate J g⁆ = ⊥ → CFSG.conjugate J g = J

theorem starUnp_holds :
    StarUnp := by
  intro G _ _ t L hS J hJ huniv g hcomm
  exfalso
  haveI : IsSimpleGroup G := hS.simple
  obtain ⟨hJC, hJF, hF, hL⟩ := hJ
  obtain ⟨x₀, hx₀, hJx₀⟩ := hJC.1
  have hJq : CFSG.Assembly.IsComponentOf J (centralizer ({x₀} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hJx₀.1).2 hJx₀.2
  have hx₀J : x₀ ∈ centralizer (J : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hJx₀.le ha)
  have hU : IsUniversalComponent J := fun u hu hu2 =>
    (isComponentOf_iff_isComponent_subgroupOf (huniv u hu2 hu).1).2 (huniv u hu2 hu).2
  have hCeven : Even (Nat.card (centralizer (J : Set G))) := by
    have h1 : orderOf (⟨x₀, hx₀J⟩ : ↥(centralizer (J : Set G))) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hx₀
    have h2 := orderOf_dvd_natCard (⟨x₀, hx₀J⟩ : ↥(centralizer (J : Set G)))
    rw [h1] at h2
    exact even_iff_two_dvd.2 h2
  exact universal_rank_two_component_commutator_ne_bot (sec4_nonabelian hS.toSec3Setting)
    hJq.2.2 (aor_two_le_pRank_of_nonPocketed hJF hF hL) hCeven hU g⁻¹ hcomm

theorem ncpw_not_universal [Finite G] (hstar : StarUnp) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A K : Subgroup G} {x y : G} (hc : SwapCfg A x y K)
    (hK : Unp K) : ¬ ComponentAtCentralInvolutions K := by
  intro hu
  have hcomm : ⁅K, CFSG.conjugate K x⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    have hw' : w ∈ cj x K := by rwa [cj_eq_conjugate_of_sq hc.x_sq]
    exact (hc.diagComm a ha w hw').symm
  exact hc.ne (hstar G t L hS K hK hu x hcomm)

theorem ncpw_exists_swap_rank_three [Finite G] {B M : Subgroup G} {x y : G}
    (hS : SwapCfg B x y M)
    (hMrank : 2 ≤ CFSG.Open.pRank 2 M) (hy : y ∉ cj x M) :
    ∃ w₁ w₂ : G, w₁ ∈ cj x M ∧ w₂ ∈ cj x M ∧ orderOf w₁ = 2 ∧ orderOf w₂ = 2 ∧
      w₁ * w₂ = w₂ * w₁ ∧ w₁ ≠ w₂ ∧
      ∃ P : Subgroup G, y ∈ P ∧ w₁ ∈ P ∧ w₂ ∈ P ∧ Nat.card P = 8 ∧
        (∀ p ∈ P, ∀ q ∈ P, p * q = q * p) ∧ (∀ p ∈ P, p * p = 1) ∧
        (∀ p ∈ P, ∀ m ∈ M, p * m = m * p) ∧
        3 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G)) := by
  obtain ⟨v₁, v₂, hv₁, hv₂, ho₁, ho₂, hc, hne⟩ := exists_fourGroup_of_two_le_pRank hMrank
  have hw₁c : x * v₁ * x⁻¹ ∈ cj x M := conj_mem_cj hv₁
  have hw₂c : x * v₂ * x⁻¹ ∈ cj x M := conj_mem_cj hv₂
  have ho₁' : orderOf (x * v₁ * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho₁]
  have ho₂' : orderOf (x * v₂ * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho₂]
  have hw₁₂ : (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) = (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) := by
    rw [show (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) = x * (v₁ * v₂) * x⁻¹ by group,
      show (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) = x * (v₂ * v₁) * x⁻¹ by group, hc]
  have hwne : x * v₁ * x⁻¹ ≠ x * v₂ * x⁻¹ := by
    intro h
    exact hne ((MulAut.conj x).injective (by simpa [MulAut.conj_apply] using h))
  have hyw₁ : y * (x * v₁ * x⁻¹) = (x * v₁ * x⁻¹) * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hS.isComp_cj.1 hw₁c)).symm
  have hyw₂ : y * (x * v₂ * x⁻¹) = (x * v₂ * x⁻¹) * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hS.isComp_cj.1 hw₂c)).symm
  have hyw₁ne : y ≠ x * v₁ * x⁻¹ := fun h => hy (h.symm ▸ hw₁c)
  have hyw₂ne : y ≠ x * v₂ * x⁻¹ := fun h => hy (h.symm ▸ hw₂c)
  have hywne : y ≠ (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) :=
    fun h => hy (h.symm ▸ (cj x M).mul_mem hw₁c hw₂c)
  obtain ⟨P, hyP, hw₁P, hw₂P, hPcard, hPcomm, hPsq, hPle⟩ :=
    exists_elemAbelian_eight hS.y_ord ho₁' ho₂' hw₁₂ hwne hyw₁ hyw₂ hyw₁ne hyw₂ne hywne
  have hyM : y ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.1 (hS.comp.1 hm)
  have hw₁M : x * v₁ * x⁻¹ ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm => hS.diagComm m hm _ hw₁c
  have hw₂M : x * v₂ * x⁻¹ ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm => hS.diagComm m hm _ hw₂c
  have hPcentM : ∀ p ∈ P, ∀ m ∈ M, p * m = m * p :=
    fun p hp m hm =>
      (Subgroup.mem_centralizer_iff.1 (hPle (centralizer (M : Set G)) hyM hw₁M hw₂M hp) m hm).symm
  have hrank : 3 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G)) :=
    three_le_pRank_of_involutions hS.y_ord ho₁' ho₂' hw₁₂ hwne hyw₁ hyw₂ hyw₁ne hyw₂ne hywne
      hyM hw₁M hw₂M
  exact ⟨x * v₁ * x⁻¹, x * v₂ * x⁻¹, hw₁c, hw₂c, ho₁', ho₂', hw₁₂, hwne,
    P, hyP, hw₁P, hw₂P, hPcard, hPcomm, hPsq, hPcentM, hrank⟩

theorem ncpw_step_four [Finite G] (hstar : StarUnp) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {K : Subgroup G} (hK : Unp K)
    {a b : G} (ha : GoodI K a) (hb : BadI K b) (hab : a * b = b * a) {P : Subgroup G}
    (haP : a ∈ P) (hbP : b ∈ P) (hcard : Nat.card P = 8)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1)
    (hPK : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) : False := by
  obtain ⟨M, hSM, hMu⟩ := exists_swapCfg hS hK ha hb hab
  have hMrank : 2 ≤ CFSG.Open.pRank 2 M :=
    aor_two_le_pRank_of_nonPocketed hMu.2.1 hMu.2.2.1 hMu.2.2.2
  have hPb : P ≤ centralizer ({b} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm p hp b hbP
  obtain ⟨hR, hRbad⟩ :=
    ncpw_swap_package hS hK ha hSM hMu hPb hPK (fun p hp => hcomm p hp a haP) haP
  obtain ⟨r₁, r₂, hr₁, hr₂, ho₁, ho₂, ho₃, h12⟩ :=
    exists_fourGroup_of_relIndex_two hcard hcomm hsq inf_le_left hR
  have hr₃ : r₁ * r₂ ∈ P ⊓ normalizer (M : Set G) := Subgroup.mul_mem _ hr₁ hr₂
  have hg₁ : GoodI M r₁ := ⟨ho₁, (hRbad r₁ hr₁ ho₁).2.1⟩
  have hg₂ : GoodI M r₂ := ⟨ho₂, (hRbad r₂ hr₂ ho₂).2.1⟩
  have hg₃ : GoodI M (r₁ * r₂) := ⟨ho₃, (hRbad (r₁ * r₂) hr₃ ho₃).2.1⟩
  have hbM : b ∉ M := fun hbM =>
    not_mem_of_unp hMu hb.1 (le_cent_iff.1 hSM.comp.1) hbM
  have hbn : b ∉ cj a M := by
    intro h
    apply hbM
    have h2 : a * b * a = b := by
      rw [hab, mul_assoc, mul_self_eq_one_of_orderOf ha.1, mul_one]
    rw [mem_cj_of_mul_self (mul_self_eq_one_of_orderOf ha.1), h2] at h
    exact h
  obtain ⟨w₁, w₂, _, _, _, _, _, _, Q, _, _, _, _, _, _, _, hQrank⟩ :=
    ncpw_exists_swap_rank_three hSM hMrank hbn
  exact ncpw_not_universal hstar hS hSM hMu
    (componentAt_of_fourGroup hS hMu hg₁ hg₂ hg₃ h12 hQrank)

theorem isComponentIn_of_commute [Finite G] (hstar : StarUnp) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A : Subgroup G} (hA : Unp A) {x₀ x : G} (hx₀ : GoodI A x₀)
    (hx : orderOf x = 2) (hcomm : x₀ * x = x * x₀) (hxA : x ∈ centralizer (A : Set G)) :
    IsComponentIn A (centralizer ({x} : Set G)) := by
  by_contra hnc
  have hxbad : BadI A x := ⟨hx, hxA, hnc⟩
  obtain ⟨K, hSK, hKu⟩ := exists_swapCfg hS hA hx₀ hxbad hcomm
  have hKrank : 2 ≤ CFSG.Open.pRank 2 K :=
    aor_two_le_pRank_of_nonPocketed hKu.2.1 hKu.2.2.1 hKu.2.2.2
  have hKnu : ¬ ComponentAtCentralInvolutions K := ncpw_not_universal hstar hS hSK hKu
  have haGood : GoodI K x := ⟨hSK.y_ord, hSK.comp⟩
  have haK : x ∉ K := fun hmem =>
    not_mem_of_unp hKu hx (le_cent_iff.1 hSK.comp.1) hmem
  have haKt : x ∉ cj x₀ K := by
    intro haKt
    apply haK
    have hmem : x₀ * x * x₀ ∈ K := (mem_cj_of_mul_self hSK.x_sq).1 haKt
    have htat : x₀ * x * x₀ = x := by
      calc x₀ * x * x₀ = (x * x₀) * x₀ := by rw [hcomm]
        _ = x := by rw [mul_assoc, hSK.x_sq, mul_one]
    rwa [htat] at hmem
  obtain ⟨w₁, w₂, hw₁, hw₂, ho₁, ho₂, hc12, hne, P, haP, hw₁P, hw₂P, hcard, hcomm', hsq,
    hPK, h3⟩ := ncpw_exists_swap_rank_three hSK hKrank haKt
  have hw₁w₂_mem : w₁ * w₂ ∈ cj x₀ K := (cj x₀ K).mul_mem hw₁ hw₂
  have hw₁w₂P : w₁ * w₂ ∈ P := P.mul_mem hw₁P hw₂P
  have hw₁sq : w₁ * w₁ = 1 := mul_self_eq_one_of_orderOf ho₁
  have hw₂sq : w₂ * w₂ = 1 := mul_self_eq_one_of_orderOf ho₂
  have hw₁w₂_ne : w₁ * w₂ ≠ 1 := by
    intro h
    apply hne
    calc w₁ = w₁ * 1 := (mul_one w₁).symm
      _ = w₁ * (w₂ * w₂) := by rw [hw₂sq]
      _ = (w₁ * w₂) * w₂ := by group
      _ = w₂ := by rw [h, one_mul]
  have hw₁w₂_sq : (w₁ * w₂) * (w₁ * w₂) = 1 := by
    calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * (w₁ * w₂)) := by group
      _ = w₁ * ((w₂ * w₁) * w₂) := by group
      _ = w₁ * ((w₁ * w₂) * w₂) := by rw [hc12]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁sq, hw₂sq, mul_one]
  have ho₁₂ : orderOf (w₁ * w₂) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hw₁w₂_sq) hw₁w₂_ne
  have hKle₁ : K ≤ centralizer ({w₁} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSK.diagComm k hk w₁ hw₁
  have hKle₂ : K ≤ centralizer ({w₂} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSK.diagComm k hk w₂ hw₂
  have hKle₁₂ : K ≤ centralizer ({w₁ * w₂} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSK.diagComm k hk (w₁ * w₂) hw₁w₂_mem
  have bad_of_not_good : ∀ w : G, orderOf w = 2 → K ≤ centralizer ({w} : Set G) →
      ¬ GoodI K w → BadI K w := by
    intro w hw hle hng
    by_contra hnb
    exact hng (goodI_of_not_badI hw (le_cent_iff.1 hle) hnb)
  by_cases hgood : GoodI K w₁ ∧ GoodI K w₂ ∧ GoodI K (w₁ * w₂)
  · exact hKnu (componentAt_of_fourGroup hS hKu hgood.1 hgood.2.1 hgood.2.2 hc12 h3)
  · have hcases : ¬ GoodI K w₁ ∨ ¬ GoodI K w₂ ∨ ¬ GoodI K (w₁ * w₂) := by
      by_contra hc
      push Not at hc
      exact hgood hc
    rcases hcases with h₁ | h₂ | h₃
    · exact ncpw_step_four hstar hS hKu haGood
        (bad_of_not_good w₁ ho₁ hKle₁ h₁) (hcomm' x haP w₁ hw₁P) haP hw₁P hcard hcomm' hsq hPK
    · exact ncpw_step_four hstar hS hKu haGood
        (bad_of_not_good w₂ ho₂ hKle₂ h₂) (hcomm' x haP w₂ hw₂P) haP hw₂P hcard hcomm' hsq hPK
    · exact ncpw_step_four hstar hS hKu haGood
        (bad_of_not_good (w₁ * w₂) ho₁₂ hKle₁₂ h₃) (hcomm' x haP (w₁ * w₂) hw₁w₂P)
        haP hw₁w₂P hcard hcomm' hsq hPK

theorem asc82Walter12L2_of_star (hstar : StarUnp) : Asc82Walter12L2 := by
  intro G _ _ t L hS X hXC hXF hF hL
  exact aor_componentAt_of_commute_case hXC.1 fun {x₀ x} hx₀ hx hcomm hXx₀ hxX =>
    isComponentIn_of_commute hstar hS ⟨hXC, hXF, hF, hL⟩ ⟨hx₀, hXx₀⟩ hx hcomm hxX

end CFSG.OddStandard.SmallF3.Omega.NCPWide

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Walter12L2_holds :
    Asc82Walter12L2 :=
  NCPWide.asc82Walter12L2_of_star NCPWide.starUnp_holds

theorem asc82NonCommuteNonPocketed_holds :
    Asc82NonCommuteNonPocketed :=
  asc82NonCommuteNonPocketed_of_walter12L2 asc82Walter12L2_holds

end CFSG.OddStandard.SmallF3.Omega
