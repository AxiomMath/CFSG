module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallBase
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeakB4
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallBar
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallLift

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

@[expose] def HallWeakFor (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Subgroup G) (c : G) (m : ℕ), 3 ≤ m → orderOf c = 2 ^ m → c ∈ D →
    Nat.card D = 2 * orderOf c → (∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) →
    (∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) →
    HallWeakConclusion D

@[expose] def HallQ8Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → HallWeakFor G') →
    ∀ (D : Subgroup G) (c : G) (m : ℕ), 3 ≤ m → orderOf c = 2 ^ m → c ∈ D →
      Nat.card D = 2 * orderOf c → (∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) →
      (∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
        ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) →
      (∀ g : G, g * cz c = cz c * g) →
      (∃ x ∈ normalizer (D : Set G), x ∉ D ∧ ∃ d ∈ D, d * d = cz c ∧ ∃ g : G, g⁻¹ * x * g = d) →
      HallWeakConclusion D

theorem hallWeakFor_of_residual
    (hres : HallQ8Residual) :
    ∀ (N : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = N → HallWeakFor G := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro G _ _ hN D c m hm hco hcD hcard hD hcl
  have IH' : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → HallWeakFor G' :=
    fun G' _ _ h => IH _ (hN ▸ h) G' rfl
  have hk : 4 ∣ orderOf c := by
    rw [hco, show m = (m - 2) + 2 by omega, pow_add]
    exact Dvd.intro_left _ rfl
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := m + 1) (by rw [hcard, hco, pow_succ'])
  by_cases hH : centralizer ({cz c} : Set G) = ⊤
  ·
    have hzc : ∀ g : G, g * cz c = cz c * g := fun g =>
      mem_centralizer_singleton_iff.mp (hH ▸ mem_top g)
    have : (zpowers (cz c)).Normal := zpowers_cz_normal hzc
    have hQ : Nat.card (G ⧸ zpowers (cz c)) < Nat.card G := by
      have h := card_eq_card_quotient_mul_card_subgroup (zpowers (cz c))
      rw [card_zpowers_cz hk] at h
      have : 0 < Nat.card (G ⧸ zpowers (cz c)) := Nat.card_pos
      omega
    have hcD' : QuotientGroup.mk' (zpowers (cz c)) c ∈ D.map (QuotientGroup.mk' _) :=
      ⟨c, hcD, rfl⟩
    have hco' := orderOf_mk_c (c := c) hk
    by_cases hsic : ∀ x ∈ normalizer ((D.map (QuotientGroup.mk' (zpowers (cz c))) : Subgroup _) :
        Set (G ⧸ zpowers (cz c))), x ∉ D.map (QuotientGroup.mk' (zpowers (cz c))) →
      orderOf x = 2 → ∀ d ∈ D.map (QuotientGroup.mk' (zpowers (cz c))), orderOf d = 2 →
        ∀ g : G ⧸ zpowers (cz c), g⁻¹ * x * g ≠ d
    · refine weak_of_quotient (card_zpowers_cz hk) (zpowers_le.mpr (cz_mem hcD)) ?_
      rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
      · exact weak_d8 hcD' (by rw [hco', hco]; rfl) (card_map_D hk hcard hcD) (data_map hD) hsic
      · refine IH' _ hQ _ _ (m - 1) (by omega) ?_ hcD' (card_map_D hk hcard hcD) (data_map hD)
          hsic
        rw [hco', hco, show m = (m - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
        congr 1
    · exact hres G IH' D c m hm hco hcD hcard hD hcl hzc
        (exists_bad_of_not_sic hD hk hcD hcl hsic)
  ·
    set H := centralizer ({cz c} : Set G) with hHdef
    have hHlt : Nat.card H < Nat.card G := by
      have h1 := card_le_card_group H
      have h2 : Nat.card H ≠ Nat.card G := fun h => hH (card_eq_iff_eq_top H |>.mp h)
      omega
    have hDH : D ≤ H := fun d hd => mem_centralizer_singleton_iff.mpr (comm_cz hD hk hd)
    have hco' : orderOf (⟨c, hDH hcD⟩ : H) = 2 ^ m := by rw [Subgroup.orderOf_mk, hco]
    refine weak_of_subgroup hD hk hcl hcard hcD hD2 le_rfl
      (IH' H hHlt (D.subgroupOf H) ⟨c, hDH hcD⟩ m hm hco' (mem_subgroupOf.mpr hcD) ?_
        (data_subgroupOf hD hDH hcD) (sic_subgroupOf hcl hDH))
    rw [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv, hcard, Subgroup.orderOf_mk]

theorem hallWeak_of_residual
    (hres : HallQ8Residual) (G : Type) [Group G] [Finite G] (D : Subgroup G)
    (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h16 : 16 ≤ Nat.card D)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) :
    HallWeakConclusion D := by
  obtain ⟨n, -, ⟨e⟩⟩ := hD
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  obtain ⟨c, hcD, hco, hcard, hDc⟩ := data_of_mulEquiv e
  have hm : 3 ≤ n - 1 := by
    by_contra h
    have : 2 ^ (n - 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hallWeakFor_of_residual hres _ G rfl D c (n - 1) hm hco hcD (by rw [hco]; exact hcard)
    hDc hcl

theorem goldschmidtCorB4_of_residual
    (hres : HallQ8Residual) : GoldschmidtCorB4 :=
  goldschmidtCorB4_of_weak (hallWeak_of_residual hres)

end CFSG.ComponentClassification.Foote5.HallGen
