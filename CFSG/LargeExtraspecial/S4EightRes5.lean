module

public import CFSG.LargeExtraspecial.S4EightRes4
public import CFSG.LargeExtraspecial.S4EightOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem FhatV_le_RmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) (F : Subgroup S.O) :
    FhatV S haQ t F ≤ RmodN S g t := by
  rintro _ ⟨r, -, rfl⟩
  exact ⟨r, r.2, fun v => coe_resV_apply haQ r v⟩

section Glue

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {F : Subgroup S.O}
  (hFodd : Odd (Nat.card F)) (hFR : F ≤ Rbar S g t) (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
  (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1)
include H ht hFodd hFR hLF hCF

theorem eq_one_of_mem_FhatV {p : Vt S g t ≃ₗ[ZMod 2] Vt S g t}
    (hp : p ∈ FhatV S H.conj_mem t F) (hpa : p (aV ht) = aV ht) : p = 1 := by
  obtain ⟨r, hr, rfl⟩ := hp
  have hrF : (r : S.O) ∈ F := mem_subgroupOf.mp hr
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    have := congrArg Subtype.val hpa
    rwa [coe_resV_apply] at this
  have h1 := eq_one_of_mem_of_apply_eq H hFodd hFR hLF hCF hrF hfix
  have : r = 1 := Subtype.ext h1
  rw [this, map_one]

omit hLF in
theorem eq_one_of_resV_eq_one (hLF : S.Lbar g ≤ normalizer (F : Set S.O)) {r : Rbar S g t}
    (hrF : (r : S.O) ∈ F) (hr : resV H.conj_mem t r = 1) : r = 1 := by
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    have := congrArg (fun x : Vt S g t ≃ₗ[ZMod 2] Vt S g t => ((x (aV ht) : Vt S g t) : S.Qt)) hr
    simp only [coe_resV_apply] at this
    exact this
  exact Subtype.ext (eq_one_of_mem_of_apply_eq H hFodd hFR hLF hCF hrF hfix)

theorem card_FhatV : Nat.card (FhatV S H.conj_mem t F) = Nat.card F := by
  have hinj : Function.Injective
      ((resV H.conj_mem t).comp (F.subgroupOf (Rbar S g t)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have h1 := eq_one_of_resV_eq_one H ht hFodd hFR hCF hLF (mem_subgroupOf.mp r.2) hr
    have : r = 1 := Subtype.ext h1
    rw [this]
    exact one_mem _
  have h1 : FhatV S H.conj_mem t F =
      ((resV H.conj_mem t).comp (F.subgroupOf (Rbar S g t)).subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv

end Glue

theorem timmesfeld_4_8_F (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) {F : Subgroup S.O}
    (hFodd : Odd (Nat.card F)) (hF1 : F ≠ ⊥) (hFR : F ≤ Rbar S g t)
    (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
    (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1) :
    Nat.card F = 3 ∨ ∃ hVQ : ¬ V S g t ≤ S.Qa g, finrank (ZMod 2) (Vt S g t) = 4 ∧
      OmegaCase H C ht ht1 hVQ ∧ Nat.card F = 9 ∧
      ∃ f, ∃ hf : f ∈ F, orbV H.conj_mem ht (hFR hf) ∉ (ZMod 2) ∙ aV ht ∧
        beta H C ht ht1 hVQ (aV ht) (orbV H.conj_mem ht (hFR hf)) = 0 := by
  rcases timmesfeld_4_8_odd H hNo C ht ht1 hR hFodd hF1 hFR hLF hCF with h3 | ⟨hVQ, h4, hcase, -⟩
  · exact Or.inl h3
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  set P := FhatV S H.conj_mem t F with hPdef
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  have ha := aV_ne_zero H ht
  have hEU := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hidx := card_spPointRadical_le_two_mul H C ht ht1 hVQ
  have hPR : P ≤ RmodN S g t := FhatV_le_RmodN H.conj_mem t F
  have hPI : P ≤ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) :=
    hPR.trans (RmodN_le_isometryGroup H C ht ht1 hVQ)
  have hEP := LmodN_le_normalizer_FhatV H.conj_mem ht (F := F) hLF
  have hreg : ∀ p ∈ P, p (aV ht) = aV ht → p = 1 := fun p hp hpa =>
    eq_one_of_mem_FhatV H ht hFodd hFR hLF hCF hp hpa
  have hcard : Nat.card P = Nat.card F := card_FhatV H ht hFodd hFR hLF hCF
  have hPodd : Odd (Nat.card P) := hcard ▸ hFodd
  have hF1' : Nat.card F ≠ 1 := fun h => hF1 (Subgroup.card_eq_one.mp h)
  rcases hcase with hA | hΩ | hPG
  ·
    have hbot := eq_bot_of_no_typeA hβ hnd h4 ha hEU hidx hA.tau_not_mem hPI hEP hreg
      hA.no_typeA
    rw [← hcard, hbot, card_bot] at hF1'
    exact absurd rfl hF1'
  ·
    have hτ := (radConfig H C ht ht1 hVQ hNo hΩ.not_transitive).tau_not_mem
    rcases card_odd_of_four hβ hnd h4 ha hEU hidx hτ hPI hEP hreg hPodd with
      h1 | h3 | ⟨h9, p, hp, hpn, hpβ⟩
    · exact absurd (hcard ▸ h1) hF1'
    · exact Or.inl (hcard ▸ h3)
    · right
      obtain ⟨r, hr, rfl⟩ := hp
      have hrF : (r : S.O) ∈ F := mem_subgroupOf.mp hr
      refine ⟨hVQ, h4, hΩ, hcard ▸ h9, r, hrF, ?_, ?_⟩
      · exact hpn
      · exact hpβ
  ·
    have hτ := hPG.tau_not_mem
    obtain ⟨d₁, hd₁, hd₁n, he₁⟩ := hPG.exists_typeA
    rcases card_odd_of_four hβ hnd h4 ha hEU hidx hτ hPI hEP hreg hPodd with
      h1 | h3 | ⟨h9, -⟩
    · exact absurd (hcard ▸ h1) hF1'
    · exact Or.inl (hcard ▸ h3)
    · exfalso
      have hV : Nat.card (Vt S g t) = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h4, Nat.card_zmod]
        norm_num
      refine false_of_card_eq_nine hV h9 ha fun p hp v hv hpv => ?_
      obtain ⟨x, hxR, hxa⟩ := hPG.transitive v hv
      have hpR := hPR hp
      set q := x⁻¹ * p * x with hq
      have hqR : q ∈ RmodN S g t := mul_mem (mul_mem (inv_mem hxR) hpR) hxR
      have hqa : q (aV ht) = aV ht := by
        rw [hq, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxa, hpv, ← hxa]
        exact x.symm_apply_apply _
      have hq9 : q ^ 9 = 1 := by
        have hp9 : p ^ 9 = 1 := by
          have := pow_card_eq_one' (G := P) (x := ⟨p, hp⟩)
          rw [h9] at this
          exact congrArg Subtype.val this
        rw [hq, show x⁻¹ * p * x = x⁻¹ * p * x⁻¹⁻¹ by rw [inv_inv], conj_pow, hp9]
        group
      have hq1 := eq_one_of_odd_of_apply_eq hβ hnd h4 ha hEU hidx hτ hd₁ hd₁n he₁
        (RmodN_le_isometryGroup H C ht ht1 hVQ hqR) hqa (mem_normalizer_LmodN H ht hqR hqa)
        (by decide : Odd 9) hq9
      rw [hq] at hq1
      calc p = x * (x⁻¹ * p * x) * x⁻¹ := by group
        _ = 1 := by rw [hq1]; group

end CFSG.LargeExtraspecial.S4
