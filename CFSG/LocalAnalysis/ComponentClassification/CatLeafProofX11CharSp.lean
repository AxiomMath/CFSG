module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4Sq
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10SpTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf

public section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.GSThmB.X10Sp4

variable {F : Type} [Field F]

theorem eq_two_of_fixed_psp4_three [Finite F] {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 3 ^ f)
    {α : MulAut (StatedProj (StatedSp 2 F))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {M : Subgroup (StatedProj (StatedSp 2 F))} (hMX : M ≤ fixOf α)
    (hM : IsPComponent 2 (M.subgroupOf (fixOf α)))
    (hMm : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSp 2 3 1) : f = 2 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf1 : 1 ≤ f := by omega
  have hodd : Odd (Nat.card F) := odd_card_of_card_eq hp hp2 hF
  have h2 := two_ne_zero_of_odd_card hodd
  have h9 : 9 ≤ 3 ^ f := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h5 : 5 ≤ 3 ^ f := by omega
  have hZ := two_mul_card_of_lieModel_psp hp2 hMm
  have hcM : pPrimeCore 2 ↥M = ⊥ →
      Nat.card M * 2 = (3 ^ 1) ^ 4 * (((3 ^ 1) ^ 2 - 1) * ((3 ^ 1) ^ 4 - 1)) := by
    intro hO
    rw [← hZ, (pPrimeCore 2 ↥M).card_eq_card_quotient_mul_card_subgroup, hO, Subgroup.card_bot,
      mul_one]
  have hOs : IsSimpleGroup ↥M → pPrimeCore 2 ↥M = ⊥ := by
    intro hs
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥M)).resolve_right fun h => ?_
    have h1 : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      rw [h]
      have : Subsingleton (↥M ⧸ (⊤ : Subgroup ↥M)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_of_subsingleton (1 : ↥M ⧸ (⊤ : Subgroup ↥M))
    rw [h1, one_mul] at hZ
    norm_num at hZ
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hF) le_rfl).2.2 α hα2 hα1
  rw [hα] at hMX hM hα1
  by_cases hσ : σ = 1
  ·
    exfalso
    subst hσ
    rw [map_one, mul_one] at hMX hM hα1
    rcases inner_cases hp hp2 hf1 hF h5 A d (mul_self_of_rep A d hd) hα1 hMX hM with
      he | h1 | h1
    · obtain ⟨e⟩ := he
      have hO : pPrimeCore 2 ↥M = ⊥ := by
        rw [← pPrimeCore_map_iso 2 e.symm, pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
      have h3 := hcM hO
      rw [Nat.card_congr e.toEquiv, card_SL2, hF] at h3
      exact false_of_psp_eq_sl hp hp2 le_rfl hf1 (Or.inr rfl)
        (by rw [← h3]; exact Nat.mul_comm _ _)
    · have h3 := hcM (hOs h1.2.1)
      rw [h1.2.2, card_SL2, hF] at h3
      exact false_of_psp_eq_sl hp hp2 le_rfl hf1 (Or.inl rfl) (by rw [← h3, one_mul])
    · have h3 := hcM (hOs h1.1)
      rw [h1.2] at h3
      exact false_of_psp_eq_sl hp hp2 le_rfl (by omega : 1 ≤ f * 2) (Or.inl rfl)
        (by rw [pow_mul (3 : ℕ) f 2, ← h3, one_mul])
  ·
    obtain ⟨hs, hc⟩ := field_card hodd A σ hσ2 hσ d hd hMX hM
    have h3 := hcM (hOs hs)
    rw [hc] at h3
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : F // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield F σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield F σ c).symm)
    rw [hk] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield F σ)
    have hk1 : 1 ≤ k := by
      by_contra h0
      rw [show k = 0 by omega, zero_pow two_ne_zero] at hKk
      omega
    have hkq := psp_inj hk1 (by norm_num) h3
    rw [hkq, hF, ← pow_mul] at hKk
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hKk
    omega

theorem eq_one_of_conf_psp {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hconf : X11.Conf G N) {f : ℕ} (hM : Blueprint.LieModel ↥N .PSp 2 3 f) : f = 1 := by
  obtain ⟨hNn, hC, -, a, b, J, K, ha, hb, -, hJN, hJC, hJp, hJm, hbJ, -, hKN, hKC, hKp, hKm⟩ :=
    hconf
  have : N.Normal := hNn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, hf1, F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hM
  rcases (show f = 1 ∨ 2 ≤ f by omega) with h1 | hf2
  · exact h1
  exfalso
  obtain ⟨hβ2, hβ1⟩ := X10Rec.conjNormal_involutive hC hb
  set β := MulAut.congr e (MulAut.conjNormal b : MulAut ↥N) with hβdef
  have hβ2' : β * β = 1 := by rw [hβdef, ← map_mul, hβ2, map_one]
  have hβ1' : β ≠ 1 := fun h => hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hcβ : ∀ x, e (MulAut.conjNormal b x) = β (e x) := fun x => by
    rw [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  obtain ⟨hK₁X, hK₁⟩ := X10Rec.fixed_pComponent_subgroupOf hKN hKC hKp
  obtain ⟨hK₀X, hK₀⟩ := isPComponent_map_fixOf hcβ hK₁X hK₁
  have eK : ↥K ≃* ↥((K.subgroupOf N).map e.toMonoidHom) := (subgroupOfEquivOfLe hKN).symm.trans
    ((K.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective)
  have hf : f = 2 := eq_two_of_fixed_psp4_three hf2 hF hβ2' hβ1' hK₀X hK₀
    (LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)) hKm)
  subst hf
  obtain ⟨hα2, hα1⟩ := X10Rec.conjNormal_involutive hC ha
  set α := MulAut.congr e (MulAut.conjNormal a : MulAut ↥N) with hαdef
  have hα2' : α * α = 1 := by rw [hαdef, ← map_mul, hα2, map_one]
  have hα1' : α ≠ 1 := fun h => hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hcα : ∀ x, e (MulAut.conjNormal a x) = α (e x) := fun x => by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  obtain ⟨hJ₁X, hJ₁⟩ := X10Rec.fixed_pComponent_subgroupOf hJN hJC hJp
  obtain ⟨hJ₀X, hJ₀⟩ := isPComponent_map_fixOf hcα hJ₁X hJ₁
  have eJ : ↥J ≃* ↥((J.subgroupOf N).map e.toMonoidHom) := (subgroupOfEquivOfLe hJN).symm.trans
    ((J.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective)
  have h360 : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 360 := by
    rw [card_of_lieModel_psl_sq (f := 1) hp2 hJm]
    norm_num
  have hJc : Nat.card ↥((J.subgroupOf N).map e.toMonoidHom) = Nat.card (pPrimeCore 2 ↥J) *
      (3 ^ 2 * ((3 ^ 2) ^ 2 - 1) / 2) := by
    rw [← Nat.card_congr eJ.toEquiv, (pPrimeCore 2 ↥J).card_eq_card_quotient_mul_card_subgroup,
      h360, show (3 : ℕ) ^ 2 * ((3 ^ 2) ^ 2 - 1) / 2 = 360 by norm_num]
    exact Nat.mul_comm _ _
  obtain ⟨hT, hJs⟩ := allTraces_of_card hp hp2 (by norm_num) hF (by norm_num) hα2' hα1' hJ₀X hJ₀
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥J))) hJc
  have : IsSimpleGroup ↥J := by
    have := hJs
    exact eJ.isSimpleGroup
  have hOJ : pPrimeCore 2 ↥J = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥J)).resolve_right fun h => ?_
    have h1 : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [h]
      have : Subsingleton (↥J ⧸ (⊤ : Subgroup ↥J)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_of_subsingleton (1 : ↥J ⧸ (⊤ : Subgroup ↥J))
    omega
  have hbc : ∀ j ∈ J, j * b = b * j := fun j hj => by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp hbJ).2 j hj
    rw [hOJ, Subgroup.map_bot, Subgroup.mem_bot] at h1
    calc j * b = b * j * (j⁻¹ * b⁻¹ * j * b) := by group
      _ = b * j := by rw [h1, mul_one]
  have hβJ : ∀ x ∈ (J.subgroupOf N).map e.toMonoidHom, β x = x := by
    rintro _ ⟨m, hm, rfl⟩
    change β (e m) = e m
    rw [← hcβ]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hbc (m : G) (mem_subgroupOf.mp hm), mul_inv_cancel_right]
  have hKc : Nat.card ↥((K.subgroupOf N).map e.toMonoidHom) = Nat.card ↥K :=
    (Nat.card_congr eK.toEquiv).symm
  have hZ := two_mul_card_of_lieModel_psp hp2 hKm
  rw [pow_one] at hZ
  have hdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  rcases card_of_fix_allTraces hp hp2 (by norm_num) hF (by norm_num) hβ2' hβ1' hT hβJ hK₀X hK₀
    with h1 | h1 <;> rw [hKc] at h1
  · exact false_of_card_le_sl le_rfl hZ hdvd Nat.card_pos h1
  · exact false_of_dvd_sl_sq le_rfl hZ hdvd h1

end CFSG.ComponentClassification.CatLeafProof.X11Char
