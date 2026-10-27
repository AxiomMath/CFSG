module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fusion
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Co1Cert
public import CFSG.Sporadic.Co1Patterson.NativeSetting
public import CFSG.LargeExtraspecial.AS35DQ
public import CFSG.Sporadic.Co1Block.Classes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.Co1Fusion

open Subgroup CFSG.ABGLocalTools CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
open CFSG.Sporadic.Co1Patterson
open CFSG.Blueprint (NativeSporadic.Co1)

@[expose] def IsFusWitness {Γ : Type*} [Group Γ] (t x c : Γ) (p k : ℕ) : Prop :=
  x * t = t * x ∧ c * t = t * c ∧ x ^ p = 1 ∧ x ≠ 1 ∧ c * c = 1 ∧
    (x ^ (p - 1) * c * x * c) ^ k * (x ^ (p - 1) * c * x * c) ^ k = 1 ∧
    (x ^ (p - 1) * c * x * c) ^ k ≠ 1

namespace IsFusWitness

variable {Γ Δ : Type*} [Group Γ] [Group Δ] {t x c : Γ} {p k : ℕ}

theorem map (h : IsFusWitness t x c p k) (ψ : Γ ≃* Δ) :
    IsFusWitness (ψ t) (ψ x) (ψ c) p k := by
  obtain ⟨hxt, hct, hxp, hx1, hcc, hww, hw1⟩ := h
  refine ⟨by rw [← map_mul, hxt, map_mul], by rw [← map_mul, hct, map_mul],
    by rw [← map_pow, hxp, map_one], fun h1 => hx1 (ψ.injective (by rw [h1, map_one])),
    by rw [← map_mul, hcc, map_one], ?_, fun h1 => hw1 (ψ.injective ?_)⟩
  · rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_pow, ← map_mul, hww, map_one]
  · rw [map_one, ← h1, map_pow, map_mul, map_mul, map_mul, map_pow]

theorem of_injective (f : Γ →* Δ) (hf : Function.Injective f)
    (h : IsFusWitness (f t) (f x) (f c) p k) : IsFusWitness t x c p k := by
  obtain ⟨hxt, hct, hxp, hx1, hcc, hww, hw1⟩ := h
  refine ⟨hf (by rw [map_mul, map_mul, hxt]), hf (by rw [map_mul, map_mul, hct]),
    hf (by rw [map_pow, hxp, map_one]), fun h1 => hx1 (by rw [h1, map_one]),
    hf (by rw [map_mul, hcc, map_one]), hf ?_, fun h1 => hw1 ?_⟩
  · rw [map_mul, map_pow, map_mul, map_mul, map_mul, map_pow, hww, map_one]
  · rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h1, map_one]

theorem conj (h : IsFusWitness t x c p k) (g : Γ) :
    IsFusWitness (g * t * g⁻¹) (g * x * g⁻¹) (g * c * g⁻¹) p k := by
  simpa only [MulAut.conj_apply] using h.map (MulAut.conj g)

end IsFusWitness

theorem fusCheck_sound {tR : Native.Rows} {t : GL24}
    (ht : MRep tR t) (htG : t ∈ GA) {d : List (List ℤ)} {ix ic p k : ℕ}
    (h : fusCheckOf tR d ix ic p k = true) :
    ∃ x ∈ GA, ∃ c ∈ GA, IsFusWitness t x c p k := by
  unfold fusCheckOf at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hxt⟩, hct⟩, hxp⟩, hxv⟩, hx1⟩, hcc⟩, hww⟩, hwv⟩, hw1⟩ := h
  have hrep := dag_rep (.cons rep_A₁ (.cons rep_A₂ (.cons ht .nil))) d hD
  have hmem : ∀ g ∈ dagG [A₁, A₂, t] d, g ∈ GA := by
    refine dagG_mem (fun g hg => ?_) d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h <;> rw [h]
    exacts [A₁_mem, A₂_mem, htG]
  have hX := getD_rep hrep MRep.one ix
  have hC := getD_rep hrep MRep.one ic
  set X := (Native.dag [Native.aR, Native.bR, tR] d).1.getD ix Native.one with hXdef
  set C := (Native.dag [Native.aR, Native.bR, tR] d).1.getD ic Native.one with hCdef
  set x := (dagG [A₁, A₂, t] d).getD ix 1 with hxdef
  set c := (dagG [A₁, A₂, t] d).getD ic 1 with hcdef
  have hW := ((((hX.pow (p - 1)).mul hC).mul hX).mul hC).pow k
  have hne : ∀ {R : Native.Rows} {g : GL24}, MRep R g → CFSG.Sporadic.Co1.InvNative.validRows R =
      true → ¬ R = Native.one → g ≠ 1 := by
    intro R g hR hv hR1 hg
    apply hR1
    rw [hg] at hR
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hv validRows_one
      (hR.trans MRep.one.symm)
  refine ⟨x, getD_mem_of_forall hmem ix, c, getD_mem_of_forall hmem ic, ?_, ?_, ?_,
    hne hX hxv hx1, ?_, ?_, hne hW hwv hw1⟩
  · exact (hX.mul ht).eq (hxt ▸ ht.mul hX)
  · exact (hC.mul ht).eq (hct ▸ ht.mul hC)
  · have h1 := hX.pow p
    rw [hxp] at h1
    exact h1.eq MRep.one
  · have h1 := hC.mul hC
    rw [hcc] at h1
    exact h1.eq MRep.one
  · have h1 := hW.mul hW
    rw [hww] at h1
    exact h1.eq MRep.one

theorem not_mem_of_witness {Γ : Type*} [Group Γ] [Finite Γ] {τ x c : Γ} {p k : ℕ}
    (hc : c ∈ centralizer ({τ} : Set Γ)) (hcc : c * c = 1)
    (hw : (x ^ (p - 1) * c * x * c) ^ k * (x ^ (p - 1) * c * x * c) ^ k = 1)
    (hw1 : (x ^ (p - 1) * c * x * c) ^ k ≠ 1) (N' : Subgroup Γ)
    (hN'n : (⊤ : Subgroup Γ) ⊓ centralizer ({τ} : Set Γ) ≤ normalizer (N' : Set Γ))
    (hN'o : Odd (Nat.card N')) : x ∉ N' := by
  intro hx
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcx : c * x * c⁻¹ ∈ N' := (mem_normalizer_iff.mp (hN'n ⟨mem_top c, hc⟩) x).mp hx
  rw [hcinv] at hcx
  have hm : x ^ (p - 1) * c * x * c ∈ N' := by
    have := mul_mem (pow_mem hx (p - 1)) hcx
    rwa [← mul_assoc, ← mul_assoc] at this
  have hord : orderOf ((x ^ (p - 1) * c * x * c) ^ k) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hw) hw1
  have hdvd := Subgroup.orderOf_dvd_natCard N' (pow_mem hm k)
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hN'o) (even_iff_two_dvd.mpr hdvd)

theorem card_centralizer_conj_eq (k a : NativeSporadic.Co1) :
    Nat.card (centralizer ({k * a * k⁻¹} : Set NativeSporadic.Co1)) =
      Nat.card (centralizer ({a} : Set NativeSporadic.Co1)) := by
  rw [CFSG.Sporadic.Co1Block.card_centralizer_equiv (MulAut.conj k) a, MulAut.conj_apply]

section Model


theorem exists_witness_of_isConj {τ : NativeSporadic.Co1} {t₀ : GL24} (ht₀ : t₀ ∈ GA)
    (h : IsConj (co1MatEquiv τ) ⟨t₀, ht₀⟩) {p k : ℕ}
    (hw : ∃ x ∈ GA, ∃ c ∈ GA, IsFusWitness t₀ x c p k) :
    ∃ x ∈ (⊤ : Subgroup NativeSporadic.Co1) ⊓ centralizer ({τ} : Set NativeSporadic.Co1),
      x ≠ 1 ∧ x ^ p = 1 ∧
      ∀ N' : Subgroup NativeSporadic.Co1, N' ≤ ⊤ ⊓ centralizer ({τ} : Set NativeSporadic.Co1) →
        ⊤ ⊓ centralizer ({τ} : Set NativeSporadic.Co1) ≤ normalizer (N' : Set NativeSporadic.Co1) →
        Odd (Nat.card N') → x ∉ N' := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨x, hxG, c, hcG, hw⟩ := hw
  have key : ∀ {M : Type} [Group M] (a b : M), a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := by
    intros
    group
  have hτ : (g : GL24)⁻¹ * t₀ * (g : GL24)⁻¹⁻¹ = nativeEmb τ := by
    have h1 := congrArg Subtype.val hg
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [nativeEmb_apply, ← key (g : GL24) ((co1MatEquiv τ : GA) : GL24), h1]
  have hgG : ((g : GL24))⁻¹ ∈ GA := GA.inv_mem g.2
  obtain ⟨X, hX⟩ := exists_nativeEmb_eq (GA.mul_mem (GA.mul_mem hgG hxG) (GA.inv_mem hgG))
  obtain ⟨C, hC⟩ := exists_nativeEmb_eq (GA.mul_mem (GA.mul_mem hgG hcG) (GA.inv_mem hgG))
  have h₁ := hw.conj (g : GL24)⁻¹
  rw [hτ, ← hX, ← hC] at h₁
  obtain ⟨hxτ, hcτ, hxp, hx1, hcc, hww, hw1⟩ := h₁.of_injective nativeEmb nativeEmb_injective
  refine ⟨X, mem_inf.mpr ⟨mem_top _, mem_centralizer_singleton_iff.mpr hxτ⟩, hx1, hxp,
    fun N' _ hN'n hN'o => not_mem_of_witness (mem_centralizer_singleton_iff.mpr hcτ) hcc hww
      hw1 N' hN'n hN'o⟩


theorem not_two_dvd_relIndex_aNC :
    ¬ 2 ∣ (centralizer ({aNC} : Set NativeSporadic.Co1)).relIndex ⊤ := by
  rw [relIndex_top_right]
  have h := (centralizer ({aNC} : Set NativeSporadic.Co1)).index_mul_card
  rw [card_centralizer_aNC, CFSG.Sporadic.Co1.card_Co1] at h
  have h' : (centralizer ({aNC} : Set NativeSporadic.Co1)).index = 46621575 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))
  rw [h']
  decide


theorem exists_sylow_centerIn_eq :
    ∃ P₀ : Subgroup NativeSporadic.Co1, IsSylowOf 2 P₀ ⊤ ∧ centerIn P₀ = zpowers aNC := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hQP, -⟩ := nativeSetting.exists_sylow_le_M
  refine ⟨P, isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by
    rw [relIndex_top_right]; exact P.not_dvd_index⟩, ?_⟩
  rw [centerIn_eq_map_center', nativeSetting.map_center_eq_zpowers P.isPGroup' hQP]
  rfl

theorem card_centerIn_of_isSylowOf {P : Subgroup NativeSporadic.Co1} (hP : IsSylowOf 2 P ⊤) :
    Nat.card (centerIn P) = 2 := by
  obtain ⟨P₀, hP₀, hZ⟩ := exists_sylow_centerIn_eq
  rw [card_centerIn_eq_of_isSylowOf hP₀ hP, hZ, Nat.card_zpowers, orderOf_aNC]

theorem exists_conj_eq_aNC {σ : NativeSporadic.Co1} (hσ : orderOf σ = 2)
    (hc : ¬ 2 ∣ (centralizer ({σ} : Set NativeSporadic.Co1)).relIndex ⊤) :
    ∃ k : NativeSporadic.Co1, k * aNC * k⁻¹ = σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (centralizer ({σ} : Set NativeSporadic.Co1))
  have hPG : IsSylowOf 2 P ⊤ := by
    rw [isSylowOf_iff] at hP ⊢
    refine ⟨le_top, hP.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex P _ ⊤ hP.1 le_top] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hP.2.2 h
    · exact hc h
  have hσZ : σ ∈ centerIn P := mem_centerIn_of_le_centralizer hPG hσ hP.le
  obtain ⟨P₀, hP₀, hZ₀⟩ := exists_sylow_centerIn_eq
  obtain ⟨k, -, hk⟩ := hP₀.exists_mem_conj hPG
  have haZ : aNC ∈ centerIn P₀ := by
    rw [hZ₀]
    exact mem_zpowers _
  have hkaZ : k * aNC * k⁻¹ ∈ centerIn P := by
    refine ⟨(hk _).mpr ?_, mem_centralizer_iff.mpr fun y hy => ?_⟩
    · rw [show k⁻¹ * (k * aNC * k⁻¹) * k = aNC by group]
      exact haZ.1
    · have h1 := mem_centralizer_iff.mp haZ.2 _ ((hk y).mp hy)
      calc y * (k * aNC * k⁻¹) = k * ((k⁻¹ * y * k) * aNC) * k⁻¹ := by group
        _ = k * (aNC * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
        _ = k * aNC * k⁻¹ * y := by group
  have hZ : centerIn P = zpowers σ :=
    (eq_of_le_of_card_ge (zpowers_le.mpr hσZ)
      (by rw [card_centerIn_of_isSylowOf hPG, Nat.card_zpowers, hσ])).symm
  rw [hZ] at hkaZ
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hkaZ
  have hmod := zpow_mod_orderOf σ n
  rw [hσ] at hmod
  refine ⟨k, ?_⟩
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · exfalso
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero, hn] at hmod
    have ha1 : aNC = 1 := by
      calc aNC = k⁻¹ * (k * aNC * k⁻¹) * k := by group
        _ = 1 := by rw [← hmod]; group
    have := orderOf_aNC
    rw [ha1, orderOf_one] at this
    omega
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one, hn] at hmod
    exact hmod.symm


theorem co1_fusion : ∀ Y : Subgroup NativeSporadic.Co1, ⊤ ≤ Y → Y ≤ ⊤ →
    ∀ σ ∈ Y, ∀ τ ∈ Y, orderOf σ = 2 → orderOf τ = 2 →
      ¬ 2 ∣ (centralizer ({σ} : Set NativeSporadic.Co1)).relIndex Y →
      2 ∣ (centralizer ({τ} : Set NativeSporadic.Co1)).relIndex Y →
      ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧
        ¬ p ∣ Nat.card (⊤ ⊓ centralizer ({σ} : Set NativeSporadic.Co1) :
          Subgroup NativeSporadic.Co1) ∧
        ∃ x ∈ (⊤ : Subgroup NativeSporadic.Co1) ⊓ centralizer ({τ} : Set NativeSporadic.Co1),
          x ≠ 1 ∧ x ^ p = 1 ∧
          ∀ N' : Subgroup NativeSporadic.Co1,
            N' ≤ ⊤ ⊓ centralizer ({τ} : Set NativeSporadic.Co1) →
            ⊤ ⊓ centralizer ({τ} : Set NativeSporadic.Co1) ≤
              normalizer (N' : Set NativeSporadic.Co1) →
            Odd (Nat.card N') → x ∉ N' := by
  intro Y hTY _ σ _ τ _ hσ hτ hσc hτc
  obtain rfl : Y = ⊤ := top_le_iff.mp hTY
  obtain ⟨kσ, hkσ⟩ := exists_conj_eq_aNC hσ hσc
  have hcardσ : Nat.card (⊤ ⊓ centralizer ({σ} : Set NativeSporadic.Co1) :
      Subgroup NativeSporadic.Co1) = 89181388800 := by
    rw [top_inf_eq, ← hkσ, card_centralizer_conj_eq, card_centralizer_aNC]
  have hτ' : orderOf (co1MatEquiv τ) = 2 := by rw [MulEquiv.orderOf_eq]; exact hτ
  rcases involution_classes.1 _ hτ' with h | h | h
  ·
    exfalso
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hg' : co1MatEquiv.symm g * τ * (co1MatEquiv.symm g)⁻¹ = aNC := by
      apply co1MatEquiv.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg, co1MatEquiv_aNC]
    have hcard : Nat.card (centralizer ({τ} : Set NativeSporadic.Co1)) =
        Nat.card (centralizer ({aNC} : Set NativeSporadic.Co1)) := by
      rw [← hg', card_centralizer_conj_eq]
    apply not_two_dvd_relIndex_aNC
    have e1 := (centralizer ({τ} : Set NativeSporadic.Co1)).index_mul_card
    have e2 := (centralizer ({aNC} : Set NativeSporadic.Co1)).index_mul_card
    rw [hcard] at e1
    have hpos : 0 < Nat.card (centralizer ({aNC} : Set NativeSporadic.Co1)) := Nat.card_pos
    have heq : (centralizer ({τ} : Set NativeSporadic.Co1)).index =
        (centralizer ({aNC} : Set NativeSporadic.Co1)).index :=
      Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
    rw [relIndex_top_right] at hτc ⊢
    rw [← heq]
    exact hτc
  ·
    refine ⟨11, by norm_num, by norm_num, by rw [hcardσ]; norm_num, ?_⟩
    exact exists_witness_of_isConj iotaC_mem_GA h
      (fusCheck_sound (p := 11) (k := 1) rep_iotaC iotaC_mem_GA
        co1Fus11_check)
  ·
    refine ⟨13, by norm_num, by norm_num, by rw [hcardσ]; norm_num, ?_⟩
    exact exists_witness_of_isConj A₁_mem h
      (fusCheck_sound (p := 13) (k := 3) rep_A₁ A₁_mem co1Fus13_check)

theorem co1_fusionModel :
    FusionModel (⊤ : Subgroup NativeSporadic.Co1) ⊤ where
  le := le_rfl
  normal := fun _ _ => le_normalizer (mem_top _)
  index := by omega
  even := by
    rw [card_top, CFSG.Sporadic.Co1.card_Co1]
    decide
  center := fun Y P hTY _ hP => by
    obtain rfl : Y = ⊤ := top_le_iff.mp hTY
    exact card_centerIn_of_isSylowOf hP
  fusion := co1_fusion

end Model

end CFSG.ComponentClassification.AS81.Co1Fusion
