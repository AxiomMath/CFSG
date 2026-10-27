module

public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Fix
public import CFSG.LocalAnalysis.SteinbergBNLinearTwoOuterInvolutionRigidity
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Open.StatedDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD subfieldD_injective)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_automorphism_semilinear_isomorphism even_linear_two_involution_normal_forms)

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem powMonoidHom_two_range_eq_top : (powMonoidHom 2 : Kˣ →* Kˣ).range = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact Units.ne_zero _ hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simp [powMonoidHom, sq, ← hc]

theorem card_coordinateG_even :
    Nat.card (coordinateG K) = (Nat.card K + 1) * (Nat.card K * (Nat.card K - 1)) := by
  rw [CFSG.LinearGroups.card_coordinateG, CFSG.LinearGroups.card_coordinateB,
    powMonoidHom_two_range_eq_top, Subgroup.card_top, Nat.card_units]

theorem card_jG (k : Subfield K) :
    Nat.card (jG k) = (Nat.card k + 1) * (Nat.card k * (Nat.card k - 1)) := by
  have hinj : Function.Injective ((coordinateD K).subtype.comp (subfieldD k)) :=
    (coordinateD K).subtype_injective.comp (subfieldD_injective k)
  have h1 : Nat.card (jG k) = Nat.card ((coordinateG k).subgroupOf (coordinateD k)) :=
    Subgroup.card_map_of_injective hinj
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D k)).toEquiv,
    card_coordinateG_even]

end Card

section Main

theorem map_conj_coordinateG {K : Type} [Field K] {h : Equiv.Perm (Omega K)}
    (hh : h ∈ coordinateG K) :
    (coordinateG K).map (MulAut.conj h).toMonoidHom = coordinateG K := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hh hy) (inv_mem hh)
  · intro y hy
    refine ⟨h⁻¹ * y * h, mul_mem (mul_mem (inv_mem hh) hy) hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_gen_cartan {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSL 2 2 (2 * f)) (α : MulAut D)
    (hα : orderOf α = 2) (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) (Y : Subgroup D)
    (hYfix : ∀ y ∈ Y, α y = y) (hYcard : Nat.card ↥Y = 2 ^ f * (2 ^ (2 * f) - 1)) :
    ∃ g : D, Y ⊔ Y.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      ∃ c ∈ Y ⊓ Y.map (MulAut.conj g).toMonoidHom, Odd (orderOf c) ∧ 1 < orderOf c := by
  classical
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  let φ : D ≃* coordinateG K :=
    eD.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (pslEquivCoordinateG K))
  let φ' : D →* Equiv.Perm (Omega K) := (coordinateG K).subtype.comp φ.toMonoidHom
  have hφ'inj : Function.Injective φ' := (coordinateG K).subtype_injective.comp φ.injective
  have hφ'range : φ'.range = coordinateG K := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact (φ d).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [φ']⟩
  obtain ⟨c, hc, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism K
  let Φ : MulAut D ≃* coordinateE K := (MulAut.congr φ).trans c.symm
  have hΦ : ∀ (β : MulAut D) (d : D),
      ((φ (β d) : coordinateG K) : Equiv.Perm (Omega K)) =
        (Φ β : Equiv.Perm (Omega K)) * φ d * (Φ β : Equiv.Perm (Omega K))⁻¹ := by
    intro β d
    have h := hc (Φ β) (φ d)
    rw [show c (Φ β) = MulAut.congr φ β from c.apply_symm_apply _] at h
    rw [← h, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set a : Equiv.Perm (Omega K) := (Φ α : Equiv.Perm (Omega K)) with ha
  have haE : a ∈ coordinateE K := (Φ α).2
  have ha2 : orderOf a = 2 := by
    rw [ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hα]
  have haG : a ∉ coordinateG K := by
    intro haG
    apply hαout
    have h1 : Φ α = ⟨a, ((coordinateG_le_D K).trans (coordinateD_le_E K)) haG⟩ := rfl
    have h2 : MulAut.congr φ α = MulAut.conj (⟨a, haG⟩ : coordinateG K) := by
      have h3 := hcG ⟨a, haG⟩
      rw [← h1] at h3
      rw [← h3]
      exact (c.apply_symm_apply _).symm
    refine ⟨φ.symm ⟨a, haG⟩, ?_⟩
    apply (MulAut.congr φ).injective
    rw [h2, CFSG.LocalAnalysis.mulAutCongr_conj_eq, φ.apply_symm_apply]
  have hNF := (even_linear_two_involution_normal_forms (K := K) hf1 hK).2.2.2.2.2.2.2.2.2 a haE
    ha2
  rcases hNF with ⟨haG', -⟩ | ⟨-, -, σ, -, -, hσx, -, -, ⟨h, hhG, hah⟩, k, hk, hkcard⟩
  · exact absurd haG' haG
  have h2f : 2 * f / 2 = f := by omega
  have hk' : ∀ x, x ∈ k ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk]
    rfl
  have hkcard' : Nat.card k = 2 ^ f := by rw [hkcard, h2f]
  have hfix := fixed_eq_jG σ k hk'
  have hA : ∀ d : D, α d = d → φ' d ∈ (jG k).map (MulAut.conj h).toMonoidHom := by
    intro d hd
    have h1 : φ' (α d) = a * φ' d * a⁻¹ := hΦ α d
    rw [hd] at h1
    have h2 : a * φ' d = φ' d * a := by
      calc a * φ' d = (a * φ' d * a⁻¹) * a := by group
        _ = φ' d * a := by rw [← h1]
    rw [hah] at h2
    have hx : h⁻¹ * φ' d * h ∈ coordinateG K ⊓ Subgroup.centralizer {fieldExtension K σ} := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hhG) (φ d).2) hhG,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (h⁻¹ * φ' d * h) * fieldExtension K σ
          = h⁻¹ * (φ' d * (h * fieldExtension K σ * h⁻¹)) * h := by group
        _ = h⁻¹ * (h * fieldExtension K σ * h⁻¹ * φ' d) * h := by rw [← h2]
        _ = fieldExtension K σ * (h⁻¹ * φ' d * h) := by group
    rw [hfix] at hx
    refine ⟨h⁻¹ * φ' d * h, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hYle : Y.map φ' ≤ (jG k).map (MulAut.conj h).toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA y (hYfix y hy)
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hJcard : Nat.card ((jG k).map (MulAut.conj h).toMonoidHom) =
      2 ^ f * (2 ^ (2 * f) - 1) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, card_jG, hkcard', pow_mul']
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1, h2]
    ring
  have hYeq : Y.map φ' = (jG k).map (MulAut.conj h).toMonoidHom := by
    apply Subgroup.eq_of_le_of_card_ge hYle
    rw [hJcard, Subgroup.card_map_of_injective hφ'inj, hYcard]
  have hkK : Nat.card K = Nat.card k ^ 2 := by rw [hK, hkcard', pow_mul']
  obtain ⟨m, hmG, hgen, c₀, ⟨hc₀J, hc₀Jm⟩, hodd, hgt⟩ :=
    exists_gen_cartan_perm k hkK (by rw [hkcard']; exact hq4)
  have hxG : h * m * h⁻¹ ∈ coordinateG K := mul_mem (mul_mem hhG hmG) (inv_mem hhG)
  let x : D := φ.symm ⟨h * m * h⁻¹, hxG⟩
  have hφ'x : φ' x = h * m * h⁻¹ := by simp [φ', x]
  refine ⟨x, ?_, ?_⟩
  ·
    have hcomp : φ'.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (h * m * h⁻¹)).toMonoidHom.comp φ' := by
      ext y
      simp [← hφ'x]
    have hYx : (Y.map (MulAut.conj x).toMonoidHom).map φ' =
        ((jG k).map (MulAut.conj m).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hYeq, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hsup : (Y ⊔ Y.map (MulAut.conj x).toMonoidHom).map φ' = coordinateG K := by
      rw [Subgroup.map_sup, hYeq, hYx, ← Subgroup.map_sup, hgen]
      exact map_conj_coordinateG hhG
    apply Subgroup.map_injective hφ'inj
    rw [hsup, ← MonoidHom.range_eq_map, hφ'range]
  ·
    have hc₀G : h * c₀ * h⁻¹ ∈ coordinateG K := mul_mem (mul_mem hhG (jG_le_G k hc₀J)) (inv_mem hhG)
    let cc : D := φ.symm ⟨h * c₀ * h⁻¹, hc₀G⟩
    have hφ'c : φ' cc = h * c₀ * h⁻¹ := by simp [φ', cc]
    have hccY : cc ∈ Y := by
      have : φ' cc ∈ Y.map φ' := by
        rw [hYeq, hφ'c]
        exact ⟨c₀, hc₀J, by simp [MulAut.conj_apply]⟩
      obtain ⟨y, hy, hyc⟩ := this
      rwa [← hφ'inj hyc]
    refine ⟨cc, ⟨hccY, ?_⟩, ?_, ?_⟩
    · obtain ⟨y, hy, hyc⟩ := hc₀Jm
      have hy1 : h * y * h⁻¹ ∈ Y.map φ' := by
        rw [hYeq]
        exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
      obtain ⟨y₁, hy₁, hy₁e⟩ := hy1
      refine ⟨y₁, hy₁, ?_⟩
      apply hφ'inj
      have hc₀e : c₀ = m * y * m⁻¹ := by
        rw [← hyc]
        simp [MulAut.conj_apply]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hφ'x, hy₁e, hφ'c,
        hc₀e]
      group
    · have := orderOf_injective φ' hφ'inj cc
      rw [← this, hφ'c]
      have h3 := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective c₀
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
      rw [h3]
      exact hodd
    · have := orderOf_injective φ' hφ'inj cc
      rw [← this, hφ'c]
      have h3 := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective c₀
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
      rw [h3]
      exact hgt

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End3
