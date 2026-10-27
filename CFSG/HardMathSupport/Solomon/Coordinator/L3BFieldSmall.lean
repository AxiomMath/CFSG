module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSU
import CFSG.RankThree.PartTwo.KFacts.K71SU3Field
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.IVK Matrix CFSG.Open

theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] {x : G} :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun a : MulAut G => a g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

theorem l3bUfix_core_small {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {f₀ : ℕ} (hf : 3 = 3 * f₀)
    (h₀ : UnitaryFieldData 2 f₀ (fixedField σ)) :
    GLAPPrimeCore 3 ↥(l3bFix (psuField h σ)) = ⊥ := by
  have := h.finite
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  obtain rfl : f₀ = 1 := by omega
  have hbar := bar_coe_fixedField h hf h₀
  set D := l3bFix (psuField h σ) with hD
  set T := l3bUT h hf h₀ with hT
  set M' := CFSG.Open.GLAPPrimeCoreOf 3 D with hM'
  have hTD : T ≤ D := l3bUT_le_fix h hf h₀
  have hcube : ∀ d ∈ D, d ^ 3 ∈ T := fun d hd => cube_fix_mem_l3bUT h hf h₀ hd
  have hM'D : M' ≤ D := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le (p := 3) D
  have hM'norm : ∀ g ∈ D, ∀ x ∈ M', g * x * g⁻¹ ∈ M' :=
    CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem
  have hM'cop : Nat.Coprime 3 (Nat.card M') :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp3 D
  have hq : 2 < 2 ^ 3 := by norm_num
  have hcent := center_unitarySU_three (h := h) hq
  set H : Subgroup (unitarySU 2 3 K 3) :=
    (M'.comap (unitaryProj h 3)) ⊓ (suIncl h h₀ hbar).range with hH
  have hHC : ∀ x ∈ H, suField h σ x = x := fun x hx =>
    (mem_range_suIncl_iff h h₀ hbar x).1 hx.2
  have hπfix : ∀ c : unitarySU 2 3 K 3, suField h σ c = c → unitaryProj h 3 c ∈ D := by
    intro c hc
    exact hTD ((mem_l3bUT_of_fixed h hf h₀ hc))
  have hHn : ∀ c, suField h σ c = c → ∀ x ∈ H, c * x * c⁻¹ ∈ H := by
    intro c hc x hx
    refine ⟨?_, ?_⟩
    · show unitaryProj h 3 (c * x * c⁻¹) ∈ M'
      rw [map_mul, map_mul, map_inv]
      exact hM'norm _ (hπfix c hc) _ hx.1
    · exact (suIncl h h₀ hbar).range.mul_mem
        ((suIncl h h₀ hbar).range.mul_mem
          ((mem_range_suIncl_iff h h₀ hbar c).2 hc) hx.2)
        ((suIncl h h₀ hbar).range.inv_mem ((mem_range_suIncl_iff h h₀ hbar c).2 hc))
  have hcentH : ∀ x : unitarySU 2 3 K 3, MulAut.conj x = 1 ↔ unitaryProj h 3 x = 1 := by
    intro x
    rw [conj_eq_one_iff_mem_center, hcent]
    have key : x ∈ unitaryScalars h 3 ↔ unitaryProj h 3 x = 1 := by
      rw [← MonoidHom.mem_ker, ker_unitaryProj]
    exact key
  have hH3 : ¬ 3 ∣ Nat.card (H.map (MulAut.conj :
      unitarySU 2 3 K 3 →* MulAut (unitarySU 2 3 K 3))) := by
    set φ₁ : H →* MulAut (unitarySU 2 3 K 3) := MulAut.conj.comp H.subtype with hφ₁
    set φ₂ : H →* ↥M' := ((unitaryProj h 3).comp H.subtype).codRestrict M' (fun x => x.2.1)
      with hφ₂
    have hrange : φ₁.range = H.map MulAut.conj := by
      rw [hφ₁, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : φ₁.ker = φ₂.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro hx
        apply Subtype.ext
        exact (hcentH _).1 hx
      · intro hx
        exact (hcentH _).2 (congrArg Subtype.val hx)
    have hc1 : Nat.card φ₁.ker * Nat.card φ₁.range = Nat.card H := by
      rw [← Subgroup.index_ker]
      exact Subgroup.card_mul_index φ₁.ker
    have hc2 : Nat.card φ₂.ker * Nat.card φ₂.range = Nat.card H := by
      rw [← Subgroup.index_ker]
      exact Subgroup.card_mul_index φ₂.ker
    have hpos : 0 < Nat.card φ₁.ker := Nat.card_pos
    have heq : Nat.card φ₁.range = Nat.card φ₂.range := by
      rw [hker] at hc1
      exact Nat.eq_of_mul_eq_mul_left (hker ▸ hpos) (hc1.trans hc2.symm)
    rw [← hrange, heq]
    intro h3
    have h4 : 3 ∣ Nat.card M' := h3.trans (Subgroup.card_subgroup_dvd_card φ₂.range)
    exact (Nat.Prime.coprime_iff_not_dvd hp3).1 hM'cop h4
  have hall := conj_eq_one_of_le_fixed h hσ hHC hHn hH3
  have hX : ∀ y ∈ M', y ∈ T → y = 1 := by
    intro y hyM hyT
    obtain ⟨g, hg⟩ := hyT
    have hx : suIncl h h₀ hbar g ∈ H := by
      refine ⟨?_, ⟨g, rfl⟩⟩
      show unitaryProj h 3 (suIncl h h₀ hbar g) ∈ M'
      have : unitaryProj h 3 (suIncl h h₀ hbar g) = y := hg
      rw [this]
      exact hyM
    have h1 := (hcentH _).1 (hall _ hx)
    rw [← hg]
    exact h1
  have hbot : M' = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have h1 : m ^ 3 = 1 := hX _ (M'.pow_mem hm 3) (hcube m (hM'D hm))
    have h2 : orderOf m ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf m ∣ Nat.card M' := Subgroup.orderOf_dvd_natCard M' hm
    have h4 : Nat.Coprime (orderOf m) 3 := Nat.Coprime.coprime_dvd_left h3 hM'cop.symm
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h2))
  exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 hbot

end CFSG.HardMathSupport.Solomon.Coordinator
