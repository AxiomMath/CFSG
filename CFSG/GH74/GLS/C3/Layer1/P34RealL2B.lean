module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage1.Thm6

section Abs

variable {F₀ : Type} [Field F₀] [Finite F₀]

@[expose] def pslRange (F₀ : Type) [Field F₀] : Subgroup (PGL2 F₀) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range

theorem pslRange_index (hodd : Odd (Nat.card F₀)) : (pslRange F₀).index = 2 :=
  pgl2_psl2Range_index_eq_two F₀ (Thm1.isOddPrimePower_of_odd F₀ hodd)

theorem oResidual_pgl2_eq (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) :
    oResidual 2 (PGL2 F₀) = pslRange F₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := pslRange_index hodd
  have hN : (pslRange F₀).Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : oResidual 2 (PGL2 F₀) ≤ pslRange F₀ := by
    refine Prod.oResidual_le_of_isPGroup_quotient (N := pslRange F₀) ?_
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, ← Subgroup.index_eq_card]
    exact hidx
  have hc1 := Proofs2.card_le_two_mul_oResidual hodd h3
  have hc2 := Subgroup.card_mul_index (pslRange F₀)
  rw [hidx] at hc2
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem exists_four_le_pslRange (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) :
    ∃ V : Subgroup (PGL2 F₀), V ≤ pslRange F₀ ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1 :=
  Proofs2.exists_four_le_of_isL2 (K := PGL2 F₀) (pslRange F₀)
    ⟨F₀, inferInstance, inferInstance, ⟨hodd, h3⟩,
      ⟨(MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm.trans
        (L2.equivPSL F₀).symm⟩⟩

end Abs

section Shear

variable {F₀ : Type} [Field F₀] [Finite F₀] {M : Type} [Group M] [Finite M]

theorem shear_abs (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) {Y S : Subgroup M}
    (φ : ↥Y ≃* PGL2 F₀) (hSY : S ≤ Y) (hS : IsSylowOf 2 S Y)
    (hgen : ∀ a ∈ S, a ∈ closure {p : M | p ∈ S ∧ p * p = 1}) :
    (∃ x ∈ S, x * x = 1 ∧ x ∉ (oResidual 2 ↥Y).map Y.subtype) ∧
    (∃ V : Subgroup M, V ≤ S ∧ V ≤ (oResidual 2 ↥Y).map Y.subtype ∧ Nat.card V = 4 ∧
      ∀ v ∈ V, v * v = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOY : (oResidual 2 ↥Y).map φ.toMonoidHom = oResidual 2 (PGL2 F₀) :=
    Prod.map_oResidual φ.toMonoidHom φ.surjective Nat.prime_two
  have hOJ : (oResidual 2 ↥Y).map φ.toMonoidHom = pslRange F₀ := by
    rw [hOY]
    exact oResidual_pgl2_eq hodd h3
  have hYcard : Nat.card ↥Y = Nat.card (PGL2 F₀) := Nat.card_congr φ.toEquiv
  have hJidx := pslRange_index hodd
  have hJcard := Subgroup.card_mul_index (pslRange F₀)
  rw [hJidx] at hJcard
  constructor
  · by_contra hcon
    push Not at hcon
    have hSI : S ≤ (oResidual 2 ↥Y).map Y.subtype := by
      intro a ha
      have h1 := hgen a ha
      refine (Subgroup.closure_le _).2 (fun p hp => hcon p hp.1 hp.2) h1
    set A : Subgroup (PGL2 F₀) := (S.subgroupOf Y).map φ.toMonoidHom with hA
    have hAJ : A ≤ pslRange F₀ := by
      rintro _ ⟨y, hy, rfl⟩
      have : (y : M) ∈ (oResidual 2 ↥Y).map Y.subtype := hSI hy
      obtain ⟨u, hu, hu'⟩ := this
      have : u = y := Subtype.ext hu'
      rw [← hOJ]
      exact ⟨u, hu, by rw [this]⟩
    have hAcard : Nat.card A = Nat.card S := by
      rw [hA, Subgroup.card_map_of_injective φ.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
    have hdvd : Nat.card A ∣ Nat.card (pslRange F₀) := Subgroup.card_dvd_of_le hAJ
    rw [hAcard, hS.card_eq, hYcard] at hdvd
    have hne : Nat.card (PGL2 F₀) ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ^ ((Nat.card (PGL2 F₀)).factorization 2 + 1) ∣ Nat.card (PGL2 F₀) := by
      have h4 := mul_dvd_mul_right hdvd 2
      rw [hJcard, ← pow_succ] at h4
      exact h4
    have h3' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 h2
    omega
  ·
    obtain ⟨V₀, hV₀J, hV₀c, hV₀sq⟩ := exists_four_le_pslRange hodd h3
    set V₁ : Subgroup ↥Y := V₀.map φ.symm.toMonoidHom with hV₁
    have hV₁O : V₁ ≤ oResidual 2 ↥Y := by
      rintro _ ⟨v, hv, rfl⟩
      have : v ∈ (oResidual 2 ↥Y).map φ.toMonoidHom := by rw [hOJ]; exact hV₀J hv
      obtain ⟨u, hu, rfl⟩ := this
      simpa using hu
    set V₂ : Subgroup M := V₁.map Y.subtype with hV₂
    have hV₂I : V₂ ≤ (oResidual 2 ↥Y).map Y.subtype := Subgroup.map_mono hV₁O
    have hV₂Y : V₂ ≤ Y := Subgroup.map_subtype_le _
    have hV₂card : Nat.card V₂ = 4 := by
      rw [hV₂, Subgroup.card_map_of_injective Y.subtype_injective, hV₁,
        Subgroup.card_map_of_injective φ.symm.injective, hV₀c]
    have hV₂sq : ∀ v ∈ V₂, v * v = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hu
      have h1 := hV₀sq v hv
      have : φ.symm v * φ.symm v = 1 := by rw [← map_mul, h1, map_one]
      show ((φ.symm v : ↥Y) : M) * ((φ.symm v : ↥Y) : M) = 1
      exact congrArg Subtype.val this
    have hV₂2 : IsPGroup 2 ↥V₂ := IsPGroup.of_card (n := 2) (by rw [hV₂card]; norm_num)
    obtain ⟨k, hkY, hk⟩ := Thm1.exists_conj_le_of_isSylowOf hS hV₂Y hV₂2
    have hIn : ∀ y ∈ (oResidual 2 ↥Y).map Y.subtype, k⁻¹ * y * k ∈
        (oResidual 2 ↥Y).map Y.subtype := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨(⟨k, hkY⟩ : ↥Y)⁻¹ * u * ⟨k, hkY⟩, ?_, ?_⟩
      · have := (Prod.oResidual_normal 2 ↥Y).conj_mem u hu (⟨k, hkY⟩ : ↥Y)⁻¹
        simpa using this
      · simp
    refine ⟨V₂.map (MulAut.conj k⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have := hk y hy
      simpa [MulAut.conj_apply] using this
    · rintro _ ⟨y, hy, rfl⟩
      have := hIn y (hV₂I hy)
      simpa [MulAut.conj_apply] using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hV₂card]
    · rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc k⁻¹ * y * k⁻¹⁻¹ * (k⁻¹ * y * k⁻¹⁻¹) = k⁻¹ * (y * y) * k⁻¹⁻¹ := by group
        _ = 1 := by rw [hV₂sq y hy]; group

end Shear

end CFSG.GH74.GLS.C3.Layer1.P34Real
