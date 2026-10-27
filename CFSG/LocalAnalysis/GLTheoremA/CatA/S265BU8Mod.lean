module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private theorem congr_trans {T P : Type} [Group T] [Group P] (e : T ≃* P) (a : MulAut P)
    (c : MulAut T) : MulAut.congr (e.trans a) c = a * MulAut.congr e c * a⁻¹ := by
  ext t
  rfl

theorem exists_layer_of_u8_model {T : Type} [Group T] {K : Type} [Field K]
    (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : n = 5 ∨ n = 6) (e : T ≃* primeFormP h (idGram K n))
    {β : MulAut T} (hβ3 : β ^ 3 = 1) (hβD : MulAut.congr e β ∉ primeFormD h (idGram K n))
    (Eb : Subgroup (MulAut T)) (hE3 : ∀ c ∈ Eb, c ^ 3 = 1)
    (hEc : ∀ c ∈ Eb, ∀ d ∈ Eb, c * d = d * c) (hβE : ∀ c ∈ Eb, β * c = c * β)
    (h81 : 81 ≤ Nat.card Eb) (V : Subgroup (MulAut T)) (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥)
    (hVD : ∀ v ∈ V, MulAut.congr e v ∈ primeFormD h (idGram K n))
    (hEV : ∀ c ∈ Eb, ∀ v ∈ V, c * v * c⁻¹ ∈ V) :
    ∃ c ∈ Eb, c ∉ Subgroup.zpowers β ∧ GLAPLayer 3 (fixSubgroup β ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI := h.finite
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ 2 ^ 3 = 2) := fun h' => by have := h'.1; omega
  obtain ⟨σ, hσdef⟩ : ∃ σ : K ≃+* K, primeFormFieldFactor h
      (isPrimeFormGram_idGram (K := K) (n := n)) hn3 hne (MulAut.congr e β) = σ := ⟨_, rfl⟩
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := n)) hn3 hne
  have hx3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hσ3 : σ ^ 3 = 1 := by rw [← hσdef, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hβD
    rw [← hker, MonoidHom.mem_ker, hσdef, h1]
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hxo : orderOf (MulAut.congr e β) = 3 :=
    orderOf_eq_prime hx3 (fun h0 => hβD (h0 ▸ Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, N, hN⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn3 hne
      Nat.prime_three (by norm_num) (MulAut.congr e β) hxo σ hσdef hσo
  obtain ⟨g, hg⟩ : ∃ g : MulAut (primeFormP h (idGram K n)),
      g = primeFormConjHom h (idGram K n) N := ⟨_, rfl⟩
  have hgD : g ∈ primeFormD h (idGram K n) := ⟨N, hg.symm⟩
  obtain ⟨e', he'⟩ : ∃ e' : T ≃* primeFormP h (idGram K n), e' = e.trans g⁻¹ := ⟨_, rfl⟩
  have hconj : ∀ c : MulAut T, MulAut.congr e' c = g⁻¹ * MulAut.congr e c * g := fun c => by
    rw [he', congr_trans, inv_inv]
  have hfσ : MulAut.congr e' β =
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ := by
    rw [hconj, hg]
    exact hN
  have hD' : ∀ c : MulAut T, MulAut.congr e c ∈ primeFormD h (idGram K n) →
      MulAut.congr e' c ∈ primeFormD h (idGram K n) := fun c hc => by
    rw [hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgD) hc) hgD
  have hβD' : MulAut.congr e' β ∉ primeFormD h (idGram K n) := by
    intro h'
    apply hβD
    have h'' : MulAut.congr e β = g * MulAut.congr e' β * g⁻¹ := by
      rw [hconj]
      group
    rw [h'']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgD h') (Subgroup.inv_mem _ hgD)
  have hx3' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hxo' : Nat.card (Subgroup.zpowers (MulAut.congr e' β)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3' (fun h0 => hβD' (h0 ▸ Subgroup.one_mem _))
  have hbot := S265.s265_inf_zpowers_bot Nat.prime_three hxo' hβD'
  have hinj : Function.Injective (MulAut.congr e').toMonoidHom := (MulAut.congr e').injective
  have hE3' : ∀ c ∈ Eb.map (MulAut.congr e').toMonoidHom, c ^ 3 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE3 c hc, map_one]
  have hbound := HDescUniRes.card_le_three_mul_card_inf_primeFormD_of_le h hn3 hne hE3'
  rw [Subgroup.card_map_of_injective hinj] at hbound
  obtain ⟨_, ⟨⟨c, hc, rfl⟩, hcD⟩, hc1, hlay⟩ := exists_layer_of_fieldHom_u8 h hn hσo
    (E₀ := Eb.map (MulAut.congr e').toMonoidHom ⊓ primeFormD h (idGram K n))
    (V := V.map (MulAut.congr e').toMonoidHom) inf_le_right (fun c hc => hE3' c hc.1)
    (by
      rintro _ ⟨⟨c, hc, rfl⟩, -⟩ _ ⟨⟨d, hd, rfl⟩, -⟩
      rw [← map_mul, ← map_mul, hEc c hc d hd])
    (by
      rintro _ ⟨⟨c, hc, rfl⟩, -⟩
      rw [← hfσ]
      show MulAut.congr e' β * MulAut.congr e' c = MulAut.congr e' c * MulAut.congr e' β
      rw [← map_mul, ← map_mul, hβE c hc])
    (by omega) (hV2.map _) (fun h0 => hV ((Subgroup.map_eq_bot_iff_of_injective V hinj).1 h0))
    (by
      rintro _ ⟨v, hv, rfl⟩
      exact hD' v (hVD v hv))
    (by
      rintro _ ⟨⟨c, hc, rfl⟩, -⟩ _ ⟨v, hv, rfl⟩
      exact ⟨c * v * c⁻¹, hEV c hc v hv, by rw [map_mul, map_mul, map_inv]⟩)
  refine ⟨c, hc, fun hcβ => hc1 ?_, S265F3.glaPLayer_ne_bot_of_congr Nat.prime_three e' β c ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcβ
    have hmem : MulAut.congr e' (β ^ i) ∈ (primeFormD h (idGram K n) ⊓
        Subgroup.zpowers (MulAut.congr e' β) : Subgroup _) :=
      Subgroup.mem_inf.2 ⟨hcD, Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow _ β i).symm⟩⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  · rw [hfσ]
    exact hlay

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
