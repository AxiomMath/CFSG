module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YComponentsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YSwap

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open

private theorem isMulCommutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by
    omega
  rcases hcases with h1 | h2 | h3 | h4
  · have hs : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _
  · exact (isCyclic_of_prime_card (p := 2) h2).isMulCommutative
  · exact (isCyclic_of_prime_card (p := 3) h3).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)

private theorem mem_sup_zpowers_or {Y : Type*} [Group Y] {E : Subgroup Y} [E.Normal] {v : Y}
    (hv : v * v = 1) {g : Y} (hg : g ∈ E ⊔ Subgroup.zpowers v) :
    g ∈ E ∨ g * v ∈ E := by
  rw [Subgroup.mem_sup_of_normal_left] at hg
  obtain ⟨e, he, z, hz, rfl⟩ := hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk : v ^ k = v ^ (k % 2) :=
    zpow_eq_zpow_emod' (x := v) k (n := 2) (by rw [pow_two]; exact hv)
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero, mul_one]
    exact he
  · right
    rw [hk, h1, zpow_one, mul_assoc, hv, mul_one]
    exact he

theorem commutator_mem_of_card_le_four {Y : Type*} [Group Y] [Finite Y] (E : Subgroup Y)
    [E.Normal] (hE : Nat.card E = 3600) (hY : Nat.card Y ≤ 16200) (y v : Y) :
    y * v * y⁻¹ * v⁻¹ ∈ E := by
  have hcard : Nat.card (Y ⧸ E) ≤ 4 := by
    have hq := E.card_eq_card_quotient_mul_card_subgroup
    rw [hE] at hq
    omega
  haveI : IsMulCommutative (Y ⧸ E) := isMulCommutative_of_card_le_four hcard
  apply (QuotientGroup.eq_one_iff (y * v * y⁻¹ * v⁻¹)).mp
  have hcomm : ∀ a b : Y ⧸ E, a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm (y : Y ⧸ E) (v : Y ⧸ E)]
  group

theorem index_sup_eq_two {Y : Type} [Group Y] [Finite Y] {P F : Subgroup Y} {v : Y}
    (h : FinalData Y P F v) {T₁ T₂ : Subgroup Y} (hT : TwoA5 Y T₁ T₂) (hF : F ≤ T₁ ⊔ T₂)
    (hswap : T₁.map (MulAut.conj v).toMonoidHom = T₂) : (T₁ ⊔ T₂).index = 2 := by
  haveI hEnorm : (T₁ ⊔ T₂).Normal := by
    have hL : CFSG.ComponentClassification.Layer.subgroup Y = T₁ ⊔ T₂ :=
      layer_eq_sup_of_two hT.comp₂ hT.comp₁ hT.only
    rw [← hL]
    exact CFSG.ComponentClassification.Layer.normal Y
  have hEcard : Nat.card ↥(T₁ ⊔ T₂) = 3600 := by
    have h := card_sup_pair h.free hT.comp₁ hT.comp₂ hT.ne
    rw [hT.card₁, hT.card₂] at h
    norm_num at h
    exact h
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a :=
    component_commute_of_ne hT.comp₁ hT.comp₂ hT.ne
  have hdisj : T₁ ⊓ T₂ = ⊥ :=
    component_inf_eq_bot h.free hT.comp₁ hT.comp₂ hT.ne
  have hvE : v ∉ T₁ ⊔ T₂ := by
    intro hv
    have hT2norm : T₂ ≤ Subgroup.normalizer (T₁ : Set Y) :=
      le_trans (fun b hb => Subgroup.mem_centralizer_iff.2 (fun a ha => hcomm a ha b hb))
        (Subgroup.centralizer_le_normalizer (T₁ : Set Y))
    have hEnorm' : T₁ ⊔ T₂ ≤ Subgroup.normalizer (T₁ : Set Y) :=
      sup_le Subgroup.le_normalizer hT2norm
    have hvN : T₁.map (MulAut.conj v).toMonoidHom = T₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEnorm' hv)
    rw [hswap] at hvN
    exact hT.ne hvN.symm
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨v, hvE, fun y => ?_⟩
  set e₀ : Y := y * v * y⁻¹ * v⁻¹ with he₀def
  have he₀ : e₀ ∈ T₁ ⊔ T₂ := by
    rw [he₀def]
    exact commutator_mem_of_card_le_four (T₁ ⊔ T₂) hEcard h.card_le y v
  have he₀v : e₀ * v = y * v * y⁻¹ := by
    rw [he₀def]; group
  have hev : (e₀ * v) * (e₀ * v) = 1 := by
    rw [he₀v]
    calc (y * v * y⁻¹) * (y * v * y⁻¹) = y * (v * v) * y⁻¹ := by group
      _ = 1 := by rw [h.v_sq]; group
  obtain ⟨t, ht, ht_eq⟩ :=
    exists_conj_of_involution_mul h.v_sq hcomm hdisj hswap he₀ hev
  have hyv : y * v * y⁻¹ = t * v * t⁻¹ := by rw [← he₀v, ht_eq]
  have hgv : (t⁻¹ * y) * v = v * (t⁻¹ * y) := by
    calc (t⁻¹ * y) * v = t⁻¹ * (y * v * y⁻¹) * y := by group
      _ = t⁻¹ * (t * v * t⁻¹) * y := by rw [hyv]
      _ = v * (t⁻¹ * y) := by group
  have hg : t⁻¹ * y ∈ F ⊔ Subgroup.zpowers v := h.centralizer_le _ hgv
  have hgE : t⁻¹ * y ∈ (T₁ ⊔ T₂) ⊔ Subgroup.zpowers v :=
    (sup_le_sup_right hF (Subgroup.zpowers v)) hg
  rcases mem_sup_zpowers_or h.v_sq hgE with hgE' | hgvE
  · right
    have hy : y = t * (t⁻¹ * y) := by group
    rw [hy]
    exact mul_mem (mem_sup_right ht) hgE'
  · left
    have hy : y * v = t * ((t⁻¹ * y) * v) := by group
    rw [hy]
    exact mul_mem (mem_sup_right ht) hgvE

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
