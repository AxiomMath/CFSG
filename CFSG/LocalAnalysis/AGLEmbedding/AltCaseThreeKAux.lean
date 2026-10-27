module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen

public section

namespace CFSG.AGLEmbedding

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mem_of_isThreeCycle_of_disjoint_union {H : Subgroup (Perm α)} {S₀ S₁ S₂ : Finset α}
    (hS₁ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (S₁ ∪ S₀) → g ∈ H)
    (hS₂ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (S₂ ∪ S₀) → g ∈ H)
    (hd : _root_.Disjoint S₁ S₂) (hd₁ : _root_.Disjoint S₁ S₀) (hd₂ : _root_.Disjoint S₂ S₀)
    (h1 : 1 < #S₁) (h2 : 1 < #S₂) {x : α} (hx₀ : x ∉ S₀) (hx₁ : x ∉ S₁) (hx₂ : x ∉ S₂)
    {g : Perm α} (hg : g.IsThreeCycle) (hgS : _root_.Disjoint g.support S₀) : g ∈ H := by
  set H' : Subgroup (Perm {a // a ∉ S₀}) := H.comap ofSubtype with hH'
  have key : ∀ S : Finset α,
      (∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (S ∪ S₀) → g ∈ H) →
      ∀ g' : Perm {a // a ∉ S₀}, g'.IsThreeCycle →
        _root_.Disjoint g'.support (S.subtype (· ∉ S₀)) → g' ∈ H' := by
    intro S hSH g' hg' hd'
    refine hSH (ofSubtype g') (cycleType_ofSubtype.trans hg') ?_
    rw [support_ofSubtype, Finset.disjoint_left]
    intro a ha haS
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    rcases Finset.mem_union.mp haS with h | h
    · exact Finset.disjoint_left.mp hd' hb (Finset.mem_subtype.mpr h)
    · exact b.2 h
  have hcard : ∀ S : Finset α, _root_.Disjoint S S₀ → #(S.subtype (· ∉ S₀)) = #S := by
    intro S hS
    rw [Finset.card_subtype, Finset.filter_true_of_mem fun a ha => Finset.disjoint_left.mp hS ha]
  have hAlt := alternatingGroup_le_of_disjoint (key S₁ hS₁) (key S₂ hS₂)
    (Finset.disjoint_left.mpr fun b hb1 hb2 =>
      Finset.disjoint_left.mp hd (Finset.mem_subtype.mp hb1) (Finset.mem_subtype.mp hb2))
    (by rwa [hcard S₁ hd₁]) (by rwa [hcard S₂ hd₂]) (x := ⟨x, hx₀⟩)
    (by rwa [Finset.mem_subtype]) (by rwa [Finset.mem_subtype])
  obtain ⟨g', rfl⟩ : g ∈ (ofSubtype : Perm {a // a ∉ S₀} →* Perm α).range := by
    rw [mem_range_ofSubtype_iff]
    intro a ha
    exact Finset.disjoint_left.mp hgS ha
  have hg' : g'.IsThreeCycle := cycleType_ofSubtype.symm.trans hg
  exact hAlt hg'.mem_alternatingGroup

theorem alternatingGroup_le_of_three {H : Subgroup (Perm α)} {B₁ B₂ B₃ : Finset α}
    (h₁ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (B₂ ∪ B₃) → g ∈ H)
    (h₂ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (B₁ ∪ B₃) → g ∈ H)
    (h₃ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support (B₁ ∪ B₂) → g ∈ H)
    (d₁₂ : _root_.Disjoint B₁ B₂) (d₁₃ : _root_.Disjoint B₁ B₃) (d₂₃ : _root_.Disjoint B₂ B₃)
    (c₁ : 1 < #B₁) (c₂ : 1 < #B₂) (c₃ : 1 < #B₃) {x : α} (hx₁ : x ∉ B₁) (hx₂ : x ∉ B₂)
    (hx₃ : x ∉ B₃) : alternatingGroup α ≤ H := by
  have h₀ : ∀ g : Perm α, g.IsThreeCycle → _root_.Disjoint g.support B₃ → g ∈ H :=
    fun g hg hgB => mem_of_isThreeCycle_of_disjoint_union h₁ h₂ d₁₂.symm d₂₃ d₁₃ c₂ c₁ hx₃ hx₂
      hx₁ hg hgB
  exact alternatingGroup_le_of_disjoint h₀ h₃
    (Finset.disjoint_union_right.mpr ⟨d₁₃.symm, d₂₃.symm⟩) c₃
    (c₁.trans_le (Finset.card_le_card Finset.subset_union_left)) hx₃ (by simp [hx₁, hx₂])

theorem exists_three_disjoint_cycles {p : ℕ} (hp : 2 ≤ p) (hcard : 3 * p + 1 ≤ Fintype.card α) :
    ∃ c₁ c₂ c₃ : Perm α, c₁.IsCycle ∧ c₂.IsCycle ∧ c₃.IsCycle ∧ #c₁.support = p ∧
      #c₂.support = p ∧ #c₃.support = p ∧ _root_.Disjoint c₁.support c₂.support ∧
      _root_.Disjoint c₁.support c₃.support ∧ _root_.Disjoint c₂.support c₃.support ∧
      ∃ x, x ∉ c₁.support ∧ x ∉ c₂.support ∧ x ∉ c₃.support := by
  obtain ⟨s₁, -, hs₁⟩ := Finset.exists_subset_card_eq (s := (univ : Finset α)) (n := p)
    (by rw [card_univ]; omega)
  obtain ⟨s₂, hs₂u, hs₂⟩ := Finset.exists_subset_card_eq (s := univ \ s₁) (n := p)
    (by rw [card_sdiff_of_subset (subset_univ _), card_univ, hs₁]; omega)
  have hd₁₂ : _root_.Disjoint s₁ s₂ :=
    Finset.disjoint_left.mpr fun a ha ha2 => (Finset.mem_sdiff.mp (hs₂u ha2)).2 ha
  obtain ⟨s₃, hs₃u, hs₃⟩ := Finset.exists_subset_card_eq (s := univ \ (s₁ ∪ s₂)) (n := p)
    (by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, card_union_of_disjoint hd₁₂, hs₁, hs₂]
      omega)
  have hd₁₃ : _root_.Disjoint s₁ s₃ := Finset.disjoint_left.mpr fun a ha ha3 =>
    (Finset.mem_sdiff.mp (hs₃u ha3)).2 (Finset.mem_union_left _ ha)
  have hd₂₃ : _root_.Disjoint s₂ s₃ := Finset.disjoint_left.mpr fun a ha ha3 =>
    (Finset.mem_sdiff.mp (hs₃u ha3)).2 (Finset.mem_union_right _ ha)
  obtain ⟨x, hx⟩ : (univ \ (s₁ ∪ s₂ ∪ s₃)).Nonempty := by
    rw [← Finset.card_pos, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd₁₃, hd₂₃⟩),
      card_union_of_disjoint hd₁₂, hs₁, hs₂, hs₃]
    omega
  obtain ⟨c₁, hc₁, rfl⟩ := exists_isCycle_support_eq (s := s₁) (by omega)
  obtain ⟨c₂, hc₂, rfl⟩ := exists_isCycle_support_eq (s := s₂) (by omega)
  obtain ⟨c₃, hc₃, rfl⟩ := exists_isCycle_support_eq (s := s₃) (by omega)
  simp only [Finset.mem_sdiff, mem_univ, mem_union, true_and, not_or] at hx
  exact ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, hs₁, hs₂, hs₃, hd₁₂, hd₁₃, hd₂₃, x, hx.1.1, hx.1.2, hx.2⟩

variable {K : Type*} [Group K] [Finite K] {n p : ℕ}

theorem exists_three_disjoint_cycles_mem_sylow (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 * p + 1 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) :
    ∃ c₁ ∈ (T : Subgroup K), ∃ c₂ ∈ (T : Subgroup K), ∃ c₃ ∈ (T : Subgroup K),
      orderOf c₁ = p ∧ orderOf c₂ = p ∧ orderOf c₃ = p ∧
      #(e c₁ : Perm (Fin n)).support = p ∧ #(e c₂ : Perm (Fin n)).support = p ∧
      #(e c₃ : Perm (Fin n)).support = p ∧
      _root_.Disjoint (e c₁ : Perm (Fin n)).support (e c₂ : Perm (Fin n)).support ∧
      _root_.Disjoint (e c₁ : Perm (Fin n)).support (e c₃ : Perm (Fin n)).support ∧
      _root_.Disjoint (e c₂ : Perm (Fin n)).support (e c₃ : Perm (Fin n)).support ∧
      ∃ x, x ∉ (e c₁ : Perm (Fin n)).support ∧ x ∉ (e c₂ : Perm (Fin n)).support ∧
        x ∉ (e c₃ : Perm (Fin n)).support := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d₁, d₂, d₃, hc₁, hc₂, hc₃, hs₁, hs₂, hs₃, hd₁₂, hd₁₃, hd₂₃, x, hx₁, hx₂, hx₃⟩ :=
    exists_three_disjoint_cycles (α := Fin n) hp.two_le (by simpa using hn)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set k₁ := e.symm ⟨d₁, mem_alternatingGroup_of_isCycle hc₁ (hs₁ ▸ hodd)⟩ with hk₁
  set k₂ := e.symm ⟨d₂, mem_alternatingGroup_of_isCycle hc₂ (hs₂ ▸ hodd)⟩ with hk₂
  set k₃ := e.symm ⟨d₃, mem_alternatingGroup_of_isCycle hc₃ (hs₃ ▸ hodd)⟩ with hk₃
  have hek₁ : (e k₁ : Perm (Fin n)) = d₁ := by simp [hk₁]
  have hek₂ : (e k₂ : Perm (Fin n)) = d₂ := by simp [hk₂]
  have hek₃ : (e k₃ : Perm (Fin n)) = d₃ := by simp [hk₃]
  have hord : ∀ k : K, orderOf k = orderOf (e k : Perm (Fin n)) := fun k => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have ho₁ : orderOf k₁ = p := by rw [hord, hek₁, hc₁.orderOf, hs₁]
  have ho₂ : orderOf k₂ = p := by rw [hord, hek₂, hc₂.orderOf, hs₂]
  have ho₃ : orderOf k₃ = p := by rw [hord, hek₃, hc₃.orderOf, hs₃]
  have hN : ∀ {a b : K} {s t : Perm (Fin n)}, (e a : Perm (Fin n)) = s →
      (e b : Perm (Fin n)) = t → _root_.Disjoint s.support t.support →
      Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set K) := by
    intro a b s t ha hb hd
    have hc : Commute a b := by
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul, ha, hb]
      exact (disjoint_iff_disjoint_support.mpr hd).commute.eq
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro c hc'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    exact ((hc.symm).zpow_left m).eq
  have hP : ∀ {k : K}, orderOf k = p → IsPGroup p (Subgroup.zpowers k) := fun ho =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  have h12 := (hP ho₁).to_sup_of_normal_right' (hP ho₂) (hN hek₁ hek₂ hd₁₂)
  have h123 := h12.to_sup_of_normal_right' (hP ho₃)
    (sup_le (hN hek₁ hek₃ hd₁₃) (hN hek₂ hek₃ hd₂₃))
  obtain ⟨Q, hQ⟩ := h123.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q T
  have hmem : ∀ k ∈ (Q : Subgroup K), g * k * g⁻¹ ∈ (T : Subgroup K) := by
    intro k hk
    rw [← hg, Sylow.coe_subgroup_smul, ← MulAut.conj_apply]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj g) _ hk
  have hconj : ∀ k : K, (e (g * k * g⁻¹) : Perm (Fin n)) =
      (e g : Perm (Fin n)) * (e k : Perm (Fin n)) * (e g : Perm (Fin n))⁻¹ := fun k => by
    simp only [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
  have hordc : ∀ k : K, orderOf (g * k * g⁻¹) = orderOf k := fun k => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hsupp : ∀ k : K, (e (g * k * g⁻¹) : Perm (Fin n)).support =
      (e k : Perm (Fin n)).support.map (e g : Perm (Fin n)).toEmbedding := fun k => by
    rw [hconj, support_conj]
  refine ⟨g * k₁ * g⁻¹, hmem k₁ (hQ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers k₁)))),
    g * k₂ * g⁻¹, hmem k₂ (hQ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers k₂)))),
    g * k₃ * g⁻¹, hmem k₃ (hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers k₃))),
    by rw [hordc, ho₁], by rw [hordc, ho₂], by rw [hordc, ho₃], ?_, ?_, ?_, ?_, ?_, ?_,
    (e g : Perm (Fin n)) x, ?_, ?_, ?_⟩
  · rw [hsupp, Finset.card_map, hek₁, hs₁]
  · rw [hsupp, Finset.card_map, hek₂, hs₂]
  · rw [hsupp, Finset.card_map, hek₃, hs₃]
  · rw [hsupp, hsupp, Finset.disjoint_map, hek₁, hek₂]
    exact hd₁₂
  · rw [hsupp, hsupp, Finset.disjoint_map, hek₁, hek₃]
    exact hd₁₃
  · rw [hsupp, hsupp, Finset.disjoint_map, hek₂, hek₃]
    exact hd₂₃
  · rw [hsupp, Finset.mem_map_equiv, hek₁]
    simpa using hx₁
  · rw [hsupp, Finset.mem_map_equiv, hek₂]
    simpa using hx₂
  · rw [hsupp, Finset.mem_map_equiv, hek₃]
    simpa using hx₃

end CFSG.AGLEmbedding
