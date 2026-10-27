module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem isConj_conj {c x : G} (hx : IsConj c x) (g : G) :
    IsConj c (g * x * g⁻¹) :=
  hx.trans (isConj_iff.2 ⟨g, rfl⟩)

private theorem mul_self_eq_one_of (h : F5Std a z) {x : G}
    (hx : IsConj a x ∨ IsConj z x) : x * x = 1 := by
  have h2 : x ^ 2 = 1 := by simpa [h.orderOf_eq_two hx] using pow_orderOf_eq_one x
  rwa [← pow_two]

private theorem conj_eq_self_of_mem_Gx {g x : G} (hg : g ∈ Gx x) : g * x * g⁻¹ = x := by
  rw [← mem_Gx.1 hg]
  group

private theorem eq_of_conj_eq_of_mem_Gx {g t : G} (hg : g ∈ Gx a)
    (h : g * t * g⁻¹ = a) : t = a := by
  have h1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [h] at h1
  rw [h1]
  simpa using conj_eq_self_of_mem_Gx (x := a) ((Gx a).inv_mem hg)

private theorem mem_tSet_zero {b c : G} (hc : IsConj a c) (hbc : IsConj z (b * c))
    (hca : c ≠ a) (hac : IsConj a (a * c)) : c ∈ tSet a z b 0 :=
  ⟨⟨hc, hbc, hca⟩, hac⟩

private theorem exists_conj_mul {x x' y y' g₁ k : G} (hg₁ : g₁ ∈ Gx a)
    (hgx : g₁ * x * g₁⁻¹ = y) (hk : k ∈ Gxy a y)
    (hkx' : k * (g₁ * x' * g₁⁻¹) * k⁻¹ = y') :
    ∃ g ∈ Gx a, g * x * g⁻¹ = y ∧ g * x' * g⁻¹ = y' := by
  have hka : k ∈ Gx a := (mem_Gxy.1 hk).1
  have hky : k ∈ Gx y := (mem_Gxy.1 hk).2
  refine ⟨k * g₁, Subgroup.mul_mem _ hka hg₁, ?_, ?_⟩
  · have e : (k * g₁) * x * (k * g₁)⁻¹ = k * (g₁ * x * g₁⁻¹) * k⁻¹ := by
      rw [mul_inv_rev]; group
    rw [e, hgx, ← mem_Gx.1 hky]; group
  · have e : (k * g₁) * x' * (k * g₁)⁻¹ = k * (g₁ * x' * g₁⁻¹) * k⁻¹ := by
      rw [mul_inv_rev]; group
    rw [e]; exact hkx'

theorem cp_pairs_ABBB (h : F5Std a z) {t t' s s' : G} (ht : t ∈ orb2A a a) (ht' : t' ∈ orb2B a z a)
    (htt : t * t' ∈ orb2BB a z a) (hs : s ∈ orb2A a a) (hs' : s' ∈ orb2B a z a)
    (hss : s * s' ∈ orb2BB a z a) : ∃ g ∈ Gx a, g * t * g⁻¹ = s ∧ g * t' * g⁻¹ = s' := by
  obtain ⟨g₁, hg₁, hg₁t'⟩ := (h.loc.tableV.self.partition.orbit 1).transitive t'
    (by simpa [tab5Set] using ht') s' (by simpa [tab5Set] using hs')
  have ht''mem : g₁ * t * g₁⁻¹ ∈ tab5Set a z 0 :=
    (h.loc.tableV.self.partition.orbit 0).conj_mem g₁ hg₁ t (by simpa [tab5Set] using ht)
  have ht'' : g₁ * t * g₁⁻¹ ∈ orb2A a a := by simpa [tab5Set] using ht''mem
  have ht''z : IsConj z ((g₁ * t * g₁⁻¹) * s') := by
    have e : (g₁ * t * g₁⁻¹) * s' = g₁ * (t * t') * g₁⁻¹ := by rw [← hg₁t']; group
    rw [e]; exact isConj_conj htt.1 g₁
  have hcomm : (g₁ * t * g₁⁻¹) * s' = s' * (g₁ * t * g₁⁻¹) :=
    h.mul_comm (Or.inl ht''.1) (Or.inl hs'.1) (Or.inr ht''z)
  have hs't''z : IsConj z (s' * (g₁ * t * g₁⁻¹)) := by
    have h2 := ht''z
    rwa [hcomm] at h2
  have haa : a * a = 1 := mul_self_eq_one_of h (Or.inl (IsConj.refl a))
  have ht''a : g₁ * t * g₁⁻¹ ≠ a := by
    intro heq
    have ht_eq_a : t = a := eq_of_conj_eq_of_mem_Gx hg₁ heq
    have hz : IsConj z t' := by
      have h2 := htt.2
      rw [ht_eq_a] at h2
      have heq' : a * (a * t') = t' := by rw [← mul_assoc, haa, one_mul]
      rwa [heq'] at h2
    exact h.not_isConj (ht'.1.trans hz.symm)
  have hsa : s ≠ a := by
    intro heq
    have hz : IsConj z s' := by
      have h2 := hss.2
      rw [heq] at h2
      have heq' : a * (a * s') = s' := by rw [← mul_assoc, haa, one_mul]
      rwa [heq'] at h2
    exact h.not_isConj (hs'.1.trans hz.symm)
  have hs'sz : IsConj z (s' * s) := by
    have hcomm2 : s * s' = s' * s :=
      h.mul_comm (Or.inl hs.1) (Or.inl hs'.1) (Or.inr hss.1)
    have h2 := hss.1
    rwa [hcomm2] at h2
  have ht''row : g₁ * t * g₁⁻¹ ∈ tSet a z s' 0 :=
    mem_tSet_zero ht''.1 hs't''z ht''a ht''.2
  have hstSet : s ∈ tSet a z s' 0 := mem_tSet_zero hs.1 hs'sz hsa hs.2
  obtain ⟨k, hk, hkt⟩ := (h.loc.tableVI.self.partition s' hs').orbit 0 |>.transitive
    (g₁ * t * g₁⁻¹) ht''row s hstSet
  obtain ⟨g, hg, h1, h2⟩ := exists_conj_mul (x := t') (y := s') (x' := t) (y' := s)
    hg₁ hg₁t' hk hkt
  exact ⟨g, hg, h2, h1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
