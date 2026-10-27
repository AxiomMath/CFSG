module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem isConj_conj {c x : G} (hx : IsConj c x) (g : G) :
    IsConj c (g * x * g⁻¹) :=
  hx.trans (isConj_iff.2 ⟨g, rfl⟩)

private theorem mul_self_eq_one (h : F5Std a z) {x : G}
    (hx : IsConj a x ∨ IsConj z x) : x * x = 1 := by
  have h2 : x ^ 2 = 1 := by simpa [h.orderOf_eq_two hx] using pow_orderOf_eq_one x
  rwa [← pow_two]

private theorem exists_conj_mul {s s' t t' g₁ k : G} (hg₁ : g₁ ∈ Gx a)
    (hgt : g₁ * t * g₁⁻¹ = s) (hk : k ∈ Gxy s a)
    (hkt : k * (g₁ * t' * g₁⁻¹) * k⁻¹ = s') :
    ∃ g ∈ Gx a, g * t * g⁻¹ = s ∧ g * t' * g⁻¹ = s' := by
  have hks : k ∈ Gx s := (mem_Gxy.1 hk).1
  have hka : k ∈ Gx a := (mem_Gxy.1 hk).2
  refine ⟨k * g₁, Subgroup.mul_mem _ hka hg₁, ?_, ?_⟩
  · have e : (k * g₁) * t * (k * g₁)⁻¹ = k * (g₁ * t * g₁⁻¹) * k⁻¹ := by
      rw [mul_inv_rev]; group
    rw [e, hgt, ← mem_Gx.1 hks]; group
  · have e : (k * g₁) * t' * (k * g₁)⁻¹ = k * (g₁ * t' * g₁⁻¹) * k⁻¹ := by
      rw [mul_inv_rev]; group
    rw [e]; exact hkt

theorem cp_pairs_BBB (h : F5Std a z) {t t' s s' : G} (ht : t ∈ orb2B a z a) (ht' : t' ∈ orb2B a z a)
    (htt : t * t' ∈ orb2B a z a) (hs : s ∈ orb2B a z a) (hs' : s' ∈ orb2B a z a)
    (hss : s * s' ∈ orb2B a z a) : ∃ g ∈ Gx a, g * t * g⁻¹ = s ∧ g * t' * g⁻¹ = s' := by
  obtain ⟨g₁, hg₁, hg₁t⟩ := (h.loc.tableV.self.partition.orbit 1).transitive t
    (by simpa [tab5Set] using ht) s (by simpa [tab5Set] using hs)
  have ht''mem : g₁ * t' * g₁⁻¹ ∈ tab5Set a z 1 :=
    (h.loc.tableV.self.partition.orbit 1).conj_mem g₁ hg₁ t' (by simpa [tab5Set] using ht')
  have ht'' : g₁ * t' * g₁⁻¹ ∈ orb2B a z a := by simpa [tab5Set] using ht''mem
  have htt''mem : g₁ * (t * t') * g₁⁻¹ ∈ tab5Set a z 1 :=
    (h.loc.tableV.self.partition.orbit 1).conj_mem g₁ hg₁ (t * t')
      (by simpa [tab5Set] using htt)
  have hsmt'' : s * (g₁ * t' * g₁⁻¹) ∈ orb2B a z a := by
    have e : s * (g₁ * t' * g₁⁻¹) = g₁ * (t * t') * g₁⁻¹ := by rw [← hg₁t]; group
    rw [e]; simpa [tab5Set] using htt''mem
  have hsA : IsConj a s := hs.1
  have hS : F5Std s z := h.of_isConj hsA (IsConj.refl z)
  have has : a * s = s * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hsA) (Or.inr hs.2)
  have hsa : IsConj z (s * a) := by rw [← has]; exact hs.2
  have hSa : a ∈ orb2B s z s := ⟨hsA.symm, hsa⟩
  have ht''ne : g₁ * t' * g₁⁻¹ ≠ s := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * (g₁ * t' * g₁⁻¹) = 1 := by rw [heq, hs2]
    have hc : IsConj a 1 := by
      have h' := hsmt''.1
      rwa [h1] at h'
    have ha1 : a = 1 := isConj_one_left.mp hc
    have h2 : orderOf a = 2 := h.typ.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht''row : g₁ * t' * g₁⁻¹ ∈ tSet s z a 0 := by
    refine ⟨⟨?_, ?_, ht''ne⟩, ?_⟩
    · exact hsA.symm.trans ht''.1
    · exact ht''.2
    · exact hsA.symm.trans hsmt''.1
  have hs'ne : s' ≠ s := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * s' = 1 := by rw [heq, hs2]
    have hc : IsConj a 1 := by
      have h' := hss.1
      rwa [h1] at h'
    have ha1 : a = 1 := isConj_one_left.mp hc
    have h2 : orderOf a = 2 := h.typ.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hs'row : s' ∈ tSet s z a 0 := by
    refine ⟨⟨?_, ?_, hs'ne⟩, ?_⟩
    · exact hsA.symm.trans hs'.1
    · exact hs'.2
    · exact hsA.symm.trans hss.1
  obtain ⟨k, hk, hkt⟩ := (hS.loc.tableVI.self.partition a hSa).orbit 0 |>.transitive
    (g₁ * t' * g₁⁻¹) ht''row s' hs'row
  exact exists_conj_mul hg₁ hg₁t hk hkt

theorem cp_pairs_AAAB (h : F5Std a z) {t t' s s' : G} (ht : t ∈ orb2A a a) (ht' : t' ∈ orb2A a a)
    (htt : t * t' ∈ orb2AB a z a) (hs : s ∈ orb2A a a) (hs' : s' ∈ orb2A a a)
    (hss : s * s' ∈ orb2AB a z a) : ∃ g ∈ Gx a, g * t * g⁻¹ = s ∧ g * t' * g⁻¹ = s' := by
  obtain ⟨g₁, hg₁, hg₁t⟩ := (h.loc.tableV.self.partition.orbit 0).transitive t
    (by simpa [tab5Set] using ht) s (by simpa [tab5Set] using hs)
  have ht''mem : g₁ * t' * g₁⁻¹ ∈ tab5Set a z 0 :=
    (h.loc.tableV.self.partition.orbit 0).conj_mem g₁ hg₁ t' (by simpa [tab5Set] using ht')
  have ht'' : g₁ * t' * g₁⁻¹ ∈ orb2A a a := by simpa [tab5Set] using ht''mem
  have hsmt'' : IsConj z (s * (g₁ * t' * g₁⁻¹)) := by
    have e : s * (g₁ * t' * g₁⁻¹) = g₁ * (t * t') * g₁⁻¹ := by rw [← hg₁t]; group
    rw [e]; exact isConj_conj htt.1 g₁
  have hsA : IsConj a s := hs.1
  have hS : F5Std s z := h.of_isConj hsA (IsConj.refl z)
  have has : a * s = s * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hsA) (Or.inl hs.2)
  have hsa : IsConj a (s * a) := by rw [← has]; exact hs.2
  have hSa : a ∈ orb2A s s := ⟨hsA.symm, hsA.symm.trans hsa⟩
  have ht''ne : g₁ * t' * g₁⁻¹ ≠ s := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * (g₁ * t' * g₁⁻¹) = 1 := by rw [heq, hs2]
    have hc : IsConj z 1 := by
      have h' := hsmt''
      rwa [h1] at h'
    have hz1 : z = 1 := isConj_one_left.mp hc
    have h2 : orderOf z = 2 := h.typ.orderOf_z
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht''ne' : g₁ * t' * g₁⁻¹ ≠ s * a := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * (g₁ * t' * g₁⁻¹) = a := by rw [heq, ← mul_assoc, hs2, one_mul]
    have hc : IsConj z a := by
      have h' := hsmt''
      rwa [h1] at h'
    exact h.not_isConj hc.symm
  have ht''row : g₁ * t' * g₁⁻¹ ∈ sSet s z a 1 := by
    refine ⟨⟨?_, ?_, ht''ne, ht''ne'⟩, ?_⟩
    · exact hsA.symm.trans ht''.1
    · exact hsA.symm.trans ht''.2
    · exact hsmt''
  have hs'ne : s' ≠ s := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * s' = 1 := by rw [heq, hs2]
    have hc : IsConj z 1 := by
      have h' := hss.1
      rwa [h1] at h'
    have hz1 : z = 1 := isConj_one_left.mp hc
    have h2 : orderOf z = 2 := h.typ.orderOf_z
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hs'ne' : s' ≠ s * a := by
    intro heq
    have hs2 : s * s = 1 := mul_self_eq_one h (Or.inl hsA)
    have h1 : s * s' = a := by rw [heq, ← mul_assoc, hs2, one_mul]
    have hc : IsConj z a := by
      have h' := hss.1
      rwa [h1] at h'
    exact h.not_isConj hc.symm
  have hs'row : s' ∈ sSet s z a 1 := by
    refine ⟨⟨?_, ?_, hs'ne, hs'ne'⟩, ?_⟩
    · exact hsA.symm.trans hs'.1
    · exact hsA.symm.trans hs'.2
    · exact hss.1
  obtain ⟨k, hk, hkt⟩ := (hS.loc.tableIV.self.partition a hSa).orbit 1 |>.transitive
    (g₁ * t' * g₁⁻¹) ht''row s' hs'row
  exact exists_conj_mul hg₁ hg₁t hk hkt

end CFSG.EvenSporadicStandard.HNRecog.Section4
