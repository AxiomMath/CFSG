module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KSubgroupL1

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

structure Trans2Data (L : Subgroup G) (F : Subgroup G) : Prop where
  trans2 : ∀ f ∈ F, f ≠ 1 → ∀ f' ∈ F, f' ≠ 1 → f ≠ f' → ∀ g ∈ F, g ≠ 1 → ∀ g' ∈ F, g' ≠ 1 →
    g ≠ g' → ∃ b ∈ L, (∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) ∧ b * f * b⁻¹ = g ∧ b * f' * b⁻¹ = g'

@[expose] def PairProp (z : G) (F : Subgroup G) (f f' : G) : Prop :=
  ∀ k ∈ Ksub z F, ∀ k' ∈ Ksub z F, k * k = 1 → k' * k' = 1 → phiv z k = f → phiv z k' = f' →
    (k * k') * (k * k') = 1

@[expose] def BadK (z : G) (F : Subgroup G) : Prop :=
  ∀ k ∈ Ksub z F, ∀ k' ∈ Ksub z F, k * k = 1 → k' * k' = 1 → phiv z k ≠ 1 → phiv z k' ≠ 1 →
    phiv z k ≠ phiv z k' → (k * k') * (k * k') ≠ 1

theorem pairProp_conj (h : OneClassData L z t) (D : NData L F) {b f f' : G} (hbL : b ∈ L)
    (hbF : ∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) (hP : PairProp z F f f') :
    PairProp z F (b * f * b⁻¹) (b * f' * b⁻¹) := by
  intro k hk k' hk' hk2 hk'2 hkf hkf'
  have hbF' : ∀ x, x ∈ F ↔ b⁻¹ * x * b⁻¹⁻¹ ∈ F := by
    intro x
    have := hbF (b⁻¹ * x * b⁻¹⁻¹)
    rw [show b * (b⁻¹ * x * b⁻¹⁻¹) * b⁻¹ = x by group] at this
    exact this.symm
  obtain ⟨hlK, hlphi⟩ := conj_mem_Ksub h D (Subgroup.inv_mem _ hbL) hbF' hk
  obtain ⟨hl'K, hl'phi⟩ := conj_mem_Ksub h D (Subgroup.inv_mem _ hbL) hbF' hk'
  have key := hP (b⁻¹ * k * b⁻¹⁻¹) hlK (b⁻¹ * k' * b⁻¹⁻¹) hl'K
    (by calc b⁻¹ * k * b⁻¹⁻¹ * (b⁻¹ * k * b⁻¹⁻¹) = b⁻¹ * (k * k) * b⁻¹⁻¹ := by group
          _ = 1 := by rw [hk2]; group)
    (by calc b⁻¹ * k' * b⁻¹⁻¹ * (b⁻¹ * k' * b⁻¹⁻¹) = b⁻¹ * (k' * k') * b⁻¹⁻¹ := by group
          _ = 1 := by rw [hk'2]; group)
    (by rw [hlphi, hkf]; group) (by rw [hl'phi, hkf']; group)
  calc (k * k') * (k * k')
      = b * ((b⁻¹ * k * b⁻¹⁻¹) * (b⁻¹ * k' * b⁻¹⁻¹) * ((b⁻¹ * k * b⁻¹⁻¹) * (b⁻¹ * k' * b⁻¹⁻¹)))
        * b⁻¹ := by group
    _ = 1 := by rw [key]; group

theorem pairProp_of_pairProp (h : OneClassData L z t) (D : NData L F) (T : Trans2Data L F)
    {f f' g g' : G} (hf : f ∈ F) (hf1 : f ≠ 1) (hf' : f' ∈ F) (hf'1 : f' ≠ 1) (hff : f ≠ f')
    (hg : g ∈ F) (hg1 : g ≠ 1) (hg' : g' ∈ F) (hg'1 : g' ≠ 1) (hgg : g ≠ g')
    (hP : PairProp z F f f') : PairProp z F g g' := by
  obtain ⟨b, hbL, hbF, hbf, hbf'⟩ := T.trans2 f hf hf1 f' hf' hf'1 hff g hg hg1 g' hg' hg'1 hgg
  rw [← hbf, ← hbf']
  exact pairProp_conj h D hbL hbF hP

omit [Finite G] in
theorem sq_mul_mul_F (D : NData L F) {k k' u u' : G} (hk : k ∈ Ksub z F) (hk' : k' ∈ Ksub z F)
    (hu : u ∈ F) (hu' : u' ∈ F) :
    (k * u * (k' * u')) * (k * u * (k' * u')) = (k * k') * (k * k') := by
  have hu_k : u * k = k * u := (mem_Ksub.1 hk).2 u hu
  have hu_k' : u * k' = k' * u := (mem_Ksub.1 hk').2 u hu
  have hu'_k : u' * k = k * u' := (mem_Ksub.1 hk).2 u' hu'
  have hu'_k' : u' * k' = k' * u' := (mem_Ksub.1 hk').2 u' hu'
  have huu' : u * u' = u' * u := D.F_comm u hu u' hu'
  have hc2 : (u * u') * (u * u') = 1 := by
    calc u * u' * (u * u') = u * (u' * u) * u' := by simp only [mul_assoc]
      _ = u * (u * u') * u' := by rw [← huu']
      _ = (u * u) * (u' * u') := by simp only [mul_assoc]
      _ = 1 := by rw [D.F_sq u hu, D.F_sq u' hu', mul_one]
  have hmm : k * u * (k' * u') = (k * k') * (u * u') := by
    calc k * u * (k' * u') = k * (u * k') * u' := by simp only [mul_assoc]
      _ = k * (k' * u) * u' := by rw [hu_k']
      _ = (k * k') * (u * u') := by simp only [mul_assoc]
  have hA : ∀ w : G, w * k = k * w → w * k' = k' * w → w * (k * k') = (k * k') * w := by
    intro w h1 h2
    calc w * (k * k') = (w * k) * k' := by simp only [mul_assoc]
      _ = (k * w) * k' := by rw [h1]
      _ = k * (w * k') := by simp only [mul_assoc]
      _ = k * (k' * w) := by rw [h2]
      _ = (k * k') * w := by simp only [mul_assoc]
  have hcomm : (u * u') * (k * k') = (k * k') * (u * u') := by
    have h1 := hA u hu_k hu_k'
    have h2 := hA u' hu'_k hu'_k'
    calc (u * u') * (k * k') = u * (u' * (k * k')) := by simp only [mul_assoc]
      _ = u * ((k * k') * u') := by rw [h2]
      _ = (u * (k * k')) * u' := by simp only [mul_assoc]
      _ = ((k * k') * u) * u' := by rw [h1]
      _ = (k * k') * (u * u') := by simp only [mul_assoc]
  calc (k * u * (k' * u')) * (k * u * (k' * u'))
      = ((k * k') * (u * u')) * ((k * k') * (u * u')) := by rw [hmm]
    _ = (k * k') * ((u * u') * (k * k')) * (u * u') := by simp only [mul_assoc]
    _ = (k * k') * ((k * k') * (u * u')) * (u * u') := by rw [hcomm]
    _ = ((k * k') * (k * k')) * ((u * u') * (u * u')) := by simp only [mul_assoc]
    _ = (k * k') * (k * k') := by rw [hc2, mul_one]

theorem goodK_or_badK (h : OneClassData L z t) (D : NData L F) (T : Trans2Data L F) :
    GoodK z F ∨ BadK z F := by
  by_cases hgood : GoodK z F
  · exact Or.inl hgood
  · right
    have hex : ∃ k ∈ Ksub z F, ∃ k' ∈ Ksub z F, k * k = 1 ∧ k' * k' = 1 ∧ phiv z k ≠ 1 ∧
        phiv z k' ≠ 1 ∧ phiv z k ≠ phiv z k' ∧ (k * k') * (k * k') ≠ 1 := by
      by_contra hcon
      apply hgood
      unfold GoodK
      intro k hk k' hk' h1 h2 h3 h4 h5
      by_contra h6
      exact hcon ⟨k, hk, k', hk', h1, h2, h3, h4, h5, h6⟩
    obtain ⟨k₁, hk₁, k₁', hk₁', hk₁2, hk₁'2, hf₁, hf₁', hff₁, hbad⟩ := hex
    intro k hk k' hk' hk2 hk'2 hf hf' hff hgood2
    have hP : PairProp z F (phiv z k) (phiv z k') := by
      intro m hm m' hm' hm2 hm'2 hmf hm'f'
      obtain ⟨u, hu, hmu⟩ := (involutions_eq h D hk hk2 hf).1 ⟨hm, hmf, hm2⟩
      obtain ⟨u', hu', hm'u'⟩ := (involutions_eq h D hk' hk'2 hf').1 ⟨hm', hm'f', hm'2⟩
      rw [hmu, hm'u', sq_mul_mul_F D hk hk' hu hu']
      exact hgood2
    have hfF := phiv_mem h D hk
    have hfF' := phiv_mem h D hk'
    have hf₁F := phiv_mem h D hk₁
    have hf₁'F := phiv_mem h D hk₁'
    have := pairProp_of_pairProp h D T hfF hf hfF' hf' hff hf₁F hf₁ hf₁'F hf₁' hff₁ hP
    exact hbad (this k₁ hk₁ k₁' hk₁' hk₁2 hk₁'2 rfl rfl)

end CFSG.EvenSporadicStandard.M23Std
