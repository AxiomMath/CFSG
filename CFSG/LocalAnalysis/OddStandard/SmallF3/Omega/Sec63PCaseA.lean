module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PSmall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_caseA [Finite G] {v y b : G} {V W Y Vb R I J : Subgroup G}
    (c : Sec63PCtx v y b V W Y Vb R I J) (hJv : CFSG.conjugate J v ≠ J) : False := by
  set J' : Subgroup G := CFSG.conjugate J v with hJ'def
  have hvb : v ∈ centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact c.hvb.symm
  have hJ'c : IsComponentIn J' (centralizer ({b} : Set G)) := by
    rw [hJ'def]; exact c.hJc.conjugate hvb
  have hJ'F : InFStar J' := by
    rw [hJ'def]; exact c.hJF.conjugate v
  have hne : J ≠ J' := by
    rw [hJ'def]; exact hJv.symm
  have h3J : J = I ∨ J = CFSG.conjugate I y := c.hthird J c.hJc c.hJF
  have h3J' : J' = I ∨ J' = CFSG.conjugate I y := c.hthird J' hJ'c hJ'F
  have hIJ : I = J ∨ I = J' := by
    rcases h3J with h | h
    · rcases h3J' with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact Or.inl h.symm
    · rcases h3J' with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hne
  have hIyJ : CFSG.conjugate I y = J ∨ CFSG.conjugate I y = J' := by
    rcases h3J with h | h
    · rcases h3J' with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact Or.inr h'.symm
    · rcases h3J' with h' | h'
      · exact Or.inl h.symm
      · exact absurd (h.trans h'.symm) hne
  have hVbJJ' : Vb ≤ J ⊔ J' := by
    refine c.hVbI.trans (sup_le ?_ ?_)
    · rcases hIJ with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · rcases hIyJ with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
  have hcomm : ∀ a ∈ J, ∀ e ∈ J', a * e = e * a :=
    c.hJc.commute_of_ne hJ'c hne
  have hconj : ∀ g ∈ R, CFSG.conjugate J g = J ∨ CFSG.conjugate J g = J' := by
    intro g hg
    have hgb : g ∈ centralizer ({b} : Set G) := (Subgroup.mem_inf.1 (c.hRle hg)).2
    have h3 := c.hthird (CFSG.conjugate J g) (c.hJc.conjugate hgb) (c.hJF.conjugate g)
    rcases h3 with h3 | h3
    · rcases hIJ with h | h
      · exact Or.inl (h3.trans h)
      · exact Or.inr (h3.trans h)
    · rcases hIyJ with h | h
      · exact Or.inl (h3.trans h)
      · exact Or.inr (h3.trans h)
  have hrel : (normalizer (J : Set G)).relIndex R ≤ 2 := sec63P_relIndex_le_two hconj
  have hfour : 4 ≤ Nat.card ↥(R ⊓ normalizer (J : Set G)) :=
    sec63P_card_inf_ge_four c.hR8 hrel
  have hR0le : R ⊓ normalizer (J : Set G) ≤
      V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) := by
    intro g hg
    obtain ⟨hgR, hgN⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgV, hgb⟩ := Subgroup.mem_inf.1 (c.hRle hgR)
    have hgN' : g ∈ normalizer (J' : Set G) := by
      have hvg : v * g = g * v :=
        Subgroup.mem_centralizer_iff.1 (c.hVc.le hgV) v (Set.mem_singleton v)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hvg' : g⁻¹ * v⁻¹ = v⁻¹ * g⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hvg]
      have hkey : v * (g * h * g⁻¹) * v⁻¹ = g * (v * h * v⁻¹) * g⁻¹ := by
        calc v * (g * h * g⁻¹) * v⁻¹ = (v * g) * h * (g⁻¹ * v⁻¹) := by group
          _ = (g * v) * h * (v⁻¹ * g⁻¹) := by rw [hvg, hvg']
          _ = g * (v * h * v⁻¹) * g⁻¹ := by group
      have h1 : h ∈ J' ↔ v * h * v⁻¹ ∈ J := by
        rw [hJ'def, sec63P_mem_conjugate_iff]
      have h2 : g * h * g⁻¹ ∈ J' ↔ g * (v * h * v⁻¹) * g⁻¹ ∈ J := by
        rw [hJ'def, sec63P_mem_conjugate_iff, hkey]
      rw [h1, h2]
      exact (Subgroup.mem_normalizer_iff.mp hgN) (v * h * v⁻¹)
    have hgW : W ≤ centralizer ({g} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (c.hWc.commute_of_ne c.hVc c.hWne a ha g hgV).symm
    have hp1 : ∀ a ∈ J, ∃ e ∈ J', a * e ∈ W := by
      intro a ha
      exact ⟨v * a * v⁻¹, sec63P_conj_mem_conjugate c.hv ha,
        sec63_diag_full c.hv c.hJc.isQuasisimple hcomm c.hWJ c.hWc a ha⟩
    have hp2 : ∀ e ∈ J', ∃ a ∈ J, a * e ∈ W := by
      intro e he
      have hve : v * (v * e * v⁻¹) * v⁻¹ = e := by
        rw [sec63P_inv_eq c.hv]
        calc v * (v * e * v) * v = (v * v) * e * (v * v) := by group
          _ = e := by rw [sec63P_mul_self c.hv]; simp
      refine ⟨v * e * v⁻¹, (sec63P_mem_conjugate_iff).mp he, ?_⟩
      have h := sec63_diag_full c.hv c.hJc.isQuasisimple hcomm c.hWJ c.hWc
          (v * e * v⁻¹) ((sec63P_mem_conjugate_iff).mp he)
      rwa [hve] at h
    have hD1 := sec63_diag_D1 (c.hJc.isQuasisimple).1 (hJ'c.isQuasisimple).1 hcomm
      hgN hgN' hgW hp1 hp2
    have hVb_le : Vb ≤ centralizer ({g} : Set G) := hVbJJ'.trans (sup_le hD1.1 hD1.2)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgV, hgb⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hVb_le ha) g (Set.mem_singleton g)).symm
  have hbound : Nat.card ↥(R ⊓ normalizer (J : Set G)) ≤ 2 :=
    c.hbound _ (c.hR2.to_le inf_le_left) hR0le
  omega

theorem sec63P_caseB [Finite G] {v y b : G} {V W Y Vb R I J : Subgroup G}
    (c : Sec63PCtx v y b V W Y Vb R I J) (hWJ : W = J) : False := by
  have hR0le : R ≤ V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) := by
    intro g hg
    obtain ⟨hgV, hgb⟩ := Subgroup.mem_inf.1 (c.hRle hg)
    have hgY : g ∈ Y := c.hVY hgV
    have hWle : W ≤ centralizer ({g} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (c.hWc.commute_of_ne c.hVc c.hWne a ha g hgV).symm
    have hK : J ≤ centralizer ({g} : Set G) := by
      rw [← hWJ]; exact hWle
    have hVb_le : Vb ≤ centralizer ({g} : Set G) :=
      sec63P_key1 c c.hJc c.hJF hgY hgb hK
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgV, hgb⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hVb_le ha) g (Set.mem_singleton g)).symm
  have hbound : Nat.card R ≤ 2 := c.hbound R c.hR2 hR0le
  have h8 : Nat.card R = 8 := c.hR8
  omega

end CFSG.OddStandard.SmallF3.Omega
