module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner2

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem nonempty_imJB_equiv (hKa : conjugate h.K h.a = h.K)
    (hc : Nat.card (imJB h) ≤ Nat.card (OddBar h.J)) : Nonempty (imJB h ≃* OddBar h.J) := by
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  set φ := jbToK h hKa with hφ
  let e₁ : ↥(GSLit.fixedLayer h.J h.B) ⧸ φ.ker ≃* imJB h :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr (range_jbToK h hKa))
  let g : ↥(GSLit.fixedLayer h.J h.B) ⧸ φ.ker →* OddBar h.J :=
    e.toMonoidHom.comp (QuotientGroup.map _ _ (MonoidHom.id _) (ker_jbToK_le h hKa))
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk x', rfl⟩
  let g' : imJB h →* OddBar h.J := g.comp e₁.symm.toMonoidHom
  have hg' : Function.Surjective g' := hg.comp e₁.symm.surjective
  exact ⟨MulEquiv.ofBijective g' (hg'.bijective_of_nat_card_le hc)⟩

theorem isSimpleGroup_imJB (hKa : conjugate h.K h.a = h.K) {p f : ℕ}
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hc : Nat.card (imJB h) ≤ Nat.card (OddBar h.J)) : IsSimpleGroup ↥(imJB h) := by
  obtain ⟨e⟩ := nonempty_imJB_equiv h hKa hc
  have : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  have : Nontrivial ↥(imJB h) := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end Hyp

theorem eq_of_sq_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  let := Fintype.ofFinite G
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter fun x : G => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha
    · exact hb
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem even_of_two_mul_eq {q n : ℕ} (hq : Odd q) (h : 2 * n = q ^ 2 * (q ^ 4 - 1)) : Even n := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : 1 ≤ (2 * k + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (2 * k + 1) ^ 4 - 1 = 8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k) := by
    have : (2 * k + 1) ^ 4 = 8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
    omega
  rw [h2] at h
  refine ⟨(2 * k + 1) ^ 2 * (2 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k)), ?_⟩
  have : n = (2 * k + 1) ^ 2 * (4 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k)) := by
    have e : 2 * ((2 * k + 1) ^ 2 * (4 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k))) =
        (2 * k + 1) ^ 2 * (8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k)) := by ring
    omega
  rw [this]
  ring

end CFSG.ComponentClassification.CatFactsL4U4
