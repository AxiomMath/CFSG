module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltReduce

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Equiv Equiv.Perm

theorem alt_of_mulEquiv (p : ℕ) (S S' : Type) [Group S] [Group S'] (e : S ≃* S')
    (h : (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∧ ¬ LieChar p S) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S' ≃* alternatingGroup (Fin n))) ∧ ¬ LieChar p S' := by
  obtain ⟨⟨n, hn, ⟨eA⟩⟩, hL⟩ := h
  exact ⟨⟨n, hn, ⟨e.symm.trans eA⟩⟩, fun ⟨τ, m, f, hm⟩ =>
    hL ⟨τ, m, f, GSThmB.OddQuot.lieModel_of_equiv e.symm hm⟩⟩

theorem rowCore_alt :
    RowCore (fun p S => (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∧
      ¬ LieChar p S) := by
  intro S _ _ _ _ p _ _ hS t ht J hJC hJs htJ hJq _ _ _ _ _ _
  obtain ⟨⟨n, -, ⟨e⟩⟩, -⟩ := hS
  set ε : S →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hε
  have hinj : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ q ∈ alternatingGroup (Fin n), ∃ x, ε x = q := fun q hq =>
    ⟨e.symm ⟨q, hq⟩, by simp [hε]⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : ε t ≠ 1 := fun h => by
    have h1 : t = 1 := hinj (by rw [h, map_one])
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : ε t * ε t = 1 := by rw [← map_mul, htt, map_one]
  set u : centralizer ({t} : Set S) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have huL : u ∈ J.subgroupOf (centralizer {t}) := htJ
  have hLq : IsTwoQuasisimple ↥(J.subgroupOf (centralizer {t})) :=
    isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC).symm hJq
  exact false_of_perfect hinj hsurj ht1 ht2 hJs hLq.1 rfl huL
    (jointKer_commute_of_isTwoQuasisimple hinj ht2 hLq)

theorem rowAlt_holds : RowAlt :=
  rowFor_of_core alt_of_mulEquiv rowCore_alt

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
