module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Corr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def AE6ModelEdgePairsMem : Prop :=
  ∀ k l m : Fin 3, k ≠ l → k ≠ m → l ≠ m → ∀ E E' : Subgroup AE6Om, E ≤ ae6ModelV k → E' ≤ ae6ModelV k →
    pCoreOf 2 (ae6ModelV k) ≤ E → pCoreOf 2 (ae6ModelV k) ≤ E' → Nat.card E = 86016 → Nat.card E' = 86016 →
    Nat.card ↥(E ⊓ E') = 12288 →
    ∃ β : MulAut ↥(ae6ModelV k),
      ((ae6ModelE k l).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E.subgroupOf (ae6ModelV k) ∧
        ((ae6ModelE k m).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E'.subgroupOf (ae6ModelV k) ∧
        ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
          ∀ g : ↥(ae6ModelV k), (g : AE6Om) ∈ J ↔ ((β g : ↥(ae6ModelV k)) : AE6Om) ∈ J'

theorem ae6Word_mem_V (k : Fin 3) {w : List (Fin 8)} (hw : ∀ i ∈ w, i ≠ ae6Omit k) :
    ae6Word w ∈ ae6ModelV k := by
  unfold ae6Word
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨i, hw i hi, rfl⟩

theorem ae6ModelK_le (k : Fin 3) : ae6ModelK ≤ ae6ModelV k := by
  have h : ∀ k : Fin 3, (∀ i ∈ ([2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : List (Fin 8)), i ≠ ae6Omit k) ∧
      ∀ i ∈ ([0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : List (Fin 8)), i ≠ ae6Omit k := by decide
  unfold ae6ModelK
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ae6Word_mem_V k (h k).1
  · exact ae6Word_mem_V k (h k).2

theorem conjSub_le_of_mem {G : Type*} [Group G] {X J : Subgroup G} {g : G} (hg : g ∈ X) (hJ : J ≤ X) :
    conjSub g J ≤ X :=
  (conjSub_mono hJ).trans (conjSub_eq_self_of_mem hg).le

theorem ae6ModelK_le_E (k l : Fin 3) : ae6ModelK ≤ ae6ModelE k l :=
  le_inf (ae6ModelK_le k) (ae6ModelK_le l)

theorem le_of_mem_conjIn_model {k : Fin 3} {J : Subgroup AE6Om} (hJ : J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK) :
    J ≤ ae6ModelV k := by
  obtain ⟨g, hg, rfl⟩ := hJ
  exact conjSub_le_of_mem hg (ae6ModelK_le k)

theorem mem_ae6ModelM_iff {x : AE6Om} : x ∈ ae6ModelM ↔ ∀ i : Fin 3, x ∈ ae6ModelV i := by
  unfold ae6ModelM
  simp only [Subgroup.mem_inf, Fin.forall_fin_succ, Fin.forall_fin_zero_pi]
  simp [and_assoc]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
