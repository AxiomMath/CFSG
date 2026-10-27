module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z11
public import CFSG.ClassicalInvolution.Asc77.AscT7Y4
public import CFSG.ClassicalInvolution.Asc77.AscT7Z14
public import CFSG.ClassicalInvolution.Asc77.AscT7Z16
public import CFSG.ClassicalInvolution.Asc77.AscT7Z23
public import CFSG.ClassicalInvolution.Asc77.AscT7Z7

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped commutatorElement MatrixGroups

variable (p f : ℕ) [Fact p.Prime]

variable {p f}

namespace T7Z

theorem c23_chain5_of_inputs (hq1 : p ^ f % 4 = 1) (hodd : T7Z.OddCenterClassical) :
    C23_chain5 p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hKΩ : K ∈ Ω := hst.mem
  have hpi : piSign p f = true := by simp [piSign, hq1]
  rw [hpi] at hE
  have hE' : LayerOrthType p f Ω e 6 (piSign p f) := by rw [hpi]; exact hE
  obtain ⟨hOE, hOY⟩ := T7Z.oddCore_layers_eq_bot hodd hs hd hα.1 hE' (Or.inl hY)
  have hex : ExactMembers Ω := T7Z.exactMembers_of_layer hs hd hα.1 hd.he2 hOE hE'
  obtain ⟨hpJ, hpJ', hEle⟩ := T7Z.eSide hs hd hα.1 hex hOE hE
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf0⟩
  obtain ⟨i, hi⟩ : ∃ i : GaloisField p f, i * i = -1 := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p f) = p ^ f := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p f hf0
    have := (FiniteField.isSquare_neg_one_iff (F := GaloisField p f)).mpr (by
      rw [hcard]
      omega)
    obtain ⟨r, hr⟩ := this
    exact ⟨r, hr.symm⟩
  obtain ⟨J₁, K₃, hJ₁, hpair, hK₃z, hK₃u, hK₃perf, hYle, hJle, hJ'le⟩ :=
    T7Z.ySide5 hs hd hex hOY hY hi
  have hcomm : Commutes K K₃ :=
    T7Z.commutes_of_perfect_centralizer hs hd hex hK₃z hK₃u hK₃perf
  have hpJ₁ : ∃ W', LinearBlockStandardPair (GaloisField p f) W' K J₁ := by
    rcases hJ₁ with rfl | rfl
    · exact hpJ
    · exact hpJ'
  refine ⟨![K, J₁, K₃], hKΩ, hcomm, hpJ₁, hpair, ?_⟩
  have hsup : (⨆ k, (![K, J₁, K₃] : Fin 3 → Subgroup G) k) = K ⊔ J₁ ⊔ K₃ := by
    refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · fin_cases k
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 0
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 1
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 2
  have hYH : exactLayer Ω u ≤ K ⊔ J₁ ⊔ K₃ :=
    hYle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hEH : exactLayer Ω e ≤ K ⊔ J₁ ⊔ K₃ :=
    hEle.trans (sup_le (sup_le (hJ'le.trans hYH) (le_sup_left.trans le_sup_left))
      (hJle.trans hYH))
  rw [hsup]
  refine eq_top_iff.mpr ?_
  rw [← hα.2, rLayer_eq_exactLayer hp2 hq hst.hyp hd.he2,
    rLayer_eq_exactLayer hp2 hq hst.hyp hd.hu2]
  exact sup_le hEH hYH

end T7Z

end CFSG.ClassicalInvolution.Asc77
