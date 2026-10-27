module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def I1015U3Res (K : Type) [Group K] : Prop :=
  ∃ P : Subgroup (MulAut K), P.Normal ∧ inner K ≤ P ∧
    (∀ A : Subgroup (MulAut K), IsElemAbelian 3 A → Nat.card A ≤ 3 * Nat.card ↥(A ⊓ P)) ∧
    (∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → E ≤ P → ∀ T : Subgroup K, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ E, ∀ y ∈ T, α y ∈ T) → Nat.card E ≤ 3)

theorem i1015oneU3Rank_of_res
    (h : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → I1015U3Res K) :
    I1015oneU3Rank := by
  intro K _ _ hK A hA T hT2 hT0 hinv
  obtain ⟨P, -, -, hcount, hbend⟩ := h K hK
  have hE : IsElemAbelian 3 (A ⊓ P) := isElemAbelian_inf_left hA
  have hEP : A ⊓ P ≤ P := inf_le_right
  have hb : Nat.card ↥(A ⊓ P) ≤ 3 :=
    hbend (A ⊓ P) hE hEP T hT2 hT0 (fun α hα y hy => hinv α (Subgroup.mem_inf.1 hα).1 y hy)
  have hc := hcount A hA
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res
