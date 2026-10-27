module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End7d

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem caseB_data (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) {X : Type} [Group X]
    [Finite X] {S : Sylow 2 X} {V : Subgroup X} {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X}
    (hX : XData S V W ρ) (hB : IsCaseB S V (Subgroup.normalClosure (V : Set X))) :
    ∃ (Ob : Subgroup X) (_ : Ob.Normal) (B : Subgroup X) (i : Fin 4) (p n : ℕ)
      (_ : Fact p.Prime), Odd (Nat.card Ob) ∧ Ob ≤ B ∧ B.IsSubnormal ∧ W i ≤ B ∧ Odd p ∧
        0 < n ∧ 5 ≤ p ^ n ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧
          Nonempty (↥B ⧸ Ob.subgroupOf B ≃* PSL(2, GaloisField p n)) := by
  classical
  set M : Subgroup X := Subgroup.normalClosure (V : Set X) with hMdef
  haveI hMn : M.Normal := Subgroup.normalClosure_normal
  have hVM : V ≤ M := Subgroup.subset_normalClosure
  have hOd : goldschmidtOddCore (Mbar M) = ⊥ :=
    CFSG.Goldschmidt.goldschmidtOddCore_quotient_eq_bot ↥M
  have hY : IsGoldSemisimple (Mbar M) := ⟨hB.o2, hOd, hB.layer, hB.comps⟩
  obtain ⟨-, D, hD⟩ := sylow_eq_image hN11a hN11c hX hVM hB
  have hP : IsPlanes (D : Subgroup (Mbar M))
      (fun i => ((W i).subgroupOf M).map (mbarMk M)) := by
    have h := isPlanes_image hX hVM hB
    rwa [← hD] at h
  have hτ : IsPlaneAuts (D : Subgroup (Mbar M))
      (fun i => ((W i).subgroupOf M).map (mbarMk M)) (fun i => psiAut M (ρ i)) := by
    have h := isPlaneAuts_psi hX hVM hB
    rwa [← hD] at h
  have hperm : ∀ y : Mbar M, (∀ x ∈ (D : Subgroup (Mbar M)), y * x * y⁻¹ ∈
      (D : Subgroup (Mbar M))) → ∀ i, ∃ j, ∀ w ∈ ((W i).subgroupOf M).map (mbarMk M),
        y * w * y⁻¹ ∈ ((W j).subgroupOf M).map (mbarMk M) := by
    have h := perm_image hX.planes.card_V hX.planes.le hVM hX.perm
    rwa [← hD] at h
  obtain ⟨J, i, p, n, hp, hJ, hWJ, _, hodd, hn, h5, h8, he⟩ :=
    caseB_component hN11b hY D hP hτ hperm
  haveI hJn : J.Normal := GoldY.component_normal hB.layer hJ
  refine ⟨mbarKer M, mbarKer_normal M, mbarPre M J, i, p, n, hp, odd_card_mbarKer M,
    mbarKer_le_mbarPre M J, mbarPre_isSubnormal M J, ?_, hodd, hn, h5, h8, ?_⟩
  · intro x hx
    have hxV : x ∈ V := hX.planes.le i hx
    have hxM : x ∈ M := hVM hxV
    rw [mem_mbarPre_iff M J ⟨x, hxM⟩]
    exact hWJ (Subgroup.mem_map_of_mem (mbarMk M) (by
      rw [Subgroup.mem_subgroupOf]; exact hx))
  · exact (mbarPre_quotient M J).map (fun f => f.trans he.some)

end CFSG.OddStandard.SmallF3.Omega
