module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyModelTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXA5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)


theorem t263SelWP_of_model {Q : ℕ → TauCeti.CFSGIndex → Prop}
    (hmod : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X], catalogIs X (Q p) →
      ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T)
    (hinn : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω)
      (x : Ω), S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (↥S ⧸ Subgroup.center ↥S) (Q p) → x ^ p = 1 →
      InnDiagOn p (Subgroup.zpowers x) S → InducesInnerMod p S x) :
    T263SelWP Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  obtain ⟨hBel, hBcard, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
      ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  have hB₀B : B₀ ≤ B := hB₀.1
  have hxB : x ∈ B := hB₀B hxB₀
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  obtain ⟨T, _, _, ⟨e⟩, hTsel⟩ := hmod p hp hp2 _ hcat
  have hin : InducesInnerMod p S x := hinn p hp hp2 Ω S x hSn hSq hSp hcat hxp hInn
  obtain ⟨-, -, hPT'⟩ :=
    norm_data_dx hSn (fun a ha b hb => isElemAbelian_commute hBel ha hb) hB₀B hxB₀ hBT'
  have hS₁x : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      Subgroup.centralizer ({x} : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : g₁ ∈ Subgroup.centralizer ({x} : Set Ω) :=
      Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hB₀B hg₁) hxB)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 hg₂.2) (inv_mem h1)) (inv_mem hg₂.2)
  have hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := le_inf (hPT'.trans hT'S) hS₁x
  obtain ⟨J, hJ | ⟨hp3, hJc, h60⟩⟩ := selComp_or_a5_of_modelSel hp hp2 hSn hSq hSp hSc hF2 hxp
    hxC hInn hin hxcomm hS₁S (hT'2.to_le hPT') e hTsel
  · exact Or.inr ⟨J, hJ⟩
  · subst hp3
    refine Or.inl (t263GConcl_of_a5 hSn hBel ?_ hxB hJc h60)
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h4

theorem t263SelWP_excEasy : T263SelWP t263GExcEasy :=
  t263SelWP_of_model (fun _ hp hp2 _ _ h => exists_modelSel_excEasy hp hp2 h)
    (fun _ hp hp2 _ _ _ _ _ hSn hSq hSp hcat hxp hInn =>
      inducesInnerMod_excEasy hp hp2 hSn hSq hSp hcat hxp hInn)

theorem t263SelWP_e6Easy : T263SelWP t263GE6Easy :=
  t263SelWP_of_model (fun _ hp hp2 _ _ h => exists_modelSel_e6Easy hp hp2 h)
    (fun _ hp hp2 _ _ _ _ _ hSn hSq hSp hcat hxp hInn =>
      inducesInnerMod_e6Easy hp hp2 hSn hSq hSp hcat hxp hInn)

theorem t263SelWP_td4Easy : T263SelWP t263GTD4Easy :=
  t263SelWP_of_model (fun _ hp hp2 _ _ h => exists_modelSel_td4Easy hp hp2 h)
    (fun _ hp hp2 _ _ _ _ _ hSn hSq hSp hcat hxp hInn =>
      inducesInnerMod_td4Easy hp hp2 hSn hSq hSp hcat hxp hInn)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
