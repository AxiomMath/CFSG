module

public import CFSG.HardMathSupport.Dickson.Bal207.FamD4Eight
public import CFSG.HardMathSupport.Dickson.Bal207.OrthIdxRank

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open QuadraticMap CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical2

namespace OrthFix

@[expose] def OrthInnerShapeRankInput : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2], (Nat.card F = 2 ∨ Nat.card F = 8) →
    ∀ {d : ℕ} (hd : 0 < d) {Q : QuadraticForm F (Fin d → F)}, (polarBilin Q).Nondegenerate →
    (∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ {n : ℕ}, d = 2 * n → 4 ≤ n → (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n) →
    ∀ {t : ProjOrthDerived Q}, orderOf t = 3 →
      PerfectInLayer (MulAut.conj t) ∧
      (∀ L : Subgroup (ProjOrthDerived Q),
        CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
        ∃ i : TauCeti.ValidLieTypeIndex, OrthCompIdx i.1 ∧ OrthIdxRankLt n i.1 ∧
          Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie i).Group)) ∧
      (∀ ω : MulAut (ProjOrthDerived Q),
        MulAut.congr (coordBridge Q hd).symm ω ∈ matrixProjectiveImage Q →
        ω * MulAut.conj t = MulAut.conj t * ω → ω ^ 3 = 1 →
        ∀ L : Subgroup (ProjOrthDerived Q),
          CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
          L.map ω.toMonoidHom = L) ∧
      (∀ ω : MulAut (ProjOrthDerived Q), ω * MulAut.conj t = MulAut.conj t * ω →
        ∀ L : Subgroup (ProjOrthDerived Q),
          CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
          L.map ω.toMonoidHom ≠ L → Subgroup.center ↥L = ⊥)

end OrthFix

theorem d4EightCompIdx_of_orthCompIdx {d : TauCeti.LieTypeIndex} (h : OrthCompIdx d)
    (hr : OrthFix.OrthIdxRankLt 4 d) : D4EightCompIdx d := by
  rcases orthCompIdx_cases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · cases d with
    | D s q =>
      have h' : s < 4 := hr
      have h'' : s = 4 := h2.1
      omega
    | _ => exact h2.elim
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)
  · cases d with
    | twistedA r q =>
      have h' : r < 4 := hr
      have h'' : 5 ≤ r := h5.2.2.1
      omega
    | _ => exact h5.elim

theorem compShapeOn_of_coordBridge {p : ℕ} {T : ∀ (Q : Type) [Group Q], Prop}
    (hT : IsoInvariant T) {F : Type} [Field F] {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    (hd : 0 < d) {S : Type} [Group S] (ψ : S ≃* matrixProjectiveDerived Q) (s : S)
    (h : CompShapeOn p T ((matrixProjectiveImage Q).comap
      (MulAut.congr (coordBridge Q hd).symm).toMonoidHom)
      (MulAut.conj (coordBridge Q hd (ψ s)))) :
    CompShapeOn p T ((matrixProjectiveImage Q).comap (MulAut.congr ψ).toMonoidHom)
      (MulAut.conj s) := by
  have hc : MulAut.congr (ψ.trans (coordBridge Q hd)) (MulAut.conj s) =
      MulAut.conj (coordBridge Q hd (ψ s)) :=
    MulEquiv.ext fun g => by simp [MulAut.congr_apply, MulAut.conj_apply]
  refine (CompShapeOn.of_congr hT (ψ.trans (coordBridge Q hd)) (hc ▸ h)).mono fun ω hω => ?_
  rw [Subgroup.mem_comap] at hω ⊢
  rw [Subgroup.mem_comap]
  convert hω using 1
  exact MulEquiv.ext fun g => by simp [MulAut.congr_apply]

theorem bal207PlusFamD4Eight_of_orthInnerShape (hS : OrthFix.OrthInnerShapeRankInput)
    (hGA : GriessAllModelsStatement) : Bal207PlusFamD4Eight NonSemilinD4Eight := by
  refine bal207PlusFamD4Eight_of_inner hGA fun S _ F₀ _ _ hF₀ e₀ s hs => ?_
  haveI : CharP F₀ 2 := by
    haveI := Fintype.ofFinite F₀
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [Fintype.card_eq_nat_card, hF₀]; norm_num)
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 F₀ (by norm_num)
  have hV : CFSG.GroupTheory.WeirSylow.IsPlusType (coordinateQuadPlus 4 F₀) ↔ Even 4 :=
    iff_of_true ((CFSG.GroupTheory.WeirSylow.isPlusType_congr (coordinatePlusIsometry 4 F₀)).1
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F₀ 4)) (by decide)
  let ψ := coordinatePlusWitnessEquiv F₀ e₀
  have ht : orderOf (coordBridge (coordinateQuadPlus 4 F₀) hd (ψ s)) = 3 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hs
  obtain ⟨hlay, htype, hnorm, hmoved⟩ := hS (Or.inr hF₀) hd hQ hT rfl le_rfl hV ht
  refine compShapeOn_of_coordBridge isoInvariant_d4EightCompType hd ψ s
    ⟨hlay, fun L hL => ?_, fun ω hω => hnorm ω hω, hmoved⟩
  obtain ⟨i, hi, hr, hiso⟩ := htype L hL
  exact ⟨i, d4EightCompIdx_of_orthCompIdx hi hr, hiso⟩

end CFSG.HardMathSupport.Dickson.Bal207

end
