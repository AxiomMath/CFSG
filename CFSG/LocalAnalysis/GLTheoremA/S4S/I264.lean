module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

section CoverTransport

variable {Q Q' : Type} [Group Q] [Group Q']

private theorem catalogIs_of_mulEquiv' {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {P : TauCeti.CFSGIndex → Prop} (h : catalogIs S P) : catalogIs S' P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem center_map_of_mulEquiv (e : Q ≃* Q') :
    (Subgroup.center Q).map e.toMonoidHom = Subgroup.center Q' :=
  Subgroup.map_center_eq e

private theorem card_center_of_mulEquiv (e : Q ≃* Q') :
    Nat.card (Subgroup.center Q') = Nat.card (Subgroup.center Q) := by
  rw [← center_map_of_mulEquiv e, Subgroup.card_map_of_injective e.injective]

private theorem isChevSimple_of_mulEquiv' {r : ℕ} {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : IsChevSimple r S) : IsChevSimple r S' := by
  rcases h with h | h
  · exact Or.inl (catalogIs_of_mulEquiv' e h)
  · exact Or.inr (catalogIs_of_mulEquiv' e h)

private theorem k1Cover_of_mulEquiv {p : ℕ} (e : Q ≃* Q') (h : K1Cover p Q) : K1Cover p Q' := by
  obtain ⟨hq, hc⟩ := h
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq, ?_⟩
  exact isChevSimple_of_mulEquiv' (QuotientGroup.congr _ _ e (center_map_of_mulEquiv e)) hc

private theorem simpleCoverList_of_mulEquiv {P : TauCeti.CFSGIndex → Prop} (e : Q ≃* Q')
    (h : SimpleCoverList Q P) : SimpleCoverList Q' P := by
  obtain ⟨hc, hP⟩ := h
  refine ⟨?_, catalogIs_of_mulEquiv' e hP⟩
  rw [← center_map_of_mulEquiv e, hc, Subgroup.map_bot]

private theorem fullLinearCover_of_mulEquiv {u : Bool} {d q : ℕ} (e : Q ≃* Q')
    (h : FullLinearCover u d q Q) : FullLinearCover u d q Q' := by
  obtain ⟨K, hF, hfin, hK⟩ := h
  refine ⟨K, hF, hfin, ?_⟩
  cases u
  · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
    obtain ⟨hc, ⟨f⟩⟩ := hK
    exact ⟨hc, ⟨e.symm.trans f⟩⟩
  · simp only [↓reduceIte] at hK ⊢
    obtain ⟨hc, ⟨f⟩⟩ := hK
    exact ⟨hc, ⟨e.symm.trans f⟩⟩

private theorem k2LinearCover_of_mulEquiv {p : ℕ} (e : Q ≃* Q') (h : K2LinearCover p Q) :
    K2LinearCover p Q' := by
  obtain ⟨hp, h⟩ := h
  refine ⟨hp, ?_⟩
  rcases h with ⟨n, hn1, hne, hF⟩ | ⟨n, hn1, hno, hF⟩ | hF
  · exact Or.inl ⟨n, hn1, hne, fullLinearCover_of_mulEquiv e hF⟩
  · exact Or.inr (Or.inl ⟨n, hn1, hno, fullLinearCover_of_mulEquiv e hF⟩)
  · exact Or.inr (Or.inr (fullLinearCover_of_mulEquiv e hF))

private theorem k3LinearCover_of_mulEquiv {p : ℕ} (e : Q ≃* Q') (h : K3LinearCover p Q) :
    K3LinearCover p Q' := by
  obtain ⟨hp, r, f, hr, hf1, h⟩ := h
  refine ⟨hp, r, f, hr, hf1, ?_⟩
  rcases h with ⟨h1, hF⟩ | ⟨h1, hF⟩
  · exact Or.inl ⟨h1, fullLinearCover_of_mulEquiv e hF⟩
  · exact Or.inr ⟨h1, fullLinearCover_of_mulEquiv e hF⟩

private theorem maximalOddCover_of_mulEquiv {i : TauCeti.CFSGIndex} (e : Q ≃* Q')
    (h : MaximalOddCover Q i) : MaximalOddCover Q' i := by
  obtain ⟨hfin, hqs, hsimp, hnon, π, hπs, hker, hcyc, hodd, huniv⟩ := h
  have hc := center_map_of_mulEquiv e
  have hmem : ∀ x : Q', x ∈ Subgroup.center Q' ↔ e.symm x ∈ Subgroup.center Q := by
    intro x
    rw [← hc, Subgroup.mem_map]
    refine Iff.trans ?_ Iff.rfl
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = e.symm x := by
        rw [← hyx]
        simp
      rw [← hyx']
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
  have hkerQ' : (π.comp e.symm.toMonoidHom).ker = Subgroup.center Q' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, hmem]
    rfl
  have hcycQ' : IsCyclic (Subgroup.center Q') := by
    have ec : Subgroup.center Q ≃* Subgroup.center Q' :=
      (MulEquiv.subgroupMap e (Subgroup.center Q)).trans (MulEquiv.subgroupCongr hc)
    exact isCyclic_of_surjective ec ec.surjective
  refine ⟨Finite.of_equiv Q e.toEquiv,
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hqs, hsimp, hnon,
    π.comp e.symm.toMonoidHom, hπs.comp e.symm.surjective, hkerQ', hcycQ',
    (card_center_of_mulEquiv e).symm ▸ hodd, ?_⟩
  intro U _ _ hUq ρ hρs hρk hρodd
  obtain ⟨f, hfs, hf⟩ := huniv U hUq ρ hρs hρk hρodd
  refine ⟨f.comp e.symm.toMonoidHom, hfs.comp e.symm.surjective, ?_⟩
  rw [← hf]
  ext x
  rfl

private theorem hatCoverList_of_mulEquiv {P : TauCeti.CFSGIndex → Prop} (e : Q ≃* Q')
    (h : HatCoverList Q P) : HatCoverList Q' P := by
  obtain ⟨i, hP, hmo, hcard⟩ := h
  exact ⟨i, hP, maximalOddCover_of_mulEquiv e hmo, by
    rw [card_center_of_mulEquiv e, hcard]⟩

private theorem k2Cover_of_mulEquiv {p : ℕ} (e : Q ≃* Q') (h : K2Cover p Q) : K2Cover p Q' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | h | h
  · exact Or.inl (simpleCoverList_of_mulEquiv e h)
  · exact Or.inr (Or.inl (simpleCoverList_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (k2LinearCover_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (hatCoverList_of_mulEquiv e h)))

private theorem k3Cover_of_mulEquiv {p : ℕ} (e : Q ≃* Q') (h : K3Cover p Q) : K3Cover p Q' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | h
  · exact Or.inl (simpleCoverList_of_mulEquiv e h)
  · exact Or.inr (Or.inl (k3LinearCover_of_mulEquiv e h))
  · exact Or.inr (Or.inr (hatCoverList_of_mulEquiv e h))

theorem fullCoverLevel_congr {p : ℕ} (e : Q ≃* Q') : fullCoverLevel p Q = fullCoverLevel p Q' := by
  classical
  unfold fullCoverLevel
  by_cases c1 : K1Cover p Q
  · have c1' : K1Cover p Q' := k1Cover_of_mulEquiv e c1
    rw [if_pos c1, if_pos c1']
  · have c1' : ¬ K1Cover p Q' := fun h => c1 (k1Cover_of_mulEquiv e.symm h)
    rw [if_neg c1, if_neg c1']
    by_cases c2 : K2Cover p Q
    · have c2' : K2Cover p Q' := k2Cover_of_mulEquiv e c2
      rw [if_pos c2, if_pos c2']
    · have c2' : ¬ K2Cover p Q' := fun h => c2 (k2Cover_of_mulEquiv e.symm h)
      rw [if_neg c2, if_neg c2']
      by_cases c3 : K3Cover p Q
      · have c3' : K3Cover p Q' := k3Cover_of_mulEquiv e c3
        rw [if_pos c3, if_pos c3']
      · have c3' : ¬ K3Cover p Q' := fun h => c3 (k3Cover_of_mulEquiv e.symm h)
        rw [if_neg c3, if_neg c3']

end CoverTransport

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.GLTheoremA
