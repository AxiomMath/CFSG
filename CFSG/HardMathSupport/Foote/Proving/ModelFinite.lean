module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.HardMathSupport.Foote.Proving

open CFSG.Blueprint CFSG.Blueprint.Chevalley Assembly.LowTwoRank

theorem finite_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) [Finite H] :
    Finite G :=
  Finite.of_equiv H e.symm.toEquiv

instance finite_generalLinearGroup (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    [Finite K] : Finite (Matrix.GeneralLinearGroup ι K) :=
  Finite.of_injective (fun u : Matrix.GeneralLinearGroup ι K => (u : Matrix ι ι K))
    fun _ _ h => Units.ext h

theorem finite_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (Matrix.GeneralLinearGroup ι K)) : Finite (StatedProj H) :=
  inferInstance

theorem finite_of_statedClassicalModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ)
    (h : StatedClassicalModel G t n p f) : Finite G := by
  obtain ⟨-, h⟩ := h
  cases t with
  | PSL =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | PSU =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | PSp =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | POmegaOdd =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | POmegaPlus =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | POmegaMinus =>
    obtain ⟨K, _, _, -, b, c, -, ⟨e⟩⟩ := h
    exact finite_of_mulEquiv e
  | _ => exact h.elim

theorem finite_of_suzukiModel' (G : Type) [Group G] (p f : ℕ) (h : SuzukiModel G p f) :
    Finite G := by
  obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := h
  exact finite_of_mulEquiv e

end CFSG.HardMathSupport.Foote.Proving
