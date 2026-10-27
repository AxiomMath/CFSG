module

public import CFSG.ClassicalInvolution.RouteD.TWYRankOdd
public import CFSG.ClassicalInvolution.RouteD.TWYRankEven
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Model
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinModels

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77

section Large

variable {p f : ℕ} [Fact p.Prime]

theorem twinYP1On_mono {P P' : StatedLieTag → ℕ → Prop} (hPP : ∀ t n, P' t n → P t n)
    (h : TwinYP1On p f P) : TwinYP1On p f P' :=
  fun G _ _ _ hnab K z S t n hrow hP' hshape T hT clsT e =>
    h G hnab K z S t n hrow (hPP t n hP') hshape T hT clsT e

theorem twinYRankOn_large (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hP1 : TwinYP1On p f TwinRow.large) :
    TwinYRankOn p f TwinRow.large := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth
  rcases hP with ⟨rfl, h5⟩ | ⟨rfl, h5⟩ | ⟨rfl, h4⟩
  · exact twinYRankOn_even hp2 hq
      (twinYP1On_mono (fun t n h => by
        rcases h with ⟨rfl | rfl, h5⟩
        · exact Or.inl ⟨rfl, h5⟩
        · exact Or.inr (Or.inl ⟨rfl, h5⟩)) hP1) G hnab K z S .POmegaPlus nY hrow
      ⟨Or.inl rfl, h5⟩ hshape T hT clsT e D hcard i horth
  · exact twinYRankOn_even hp2 hq
      (twinYP1On_mono (fun t n h => by
        rcases h with ⟨rfl | rfl, h5⟩
        · exact Or.inl ⟨rfl, h5⟩
        · exact Or.inr (Or.inl ⟨rfl, h5⟩)) hP1) G hnab K z S .POmegaMinus nY hrow
      ⟨Or.inr rfl, h5⟩ hshape T hT clsT e D hcard i horth
  · exact twinYRankOn_odd hp2 hq
      (twinYP1On_mono (fun t n h => Or.inr (Or.inr h)) hP1) G hnab K z S .POmegaOdd nY hrow
      ⟨rfl, h4⟩ hshape T hT clsT e D hcard i horth

end Large

end CFSG.ClassicalInvolution.RouteD.TWY
