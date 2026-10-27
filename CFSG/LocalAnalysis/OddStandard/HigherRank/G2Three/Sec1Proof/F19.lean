module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LBase

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

set_option quotPrecheck false in
local notation "D1" => (t1G ()).tab
set_option quotPrecheck false in
local notation "I1" => idx1 (t1G ()).tab
set_option quotPrecheck false in
local notation "D5" => (t5G ()).tab
local notation "I5" => idx5

theorem G23LCtx.Y1_conj (X : G23LCtx m) :
    ∃ t ∈ g23T5 m, cen (frameOf m).B ⊔ closure {(frameOf m).h₀} = conjSub t (frameOf m).E :=
  X.f5.Y1_conj

theorem G23LCtx.Y2_conj (X : G23LCtx m) :
    ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂, (frameOf m).b₁ * (frameOf m).a₂,
      (frameOf m).z} = conjSub h (frameOf m).E := X.f1.Y2_conj

theorem G23LCtx.Y3_conj (X : G23LCtx m) :
    ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂,
      (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} =
        conjSub h (frameOf m).F := X.f1.Y3_conj

theorem G23LCtx.fact19 (X : G23LCtx m) (h11 : (frameOf m).Fact11 m.L)
    (h14 : (frameOf m).Fact14) : (frameOf m).Fact19 m.L := by
  obtain ⟨-, -, -, -, -, ⟨-, h6⟩, -⟩ := h14
  obtain ⟨t, ht, h1⟩ := X.Y1_conj
  obtain ⟨h, hh, h2⟩ := X.Y2_conj
  obtain ⟨h', hh', h3⟩ := X.Y3_conj
  exact fact19_of_witness h11.2.1 h6 ⟨t, g23T5_le m ht, Or.inl h1⟩ ⟨h, g23H_le m hh, Or.inl h2⟩
    ⟨h', g23H_le m hh', Or.inr h3⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
