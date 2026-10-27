module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS4
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7HS3

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem twinSquareFact_proved : TwinSquareFact p := by
  intro t k e hadm hp2 hq htag R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 _ hc
  obtain ⟨c, hcZ, hcc⟩ := hc
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (T7H.psp2_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact Or.inl ⟨rfl, rfl, T7H.psl4_twin_sq hp2 hq R hR R' hR' hne hcomm x hx x' hx' hx2 hx1
      hx'2 hx'1 c hcZ hcc⟩
  · exact Or.inr ⟨rfl, rfl, T7H.psu4_twin_sq hp2 hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1
      hx'2 hx'1 c hcZ hcc⟩
  · exact (T7H.spinOdd_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact (T7H.spinPlus_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact (T7H.spinMinus_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim

namespace T7H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer AscE184Sect

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem layer_orth_six_proved (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : c * c = 1) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {K K' L : Subgroup G} {z t b b' : G}
    (hK : K ∈ tqMembers Ω c) (hK' : K' ∈ tqMembers Ω c) (hL : L ∈ tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : KPerp Ω K = {K, K'}) (hperp' : KPerp Ω K' = {K', K})
    (htL : IsUniqueInvolution L t) (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (exactCore c K)) (hR' : IsSylow2In R' (exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ exactCore c K) (hb' : b' ∈ exactCore c K') (ob : b * b = z) (ob' : b' * b' = z)
    (hrel : t = b * b' * c) :
    LayerOrthType p f Ω c 6 (piSign p f) :=
  layer_orth_six twinSquareFact_proved hp hq hΩ hBelow hc2 hnc hK hK' hL hz hz' hperp hperp' htL
    hzt htz hR hR' hRR' hb hb' ob ob' hrel

end T7H

theorem c23_4X_proved : C23_4X p f :=
  c23_4X_of_tsf twinSquareFact_proved

end CFSG.ClassicalInvolution.Asc77
