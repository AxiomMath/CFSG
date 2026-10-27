module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftedData
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftGroup
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlockCommute

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi
open scoped commutatorElement


theorem hBA_twistedA {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : 3 ≤ r) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥)
    (U : Subgroup Y) (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hUD : U ≤ Subgroup.centralizer (D : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) := by
  obtain ⟨r', ε, K, hF, hFin, hchar, hε, hr1, hn4, hcard, hf, ρ, e', S₀, Dt, d, hρs, hρe, hρc,
    hNJ, hJ, hDtJ, hDt, hdD, hds, hd3, hfree, hcyc, hrank, hfix⟩ :=
    exists_lifted_data hcomp hodd hpar hne r hr q hv hd f hfq e hrank3 hcycY hDperf hDle hx hx3 hxC
      hfreeY
  obtain ⟨hf1, -⟩ := survivor_analysis hr1 hε hn4 hcard hf _ S₀ hNJ hJ Dt hDtJ hDt d hdD hds hd3
    hfree hcyc
  subst hf1
  have hK : Nat.card K = (2 ^ 1) ^ 2 := hcard
  have hcomm := hBA_core hr1 hε hn4 hK hf _ S₀ hNJ hJ Dt hDtJ hDt d hdD hds hd3 hfree hcyc hrank
    (liftGroup hK ρ U) (fun u hu => (mem_liftGroup_iff hK ρ U u).mp hu |>.1)
    (fun u hu => pow_eq_one_of_mem_liftGroup hn4 hK ρ e' hρe hρc hUL hU3 hu)
    (fun u hu y y' hy =>
      mem_liftGroup_real_mem_iff hUP
        (fun y => by rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]) hu y y' hy)
    (fun u hu x hx => real_commutes_scalar ρ hρc
      (fun v hv g hg => hfix v (hUL hv) (hUD hv) g hg) hu hx)
  intro a ha b hb
  obtain ⟨Aa, hAa, hra⟩ := exists_mem_liftGroup_real hn4 hK ρ e' hρe hUL hU3 a ha
  obtain ⟨Ab, hAb, hrb⟩ := exists_mem_liftGroup_real hn4 hK ρ e' hρe hUL hU3 b hb
  exact commutator_mem_centralizer_of_real hρs hAa hAb hra hrb (hcomm Aa hAa Ab hAb)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
