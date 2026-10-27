module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoToralCoords
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoReflectionFrame
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalFamilyKernel
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalA2Pair
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley

theorem exists_twE6ToralCoords_of_route_proved {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) :
    letI := (twE6CoverData hS hmark).fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3),
      TwE6ToralCoords (twE6CoverData hS hmark).lab.n (twE6CoverData hS hmark).hEN
        (twE6CoverData hS hmark).ψ κ :=
  exists_twE6ToralCoords_of_route_holds ggTwE6ThreeNbrRankInput_holds hcfg hX hS hmark

theorem exists_roots_ggHyperplane_of_ne_of_route_proved
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) (hne : r ≠ s) :
    letI := (twE6CoverData hS hmark).fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3),
      TwE6ToralCoords (twE6CoverData hS hmark).lab.n (twE6CoverData hS hmark).hEN
        (twE6CoverData hS hmark).ψ κ ∧
      ∃ α β : Fin 6 → ℤ, IsRoot .E6 α ∧ IsRoot .E6 β ∧
        (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
          ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
        (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
          ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
        β ≠ α ∧ β ≠ -α :=
  exists_roots_ggHyperplane_of_ne_of_route ggTwE6ThreeNbrRankInput_holds
    hcfg hX hS hmark hrA hr hsA hs hne

theorem ggPairConcl_of_large_twE6_member_of_route_proved
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 3 ≤ lab.n) 3 Bs X)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (hsA : s ∈ ggAutomizer X Bs) (hsC : s ∈ ggCoxRefl M e) (hne : r ≠ s) :
    GGPairConcl Bs X r s := by
  let D := twE6CoverData (fun _ h => h.1) hmark
  let := D.fieldK
  let := D.finiteK
  have : Fact (IsElemAbelian 3 Bs) := ⟨hcfg.1.1.2.1.2.1⟩
  have hr := ggCoxRefl_isReflection hpres.2 hrC
  have hs := ggCoxRefl_isReflection hpres.2 hsC
  obtain ⟨κ, hκ, α, β, hα, hβ, hHr, hHs, hβα, hβa⟩ :=
    exists_roots_ggHyperplane_of_ne_of_route_proved hcfg hX (fun _ h => h.1) hmark
      hrA hr hsA hs hne
  have hαnβ : α ≠ -β := by
    intro h
    exact hβa (by simpa only [neg_neg] using congrArg Neg.neg h.symm)
  exact D.original_pair_concl_of_root_positions D.hSlab.2 hκ hcfg.1.2.2.2.1
    r s hrA hr hsA hs α β hα hβ (Ne.symm hβα) hαnβ
    (hκ.act_eq_excRefl_of_ggHyperplane_iff hrA hr hα hHr)
    (hκ.act_eq_excRefl_of_ggHyperplane_iff hsA hs hβ hHs) hHr hHs

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
