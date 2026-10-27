module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverModule

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.Sporadic.Fi22 CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

theorem card_ge_of_cover {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (hnt : Nontrivial W) {p₀ p₁ p₂ q₀ q₁ q₂ c ω n : MulAut W} {r : ℕ}
    (h : Fi22CoverStruct p₀ p₁ p₂ q₀ q₁ q₂ c ω n r) (hfix : ∀ w : W, ω w = w → w = 1) :
    2 ^ 54 ≤ Nat.card W := by
  by_cases hr : ω ^ r = 1
  · exact card_ge_of_exact hW h hr
  · exact card_ge_of_ne hW hnt h hr hfix

theorem fixed_eq_one_of_central {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {ω : MulAut W} (hcomm : ∀ g ∈ L, g * ω = ω * g) (hω1 : ω ≠ 1) :
    ∀ w : W, ω w = w → w = 1 := by
  have hU : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers ω), g u ∈ fixV (Subgroup.zpowers ω) := by
    intro g hg u hu
    rw [mem_fixV_zpowers] at hu ⊢
    have := congrArg (fun m : MulAut W => m u) (hcomm g hg)
    simp only [MulAut.mul_apply] at this
    rw [← this, hu]
  rcases hirr.2 _ hU with h0 | h1
  · intro w hw
    have : w ∈ fixV (Subgroup.zpowers ω) := mem_fixV_zpowers.2 hw
    rwa [h0, Subgroup.mem_bot] at this
  · exfalso
    apply hω1
    refine MulEquiv.ext fun w => ?_
    have : w ∈ fixV (Subgroup.zpowers ω) := by rw [h1]; trivial
    exact mem_fixV_zpowers.1 this

theorem noIrrFFOffenderCenterThree_Fi22_native :
    NoIrrFFOffenderCenterThree NativeSporadic.Fi22 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hZ hEN hE hel _
  have hker := ker_centerQuotientHom e
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD⟩ := fi22_coverData
  obtain ⟨P₀, P₁, P₂, Q₀, Q₁, Q₂, c, ω, N, r, hωK, hω1, hs⟩ := fi22_cover_struct
    (centerQuotientHom e) (centerQuotientHom_surjective e) hker.le (by rw [hker]; exact hZ) hD
  have hs' := hs.map L.subtype L.subtype_injective
  have hωc : ω ∈ Subgroup.center ↥L := by rw [← hker]; exact hωK
  have hfix := fixed_eq_one_of_central hirr (L := L) (ω := L.subtype ω) (fun g hg => by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hωc ⟨g, hg⟩)
      exact this)
    (fun h1 => hω1 (L.subtype_injective (by rw [h1, map_one])))
  have hb := card_ge_of_cover hW hirr.1 hs' hfix
  refine exclusion_of_card_lt_of_outer hW hq hirr hEN hE hel e
    (fun B _ _ => card_le_two_mul_inf_inner_of_index fi22_index_inner B) ?_
  rw [hZ, CFSG.Sporadic.Fi22.card_Fi22]
  exact lt_of_lt_of_le (by norm_num) hb

theorem fi22CenterThree :
    Fi22CenterThree :=
  noIrrFFOffenderCenterThree_transfer noIrrFFOffenderCenterThree_Fi22_native
    CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Fi22 :
    GF2NoFFSporadicFor .Fi22 :=
  gf2NoFFSporadicFor_Fi22_of_three fi22CenterThree

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
