module

public import CFSG.Quasithin.EmptyFaithful.R3c18F
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem two_le_pRank_three_largeRee_model
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨a, K, _, _, _, -, -, -, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
  have : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Finite (ModGL ReeTag.F4.tag (ZMod 2)) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (ModGL ReeTag.F4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hpow : ∀ (c : ZMod 2) (n : ℕ), c ^ 2 ^ n = c := by
    intro c n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have h0 : ∀ c : ZMod 2, ι (c ^ 2 ^ 0) = ι c ^ 2 ^ a := fun c => by
    rw [← map_pow, hpow, hpow]
  have h1 : ∀ c : ZMod 2, ι (c ^ 2 ^ (0 + 1)) = ι c ^ 2 ^ (a + 1) := fun c => by
    rw [← map_pow, hpow, hpow]
  have hΓ : ReeTag.F4.reeGamma (ZMod 2) 0 =
      (reeFixed ReeTag.F4 (ZMod 2) 0).map (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 (ZMod 2) 0)
  let ψ : commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0) →* ReeTag.F4.reeGamma (ZMod 2) 0 :=
    ((((adjointGroup ReeTag.F4.tag (ZMod 2)).subtype.comp
      (reeFixed ReeTag.F4 (ZMod 2) 0).subtype).comp
        (commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)).subtype).codRestrict _ fun g => by
      rw [hΓ]
      exact ⟨_, (g : ↥(reeFixed ReeTag.F4 (ZMod 2) 0)).2, rfl⟩)
  have hψ : Function.Injective ψ := fun g g' h => by
    have h' : (((g : ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) : adjointGroup ReeTag.F4.tag (ZMod 2)) :
        ModGL ReeTag.F4.tag (ZMod 2)) = (((g' : ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) :
          adjointGroup ReeTag.F4.tag (ZMod 2)) : ModGL ReeTag.F4.tag (ZMod 2)) :=
      congrArg (fun z : ↥(ReeTag.F4.reeGamma (ZMod 2) 0) => (z : ModGL ReeTag.F4.tag (ZMod 2))) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := ZMod 2) (Nat.card_zmod 2)
  have hT := Tables.Census.two_le_pRank_of_cubic_witness' Nat.prime_three hx hz hzx hzy
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact hT.trans (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
    ((CFSG.Quasithin.R3c18.reeGammaMap h0 h1).comp ψ)
    ((CFSG.Quasithin.R3c18.reeGammaMap_injective h0 h1).comp hψ))

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
