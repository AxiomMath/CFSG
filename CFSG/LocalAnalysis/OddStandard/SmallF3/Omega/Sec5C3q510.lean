module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB4
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sym59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 7 →
      ¬ ∃ h : G, h⁻¹ * t * h = t * z

@[expose] def Asc82Pocket510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 7 →
      (¬ ∃ h : G, h⁻¹ * t * h = t * z) → ∃ K : Subgroup G, Sl23PocketIn (⊤ : Subgroup G) z K

theorem asc82Fact510_of_inputs (cq : Asc82CorIIIq) (hs : Asc82Sym59) (hp : Asc82Pocket510) :
    Asc82Fact510 := by
  intro G _ _ t L S z r B A hR h7
  obtain ⟨K, hzK, hKle, hKsub, ⟨e⟩⟩ := hp G t L S z r B A hR h7 (hs G t L S z r B A hR h7)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    have := GaloisField.card 3 1 one_ne_zero
    simpa using this
  obtain ⟨eF⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hcard
  exact cq G t L hR.toSec5Ctx.toSec5Setting.toSec3SettingLB z K 3 1 hR.pocket.1 one_pos
    (Or.inl (by norm_num)) ⟨hzK, hKle, hKsub, ⟨e.trans eF.symm⟩⟩

end CFSG.OddStandard.SmallF3.Omega
