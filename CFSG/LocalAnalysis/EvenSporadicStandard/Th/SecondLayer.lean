module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommNormal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEnd

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Blueprint.NativeSporadic

structure SylowFacts {G : Type} [Group G] (L S B Aa : Subgroup G) : Prop where
  abelian_le : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
    IsPGroup 2 Y → (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8
  elementary_le : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
    (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7
  center_quotient : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

theorem ThCyc.not_sylow_le_normalizer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (F : SylowFacts L S B Aa) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hSP : S ⊔ zpowers t ≤ P) :
    ¬ P ≤ normalizer ((W5 A t : Subgroup G) : Set G) := by
  intro hPN
  obtain ⟨D, hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩ := H.exists_D W W2
  exact H.false_of_sylow_normalizer W W2 D hDC hDab hAaD hDsup hDdisj hDcard hDnorm hBpC
    F.abelian_le F.elementary_le F.center_quotient P hP hPidx hSP hPN

@[expose] def ThSecondLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G) (S A B Aa : Subgroup G) (z b : G),
    ThCyc G L R t → ThLocalIn L S A B z → ThLocalIn2 B A Aa b → SylowFacts L S B Aa →
    ∀ P : Subgroup G, IsPGroup 2 P → S ⊔ Bp A t ≤ P →
      ¬ P ≤ normalizer ((W5 A t : Subgroup G) : Set G) → False

end CFSG.EvenSporadicStandard.ThStd
