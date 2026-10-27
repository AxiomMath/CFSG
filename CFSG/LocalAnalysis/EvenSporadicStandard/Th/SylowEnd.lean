module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndEnd

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

theorem ThCyc.false_of_sylow_normalizer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (D : Subgroup G) (hDC : D ≤ Csub A Aa t)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hAaD : Aa ≤ D)
    (hDsup : D ⊔ zpowers t = Csub A Aa t) (hDdisj : Disjoint D (zpowers t))
    (hDcard : Nat.card D = 2 ^ 12)
    (hDnorm : ∀ n ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ x ∈ D, n * x * n⁻¹ ∈ D)
    (hBpC : ∀ r ∈ Bp A t, ∀ c ∈ Csub A Aa t, r * c * r⁻¹ * c⁻¹ ∈ Aa)
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hSP : S ⊔ zpowers t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) : False := by
  have hD : SylowEnd.DHyp A Aa t D :=
    ⟨hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩
  obtain ⟨g, hle, hu, hcard⟩ := H.exists_conj_card_eq W W2 hD hAb hZ hP hPidx hSP hPN
  exact H.false_of_card_eq W W2 hD hEl hle hu hcard

end CFSG.EvenSporadicStandard.ThStd
