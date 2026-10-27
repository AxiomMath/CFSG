module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AltSixSevenAut
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.A7
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KFactAltSixSevenAutFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L U : Subgroup X) (p : ℕ), IsComponentOf L ⊤ →
    (Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 7))) →
    p.Prime → 5 ≤ p → U ≤ Subgroup.normalizer (L : Set X) → IsPGroup p U →
    (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ≤ p

@[expose] def CitedBlockAltNormalizerSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) → p.Prime → p ≠ 2 →
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ U : Subgroup G, U ≤ M ⊓ Subgroup.normalizer (S : Set G) →
      U ≤ Subgroup.normalizer (L : Set G) → IsPGroup p U →
      ∃ U₁ U₂ : Subgroup G, U₁ ≤ U ∧ U₂ ≤ U ∧ U₁ ⊓ U₂ ≤ blockCentralizer M L ∧
        U₁.relIndex U ≤ p ∧ U₂.relIndex U ≤ p ∧
        ∀ y ∈ M ⊓ Subgroup.normalizer (S : Set G), y ∈ Subgroup.normalizer (L : Set G) →
          y ∈ Subgroup.normalizer (U : Set G) →
          y ∈ Subgroup.normalizer (U₁ : Set G) ∧ y ∈ Subgroup.normalizer (U₂ : Set G)

namespace AltSixSevenAut

theorem not_pow_two_dvd {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n = 1440 ∨ n = 5040) :
    ¬ p ^ 2 ∣ n := by
  intro h
  have hle := Nat.le_of_dvd (by omega) h
  have hp71 : p ≤ 71 := by
    by_contra hc
    have h72 : 72 ≤ p := by omega
    have := Nat.pow_le_pow_left h72 2
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem relIndex_inf_centralizer_le_five {X : Type} [Group X] {L U : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hU : IsPGroup p U) {Q : Type} [Group Q]
    (ψ : ↥U →* MulAut Q) (hker : ∀ u : ↥U, ψ u = 1 → (u : X) ∈ Subgroup.centralizer (L : Set X))
    {n : ℕ} (hn : n = 1440 ∨ n = 5040) (hcard : Nat.card (MulAut Q) = n) :
    (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut Q) := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ∣ Nat.card ψ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le fun u hu => ⟨u.2, hker u hu⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := ψ.range)).1
    (hU.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
  have hk' : p ^ k ∣ n := hcard ▸ hk ▸ Subgroup.card_subgroup_dvd_card ψ.range
  have hk1 : k ≤ 1 := by
    by_contra h
    exact not_pow_two_dvd hp hp5 hn ((pow_dvd_pow p (not_le.1 h)).trans hk')
  rw [hk] at hdvd
  have := (Nat.le_of_dvd (pow_pos hp.pos k) hdvd).trans (Nat.pow_le_pow_right hp.pos hk1)
  simpa using this

end AltSixSevenAut

theorem kFactAltSixSevenAutFive :
    KFactAltSixSevenAutFive := by
  intro X _ _ L U p hL hLtype hp hp5 hUN hU
  obtain ⟨-, -, hperf, -⟩ := hL
  rcases hLtype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
    refine AltSixSevenAut.relIndex_inf_centralizer_le_five hp hp5 hU
      ((AltSixSevenAut.quotientCenterAut ↥L).comp
        (L.normalizerMonoidHom.comp (Subgroup.inclusion hUN))) ?_ (Or.inl rfl)
      (CFSG.GH74.KGroups.A6.card_mulAut e')
    exact fun u hu => AltSixSevenAut.mem_centralizer_of_quotientCenterAut_eq_one hperf
      (hUN u.2) hu
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A7.equiv_of_alt e
    refine AltSixSevenAut.relIndex_inf_centralizer_le_five hp hp5 hU
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hUN)) ?_ (Or.inr rfl)
      (CFSG.GH74.KGroups.A7.card_mulAut e')
    intro u hu
    have hmem : Subgroup.inclusion hUN u ∈ L.normalizerMonoidHom.ker := hu
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact hmem

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

theorem citedBlockAltNormalizer_of_sq (h : CitedBlockAltNormalizerSq) :
    CitedBlockAltNormalizer := by
  intro G _ _ M S L p hK hA hL hX1 hS h678 hp hp2 hJ U hUK hUL hUp
  obtain ⟨U₁, U₂, hU₁, hU₂, hU12, hi₁, hi₂, -⟩ :=
    h G M S L p hK hA hL hX1 hS h678 hp hp2 hJ U hUK hUL hUp
  have hle : U₁ ⊓ U₂ ≤ U ⊓ blockCentralizer M L := le_inf (inf_le_left.trans hU₁) hU12
  have hne : (U₁ ⊓ U₂).relIndex U ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (U ⊓ blockCentralizer M L).relIndex U ≤ (U₁ ⊓ U₂).relIndex U :=
        Subgroup.relIndex_le_of_le_left hle hne
    _ ≤ U₁.relIndex U * U₂.relIndex U := Subgroup.relIndex_inf_le
    _ ≤ p * p := Nat.mul_le_mul hi₁ hi₂
    _ = p ^ 2 := (sq p).symm

end CFSG.AGLEmbedding
