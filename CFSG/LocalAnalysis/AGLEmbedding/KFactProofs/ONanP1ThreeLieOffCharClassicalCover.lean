module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharInner
public import CFSG.LieType.SeitzGeneration.HyperCoverUnitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.RankThree.PartOne.K133B.NC5Cover
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def HyperExCoverUnitary : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (p : ℕ),
    p.Prime → p ≠ 2 → p ∣ q.card + 1 → 3 ≤ r → ¬ P1ThreeLieList p ⟨.twistedA r q, hv⟩ →
    ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
      Nonempty (K ⧸ Subgroup.center K ≃* Cat ⟨.twistedA r q, hv⟩) →
      ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ HyperGen p ⊤ E

@[expose] def P1OffCharCoverThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        ((∃ q, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) ∨ (∃ q, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1)) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        3 ≠ d.1.characteristic → 3 ∣ Nat.card (Subgroup.center K) →
        (∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
            E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
            E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) →
        P1ThreeLieList 3 d

theorem classical_cover_cases (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalIndex d.1)
    (e : K ⧸ Subgroup.center K ≃* Cat d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic) (hz : p ∣ Nat.card (Subgroup.center K)) :
    (∃ r q, d.1 = .A r q ∧ p ∣ r + 1 ∧ p ∣ q.card - 1) ∨
      (∃ r q, d.1 = .twistedA r q ∧ p ∣ r + 1 ∧ p ∣ q.card + 1) := by
  have hq' : CFSG.IsQuasisimple K :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hK
  obtain ⟨dd, hv⟩ := d
  have hchar3 : ∀ q : TauCeti.PrimePower, q.card = 3 → q.p = 3 := fun q hq =>
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne')
  by_cases h3 : p = 3
  · subst h3
    have hidx := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA ⟨dd, hv⟩ K
      ⟨hq', hz, ⟨e⟩⟩
    cases dd with
    | A r q => exact Or.inl ⟨r, q, rfl, hidx.1, hidx.2⟩
    | twistedA r q =>
      rcases hidx with hid | ⟨-, hq3⟩
      · exact Or.inr ⟨r, q, rfl, hid.1, hid.2⟩
      · exact (hpd (by rw [TauCeti.LieTypeIndex.characteristic_twistedA, hchar3 q hq3])).elim
    | B r q =>
      obtain ⟨-, hq3⟩ := hidx
      exact (hpd (by rw [TauCeti.LieTypeIndex.characteristic_B, hchar3 q hq3])).elim
    | _ => first | exact hidx.elim | exact (hd).elim
  · have hidx : CFSG.RankThree.PartOne.N143.PrimeCoverLieIndex p dd := by
      by_cases h5 : p = 5
      · subst h5
        exact CFSG.RankThree.PartOne.K133B.primeCoverLie_five hGA ⟨dd, hv⟩ hq' e hz
      · have h7 : 7 ≤ p := by
          have h2 := hp.two_le
          by_contra hlt
          have h4 : p ≠ 4 := by
            rintro rfl
            exact absurd hp (by norm_num)
          have h6 : p ≠ 6 := by
            rintro rfl
            exact absurd hp (by norm_num)
          omega
        exact CFSG.RankThree.PartOne.N143.primeCoverLie_of_griess hGA hp h7 ⟨dd, hv⟩ hq' e hz
    cases dd with
    | A r q => exact Or.inl ⟨r, q, rfl, hidx.1, hidx.2⟩
    | twistedA r q => exact Or.inr ⟨r, q, rfl, hidx.1, hidx.2⟩
    | _ => exact hidx.elim

theorem four_le_of_dvd_succ {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr1 : 1 ≤ r) (hr2 : r ≠ 2)
    (hpr : p ∣ r + 1) : 4 ≤ r := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hle : p ≤ r + 1 := Nat.le_of_dvd (by omega) hpr
  by_contra hlt
  have hr3 : r = 3 := by omega
  subst hr3
  have : p ≤ 4 := hle
  interval_cases p
  · omega
  · norm_num at hp

theorem p1OffCharClassicalCover_of (hGA : GriessMultipliersAllModels) (hU : HyperExCoverUnitary)
    (h3 : P1OffCharCoverThree) : P1OffCharClassicalCover := by
  intro p _ Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d hcl hd hpd hz hex
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨e⟩ := hd
  have hkill : ∀ E₁ : Subgroup K, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 3 →
      HyperGen p ⊤ E₁ → False := fun E₁ hE₁a hE₁c hgen₁ =>
    h.false_of_cube_of_le hKn (E₂ := E₁.map K.subtype) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁a K.subtype)
      ((Nat.card_congr
        (E₁.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm.trans hE₁c)
      (hyperGen_map_subtype hgen₁)
  rcases classical_cover_cases hGA hK.2.2 d hcl e hp hp2 hpd hz with
    ⟨r, q, hdr, hpr, hpq⟩ | ⟨r, q, hdr, hpr, hpq⟩
  · by_cases hr : r = 2
    · subst hr
      obtain rfl : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpr
      exact h3 Y Rb Y₀ h hcat K hK huniq hnc hcent d (Or.inl ⟨q, hdr, hpq⟩) ⟨e⟩ hpd hz hex
    · obtain ⟨dd, hv⟩ := d
      simp only at hdr
      subst hdr
      have hr1 : 1 ≤ r :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      obtain ⟨E₁, hE₁a, hE₁c, hgen₁⟩ := exists_hyperGen_cover_linear
        (four_le_of_dvd_succ hp hp2 hr1 hr hpr) q hv hp hp2 hpq hK.2.2 e
      exact (hkill E₁ hE₁a hE₁c hgen₁).elim
  · by_cases hr : r = 2
    · subst hr
      obtain rfl : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpr
      exact h3 Y Rb Y₀ h hcat K hK huniq hnc hcent d (Or.inr ⟨q, hdr, hpq⟩) ⟨e⟩ hpd hz hex
    · obtain ⟨dd, hv⟩ := d
      simp only at hdr
      subst hdr
      have hr2 : 2 ≤ r :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      by_contra hlist
      obtain ⟨E₁, hE₁a, hE₁c, hgen₁⟩ := hU r q hv p hp hp2 hpq (by omega) hlist K hK.2.2 ⟨e⟩
      exact hkill E₁ hE₁a hE₁c hgen₁

theorem hyperExCoverUnitary :
    HyperExCoverUnitary := by
  intro r q hv p hp hp2 hpq hr hlist K _ _ hK ⟨e⟩
  refine exists_hyperGen_cover_unitary hr q hv hp hp2 hpq ?_ hK e
  by_contra hcon
  have hq2 : q.card = 2 := by
    by_contra h
    exact hcon (Or.inl h)
  have hr5 : r < 5 := by
    by_contra h
    exact hcon (Or.inr (by omega))
  have hqpe : q.p = 2 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq2
    exact (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq2
  have hp3 : p = 3 := by
    rw [hq2] at hpq
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq
  subst hp3
  apply hlist
  interval_cases r
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, Or.inr ⟨rfl, hqpe.1, hqpe.2, rfl⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hqpe.1, hqpe.2,
      Or.inr (Or.inr (Or.inl rfl))⟩))))

section Cubes


theorem p1ThreeLieOffChar_of_cubesV7 (hX : ExcCubeResidualsV4) (hGA : GriessMultipliersAllModels)
    (hU : HyperExCoverUnitary) (h3 : P1OffCharCoverThree) (hRes : P1OffCharNoInnerCube) :
    P1ThreeLieOffChar :=
  p1ThreeLieOffChar_of_cubesV6 hX hGA (p1OffCharClassicalCover_of hGA hU h3) hRes

theorem p1ThreeLieOffChar_of_cubesV8 (hX : ExcCubeResidualsV4) (hGA : GriessMultipliersAllModels)
    (h3 : P1OffCharCoverThree) (hRes : P1OffCharNoInnerCube) : P1ThreeLieOffChar :=
  p1ThreeLieOffChar_of_cubesV7 hX hGA hyperExCoverUnitary h3 hRes

end Cubes

end CFSG.AGLEmbedding
