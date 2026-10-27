module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwReturn
public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwIsolated
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Chain

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem e6_card_eq_cross (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.E6.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hodd₂ : Odd (Nat.card F₂))
    (eY : Y ⧸ O ≃* SL(2, F₂)) : Nat.card F₂ = p ^ e := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  have hiso : ∀ r ∈ e6SignDiagramReps, UniqueIsolated (signMaskChar Tag.E6 r.mask) := by
    intro r hr
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact e6_uniqueIsolated_zero
    · exact e6_uniqueIsolated_twenty
    · exact e6_uniqueIsolated_two
  have hunt : ∀ r ∈ e6SignDiagramReps,
      UntwistAt (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))
        (signCharTuple (signMaskChar TwistTag.E6.tag r.mask)) := by
    intro r hr
    refine untwistAt_of_eq _ _ ?_
    have ha := signCharTuple_sign (k := k) (signMaskChar TwistTag.E6.tag r.mask)
    exact (exceptional_toral_centralizer_identity_component TwistTag.E6.tag k hk2 _ ha).2.2.2.2.1
      (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨r, hr, D, hDχ, hqD, -, J', O₀, hO₀, hA, hcard⟩ :=
    exists_datum_of_isPComponent_twist_cross p TwistTag.E6 hp hk he e6SignDiagramReps
      (r₀ := 2) symmetrizedCartan_perm_E6 h6.permChar_eq h6.exists_rep hunt
      (fun r hr => h6.theta r hr [] (nil_mem_omegaWords_e6 hr))
      (fun r hr => n6 r hr [] (nil_mem_omegaWords_e6 hr)) hx hx2 hL hLc φ₀ O hO hodd₂ eY
  have hd : orbitCard O₀ = 1 :=
    orbitCard_eq_one_of_uniqueIsolated D (by rw [hDχ]; exact hiso r hr) hO₀ hA
  rwa [hd, pow_one, hqD] at hcard

end Chain

variable {p f r e : ℕ} [Fact p.Prime] [Fact r.Prime]

theorem card_eq_of_isClassicalMember_twistedE6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hr2 : r ≠ 2)
    (he : 1 ≤ e) [Finite (twistedE6Group r e)] {L : Subgroup (twistedE6Group r e)}
    {z : twistedE6Group r e} (hL : IsClassicalMember p f L z) : p ^ f = r ^ e := by
  classical
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  set K0 := GaloisField r (2 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k r := charP_of_injective_algebraMap (algebraMap K0 k).injective r
  set F := frobTwistGL TwistTag.E6.tag k r e (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Φ := twistedE6Phi r e k with hΦ
  have hrange : Φ.range = ⁅R, R⁆ := range_twistedE6Phi r e hr2 he
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group r e) := ker_twistedE6Phi_le_center r e k
  have hΦR : ∀ y : twistedE6Group r e, Φ y ∈ R := twistedE6Phi_mem_fixedPointsIn r e hr2 he
  have hqs := isQuasisimple_twistedE6 r e he
  have hz : Φ z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center (twistedE6Group r e) := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := exists_two_involutions_fixedGroup (frobQ r e)
      (two_ne_zero_galoisField (2 * e) hr2)
    by_cases h : y₁ = z
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₂
        (fun h' => hne (h.trans h'.symm))
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₁ h
  let Φ' : twistedE6Group r e →* ↥⁅R, R⁆ :=
    Φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Finite ↥⁅R, R⁆ := Finite.of_surjective Φ' hΦ'surj
  have hker' : Φ'.ker ≤ Subgroup.center (twistedE6Group r e) := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hz' : Φ' z ≠ 1 := fun h1 => hz (congrArg Subtype.val h1)
  have hL' := isClassicalMember_map_central Φ' hΦ'surj hker' hodd hL hz'
  have hL'cent : L.map Φ' ≤ Subgroup.centralizer ({Φ' z} : Set ↥⁅R, R⁆) :=
    isSubnormal_le hL'.subnormal
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hP := isPComponent_two_of_isClassicalMember h4 hL'
  have hPM := isPComponent_inf_centralizer_of_isPComponent ⁅R, R⁆ (Φ' z) hL'cent hP
  set x : ModGL TwistTag.E6.tag k := Φ z with hx_def
  have hxR : x ∈ R := hΦR z
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two] at this
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, hz2, map_one]
  set L₁ : Subgroup (ModGL TwistTag.E6.tag k) := (L.map Φ').map (⁅R, R⁆).subtype with hL₁
  have hL₁Φ : L₁ = L.map Φ := by
    rw [hL₁, Subgroup.map_map]
    rfl
  have hL₁le : L₁ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hL'cent hy)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
  obtain ⟨eY⟩ := hL'.nonempty_equiv
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard := e6_card_eq_cross r hr2 (isAlgebraic_zmod_of_isAlgClosure r K0 k) he hxR hx2
    hL₁le hPM ((L.map Φ').equivMapOfInjective (⁅R, R⁆).subtype (⁅R, R⁆).subtype_injective)
    (classicalInvolutionOddCore (L.map Φ')) (CFSG.ComponentClassification.OddCore.odd_card _)
    hodd eY
  rwa [GaloisField.card p f hf0] at hcard

theorem classicalMemberParametersAt_twistedE6 : ClassicalMemberParametersAt p f .twistedE6 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .twistedE6 0 r e hr).K :=
    ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite (twistedE6Group r e) := hfin
  have hcard := card_eq_of_isClassicalMember_twistedE6 hp2 hq hr2 he (L := L) (z := z) hL
  have hcard' : Nat.card (GaloisField r e) = p ^ f := by
    rw [GaloisField.card r e (by omega)]
    exact hcard.symm
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard'
  exact ⟨rfl, Or.inl rfl⟩

end CFSG.ClassicalInvolution.Upgrade
