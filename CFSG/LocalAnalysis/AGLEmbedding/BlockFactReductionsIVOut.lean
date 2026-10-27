module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIOut

public section

namespace CFSG.AGLEmbedding

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_three_dvd_card_outer_of_psl_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) : ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨⟨-, -, hn, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by
    by_contra h3
    exact hn2 (by rw [show n = 2 by omega]; rfl)
  have e' : X ≃* LinearFlag.projectiveSL n K := e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hdvd := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two
    le_rfl hn3 hK
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  intro h3
  have := h3.trans hdvd
  norm_num at this

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
theorem three_dvd_of_three_dvd_card_outer_psu {X : Type} [Group X] {n p : ℕ}
    (h : StatedClassicalModel X .PSU n p 1) (h3 : 3 ∣ Nat.card (Outer X)) :
    3 ∣ Nat.gcd n (p + 1) := by
  obtain ⟨⟨hpp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p 1 K := ⟨hpp, hf, by rw [hK]; ring⟩
  have hq : ¬(n = 3 ∧ p ^ 1 = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h1 := (UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
    h1, mul_one, pow_one] at h3
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_three_dvd_card_outer_of_psp_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSp n 2 1) : ¬ 3 ∣ Nat.card (Outer X) := by
  have hdvd := (symplectic_model_outer_two_part_bound X n 2 1 h).2.1
  intro h3
  have := h3.trans hdvd
  norm_num at this

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_three_dvd_card_outer_of_psl_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hdvd := (linear_two_outer_order_divisor (p := 7) (f := 1) (by norm_num) F
    (by simpa using hcard)).2 X ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  intro h3
  have := h3.trans hdvd
  norm_num at this

section Orthogonal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

theorem card_outer_le_two_of_omegaPlus_two_of_five_le {T : Type} [Group T] {m : ℕ}
    (h : StatedClassicalModel T .POmegaPlus m 2 1) (hm5 : 5 ≤ m) :
    0 < Nat.card (Outer T) ∧ Nat.card (Outer T) ≤ 2 := by
  have h0 := h
  obtain ⟨⟨hp, -, hm⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) m 2 1 h K hK (quadPlus m K) (coe_quadPlus m K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) m 2 1 h) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus m K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinatePlusWitnessEquiv K e)).toEquiv
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus h K hK e).1
  have hidx : (matrixProjectiveImage (coordinateQuadPlus m K)).index = 1 := by
    rw [← hEA, horbit.2.2.2.2.1 hm5, Subgroup.index_top]
  have ha := relIndex_inner_dvd (coordinateQuadPlus m K)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus m K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadPlus m K) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadPlus m K)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (coordinateQuadPlus m K)).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadPlus m K)).range.relIndex
      (matrixProjectiveImage (coordinateQuadPlus m K)) = 1 := Nat.dvd_one.1 hc
  rw [hsq, Nat.dvd_one] at hb
  have hpos := Nat.card_pos (α := Outer (matrixProjectiveDerived (coordinateQuadPlus m K)))
  rw [hout, card_outer_eq, hb, hc', hidx, mul_one, mul_one, mul_one]
  rw [card_outer_eq, hb, hc', hidx, mul_one, mul_one, mul_one] at hpos
  have hA0 := Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadPlus m K)))
  exact ⟨hpos, (Nat.le_of_dvd hA0 ha).trans hA⟩

end Orthogonal

theorem three_dvd_card_outer_census {X : Type} [Group X]
    (h : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h3 : 3 ∣ Nat.card (Outer X)) :
    (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .D 4 q) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        (∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ 3 ∣ r + 1 ∧ d.1 = .twistedA r q) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hcard : ∀ {X' : Type} [Group X'] (e : X ≃* X'), 3 ∣ Nat.card (Outer X') := fun e => by
    rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  rcases h with ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · cases d with
    | A r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact absurd h3 (not_three_dvd_card_outer_of_psl_two h)
    | twistedA r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hp, hf] at h
      exact Or.inr ⟨⟨.twistedA r q, hv⟩, ⟨r, q, hd,
        (three_dvd_of_three_dvd_card_outer_psu h h3).trans (Nat.gcd_dvd_left _ _), rfl⟩, ⟨e⟩⟩
    | B r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hp, hf] at h
        exact absurd h3 (not_three_dvd_card_outer_of_psp_two h)
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
          (by omega) e
        rw [hp, hf] at h
        exact absurd h3 (not_three_dvd_card_outer_of_psp_two h)
    | C r q => exact hd.elim
    | D r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have hr : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
      · exact Or.inl ⟨⟨.D 4 q, hv⟩, ⟨q, hd, rfl⟩, ⟨e⟩⟩
      · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv
          (MulEquiv.refl _)
        rw [hp, hf] at hmod
        have h2 := card_outer_le_two_of_omegaPlus_two_of_five_le hmod h5
        have h3' := hcard e
        change 3 ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.D r q, hv⟩)) at h3'
        have := Nat.le_of_dvd h2.1 h3'
        omega
    | twistedD r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
        (MulEquiv.refl _)
      rw [hp, hf] at hmod
      have h2 := card_outer_le_two_of_omegaMinus_two hmod
      have h3' := hcard e
      change 3 ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩)) at h3'
      have := Nat.le_of_dvd h2.1 h3'
      omega
    | G2 q =>
      change q.card = 2 at hd
      have hq3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      omega
    | _ => exact hd.elim
  · exact absurd (hcard e) (not_dvd_card_outer_alternatingGroup n (by omega) 3 Nat.prime_three
      (by norm_num))
  · rcases hd with ⟨q, hq7, hd⟩ | ⟨q, hq3, hd⟩
    · simp only at hd
      subst hd
      obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq7
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp7, hf] at h
      exact absurd h3 (not_three_dvd_card_outer_of_psl_seven h)
    · simp only at hd
      subst hd
      obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq3
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp3, hf] at h
      have := three_dvd_of_three_dvd_card_outer_psu h h3
      norm_num at this

section Lift

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification

@[expose] def KFactUnitaryParabolicThreeRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    Nat.Coprime 3 (Nat.card (Subgroup.center Y)) → ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ 3 ∣ r + 1 ∧ d.1 = .twistedA r q) →
    Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
    J ≠ Subgroup.normalizer (T : Set Y) →
    (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
    IsMulCommutative ↥(CFSG.pCore 3 (↥J ⧸ primeComplementCore (G := ↥J) 3)) →
    Open.pRank 3 J ≤ 3 → ∀ E : Subgroup Y, E ≤ J → IsElemAbelian 3 E → Nat.card E ≠ 3 ^ 3

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_elemAbelian_fixed_of_centerQuotient
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center Y))) (α : MulAut Y)
    {E' : Subgroup (Y ⧸ Subgroup.center Y)} (hE' : IsElemAbelian 3 E')
    (hE'9 : Nat.card E' = 3 ^ 2)
    (hfix : ∀ x ∈ E', PerfectAutomorphisms.centerQuotientHom Y α x = x) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ x ∈ E, α x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (Subgroup.center Y)
  set H : Subgroup Y := E'.comap π
  set f : ↥H →* ↥E' := (π.comp H.subtype).codRestrict E' fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨⟨y, hx⟩, rfl⟩
  have hE'3 : IsPGroup 3 ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥H))
  have hQtop : (Q : Subgroup ↥H).map f = ⊤ := by
    rw [← Sylow.coe_mapSurjective hf Q]
    exact ((Q.mapSurjective hf).is_maximal' (hE'3.of_equiv Subgroup.topEquiv.symm)
      le_top).symm
  set E : Subgroup Y := (Q : Subgroup ↥H).map H.subtype
  have hE3 : IsPGroup 3 E := Q.isPGroup'.map _
  have hEZ : ∀ x ∈ E, π x = 1 → x = 1 := by
    intro x hx hπ
    have hxZ : x ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff x).mp hπ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE3) ⟨x, hx⟩
    have h1 : orderOf x ∣ Nat.card (Subgroup.center Y) := by
      rw [← Subgroup.orderOf_mk x hxZ]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at h1
    have h2 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hZ) h1
    exact orderOf_eq_one_iff.mp (hk.trans h2)
  set φ : ↥E →* Y ⧸ Subgroup.center Y := π.comp E.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (hEZ x x.2 hx))
  have hrange : φ.range = E' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : E.map π = ((Q : Subgroup ↥H).map f).map E'.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hQtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmem : ∀ x : ↥E, φ x ∈ E' := fun x => hrange ▸ ⟨x, rfl⟩
  refine ⟨E, ⟨⟨⟨fun a b => hφ ?_⟩⟩, fun x hx => ?_⟩, ?_, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE'.1.is_comm.comm ⟨φ a, hmem a⟩ ⟨φ b, hmem b⟩)
  · have h1 := hE'.2 (φ ⟨x, hx⟩) (hmem _)
    rw [← map_pow] at h1
    exact congrArg Subtype.val (hφ (h1.trans (map_one φ).symm))
  · rw [← hE'9, ← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  · have hx3 : x ^ 3 = 1 := by
      have h1 := hE'.2 (φ ⟨x, hx⟩) (hmem _)
      rw [← map_pow] at h1
      exact congrArg Subtype.val (hφ (h1.trans (map_one φ).symm))
    have hπ : π (α x) = π x := by
      rw [← PerfectAutomorphisms.onCenterQuotient_apply_mk]
      exact hfix _ (hmem ⟨x, hx⟩)
    set z := x⁻¹ * α x
    have hz : z ∈ Subgroup.center Y := by
      refine (QuotientGroup.eq_one_iff z).mp ?_
      change π (x⁻¹ * α x) = 1
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
    have hαx : α x = x * z := by simp [z]
    have hz3 : z ^ 3 = 1 := by
      have h1 : (α x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      have hc : Commute x z := Subgroup.mem_center_iff.mp hz x
      rw [hαx, hc.mul_pow, hx3, one_mul] at h1
      exact h1
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      have h2 : orderOf z ∣ Nat.card (Subgroup.center Y) := by
        rw [← Subgroup.orderOf_mk z hz]
        exact orderOf_dvd_natCard _
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hZ h1 h2)
    rw [hαx, hz1, mul_one]

end Lift

end CFSG.AGLEmbedding
