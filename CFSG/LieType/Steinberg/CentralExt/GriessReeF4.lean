module

public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.LieType.Ree.LargeReeEightCentralTwoCover
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LieType.Multipliers.Tits
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier TauCeti

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem lieModel_of_reeF4 {X : Type} [Group X] (m : ℕ)
    (hv : (LieTypeIndex.reeF4 m).Valid) (e : X ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    1 ≤ m ∧ CFSG.Blueprint.LieModel X .twistedF4 0 2 (2 * m + 1) := by
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  refine ⟨hm1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, by omega,
    ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl, ⟨(ReeF4LieIndex.of m hv).1.fixedField,
      inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩))⟩

theorem reeF4_two_cover_trivial {J : Type} [Group J] [Finite J] {m : ℕ} (hm : 1 ≤ m)
    (hJ : CFSG.Blueprint.LieModel J .twistedF4 0 2 (2 * m + 1)) {P : Type} [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* J) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · exact (CFSG.LieType.Ree.large_Ree_field_eight_central_two_cover_trivial η hη hC h2 hJ).1
  · exact (CFSG.LieType.Ree.large_Ree_large_even_field_central_two_cover_trivial η hη hC h2
      (by omega) hJ).1

theorem reeF4_hopfMultiplier
    {X : Type} [Group X] {m : ℕ}
    (hm : 1 ≤ m) (hX : CFSG.Blueprint.LieModel X .twistedF4 0 2 (2 * m + 1)) :
    commutator X = ⊤ ∧ Subsingleton (CFSG.Open.griessHopfMultiplier X) := by
  have hR : ReeTitsModel X .twistedF4 2 (2 * m + 1) := by
    rcases hX with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hR
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model hR
  set Γ := CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K a
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect Γ := ⟨CFSG.LieType.Simplicity.commutator_reeFixed_F4 a ha hK⟩
  have hZ : Subgroup.center Γ = ⊥ := CFSG.SectionRank.reeFixed_F4_center_eq_bot a
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := FieldFour.hopfMultiplier_subsingleton hZ fun E _ _ π hπ hcen =>
    CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
      (fun E' _ _ π' hπ' hcen' hp' => FieldFour.exists_section_of_ker_eq_bot
        (fun P _ _ _ η hη hC h2 => FieldTwo.ker_eq_bot_of_injective (θ := e.symm.toMonoidHom)
          e.symm.surjective e.symm.injective
          (fun η' hη' hC' h2' => reeF4_two_cover_trivial hm hX η' hη' hC' h2') η hη hC h2)
        E' π' hπ' hcen' hp')
      (fun E' _ _ π' hπ' hcen' hc' =>
        CFSG.SectionRank.LargeRee.large_ree_section_of_suzuki
          CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK hπ' hcen'
          (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hc'))))
  have eΓ : Γ ⧸ Subgroup.center Γ ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e.symm
  obtain ⟨h1, h2⟩ := hM
  have : Group.IsPerfect (Γ ⧸ Subgroup.center Γ) := ⟨h1⟩
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := eΓ.toMonoidHom) eΓ.surjective
  exact ⟨Group.IsPerfect.commutator_eq_top,
    (griessHopfMultiplierCongr eΓ.symm).toEquiv.subsingleton⟩

variable {X : Type} [Group X] {n p f : ℕ}

theorem twistedF4_row
    (hmodel : CFSG.Models.LieModel X .twistedF4 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .twistedF4 n p f × exceptional .twistedF4 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | reeF4 m =>
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨hm, hX⟩ := lieModel_of_reeF4 m hv e
      refine row_of_subsingleton rfl ?_ (reeF4_hopfMultiplier hm hX)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem lieModel_of_tits (hv : LieTypeIndex.tits.Valid)
    (e : X ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) : CFSG.Blueprint.LieModel X .Tits 0 2 1 := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
    ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩))

theorem tits_row
    (hmodel : CFSG.Models.LieModel X .Tits n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .Tits n p f × exceptional .Tits n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | tits =>
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨hX, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_Tits X (lieModel_of_tits hv e)
      refine row_of_subsingleton rfl ?_ ⟨hX, eM.toEquiv.subsingleton⟩
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
