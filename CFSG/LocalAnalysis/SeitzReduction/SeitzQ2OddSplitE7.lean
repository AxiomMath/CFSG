module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

section MinGroup


theorem e7_exists_section_of_coprime {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {E : Type} [Group E] [Finite E] {π : E →* e7Data_valid.minGroup k}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : e7Data_valid.minGroup k →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, -, -⟩ := e7_conclusionB k
  obtain ⟨C, -, hCO⟩ := e7Datum_commutatorFormula k _ (roots_eq isFiniteType_cartan_E7) O
  exact CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
    (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k) (e7_chevalleyExtras k O C hCO) E π
    hπ hcen hC

theorem oddCentralSplit_e7MinGroup (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddCentralSplit (e7Data_valid.minGroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E _ _ π hπ hcen hodd
  exact e7_exists_section_of_coprime hπ hcen (Nat.coprime_two_left.2 hodd)

end MinGroup

section Adjoint


theorem oddCentralSplit_adjointGroup_E7 (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddCentralSplit (adjointGroup .E7 K) :=
  (oddCentralSplit_e7MinGroup K).of_mulEquiv (E8Pilot.e7MinEquivAdjoint K)

theorem oddSchurTrivial_adjointGroup_E7_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddSchurTrivial (adjointGroup .E7 K) :=
  oddSchurTrivial_of_oddCentralSplit (oddCentralSplit_adjointGroup_E7 K)

theorem oddSchurTrivial_adjointGroup_E7_of_card {K : Type} [Field K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : OddSchurTrivial (adjointGroup .E7 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := charTwo_of_natCard_eq_two_pow hK
  exact oddSchurTrivial_adjointGroup_E7_of_charTwo K

theorem oddSchurTrivial_e7Levi (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddSchurTrivial (E8Pilot.e7Levi K) :=
  (oddSchurTrivial_adjointGroup_E7_of_charTwo K).of_mulEquiv (E8Pilot.e7LeviEquiv K).symm

theorem oddSchurTrivial_of_lieModel_E7 {X : Type} [Group X] {f : ℕ}
    (hX : LieModel X .E7 0 2 f) : OddSchurTrivial X := by
  rcases hX with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have hZ := center_adjointGroup_eq_bot (τ := .E7) (K := K)
    let e' : X ≃* adjointGroup .E7 K :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    exact (oddSchurTrivial_adjointGroup_E7_of_card hK).of_mulEquiv e'.symm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem e7_exists_section_of_central_of_four_le {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {E : Type} [Group E] [Finite E] {π : E →* e7Data_valid.minGroup F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) :
    ∃ σ : e7Data_valid.minGroup F →* E, ∀ g, π (σ g) = g := by
  rcases Nat.lt_or_ge (Nat.card F) 5 with h5 | h5
  · have hF4 : Nat.card F = 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      omega
    exact CFSG.LieType.Steinberg.CentralExt.FieldFour.e7_four_exists_section hF4 E π hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_exists_section_of_central h5 hπ
      hcen

theorem injective_of_surjective_of_le_center_E7_of_four_le {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : 4 ≤ Nat.card F) {P : Type} [Group P] [Finite P] [Group.IsPerfect P]
    (π : P →* adjointGroup .E7 F) (hπ : Function.Surjective π) (hker : π.ker ≤ center P) :
    Function.Injective π := by
  set ε : e7Data_valid.minGroup F ≃* adjointGroup .E7 F := E8Pilot.e7MinEquivAdjoint F with hε
  set π' : P →* e7Data_valid.minGroup F := ε.symm.toMonoidHom.comp π with hπ'def
  have hπ' : Function.Surjective π' := ε.symm.surjective.comp hπ
  have hker' : π'.ker = π.ker := by
    ext x
    simp only [hπ'def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨σ, hσ⟩ := e7_exists_section_of_central_of_four_le hF hπ' (hker' ▸ hker)
  have hinj := F4Pilot.injective_of_section_of_perfect π' (hker' ▸ hker) σ hσ
  intro a b hab
  apply hinj
  simp only [hπ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hab]

end Adjoint

end CFSG.SeitzReduction.SeitzQ2
