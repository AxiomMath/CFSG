module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.CentralExt.FieldFour

namespace CFSG.LieType.Steinberg.CentralExt.FieldTwo

variable {K : Type} [Field K] [Finite K]

theorem ker_eq_bot_of_injective {G A P : Type} [Group G] [Group A] [Group P] {p : ℕ}
    {θ : G →* A} (hθ : Function.Surjective θ) (hθi : Function.Injective θ)
    (htriv : ∀ (η : P →* A), Function.Surjective η → η.ker ≤ Subgroup.center P →
      IsPGroup p η.ker → η.ker = ⊥)
    (η : P →* G) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P)
    (h2 : IsPGroup p η.ker) : η.ker = ⊥ := by
  have hker : (θ.comp η).ker = η.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hθi (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
  rw [← hker]
  exact htriv _ (hθ.comp hη) (hker ▸ hC) (hker ▸ h2)

section E8

variable
  [CharP K 2]

theorem e8_two_exists_section (hK : Nat.card K = 2) (E : Type) [Group E] [Finite E]
    (π : E →* adjointGroup .E8 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  obtain ⟨-, ⟨O⟩, -, -⟩ := e8_conclusionB K
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun _ _ _ _ η hη hC' h2 => SimplyLacedCover.ker_eq_bot_of_adjointGroup_two
        (Or.inr (Or.inr rfl)) hK η hη hC' h2)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e8_isCTGroupDatum K)
      (e8_steinbergExtras K) (e8_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e8_two_hopfMultiplier (hK : Nat.card K = 2) :
    commutator (AdjointQuotient .E8 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e8_two_exists_section hK E π hπ hcen

end E8

section E6

theorem e6Isogeny_injective_two (hK : Nat.card K = 2) : Function.Injective (e6Isogeny K) := by
  have hZ : Subgroup.center ↥(e6Data_valid.minGroup K) = ⊥ := by
    have h1 := (MinusculeClosed.card_center_e6 K).1
    rw [hK] at h1
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)
  rw [← MonoidHom.ker_eq_bot_iff, e6Isogeny_ker_eq_center, hZ]

variable [CharP K 2]

theorem e6_two_exists_section (hK : Nat.card K = 2) (E : Type) [Group E] [Finite E]
    (π : E →* e6Data_valid.minGroup K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e6Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  have := finite_minGroup' (K := K) e6Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := e6_conclusionB K
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E6) O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC' h2 => ker_eq_bot_of_injective (e6Isogeny_surjective K)
        (e6Isogeny_injective_two hK) (fun η' hη' hC'' h2' =>
          SimplyLacedCover.ker_eq_bot_of_adjointGroup_two (Or.inl rfl) hK η' hη' hC'' h2')
        η hη hC' h2) E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e6Datum_isCTGroupDatum K)
      (e6Datum_steinbergExtras K) (e6_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e6_two_hopfMultiplier (hK : Nat.card K = 2) :
    commutator (AdjointQuotient .E6 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e6Isogeny K) (e6Isogeny_surjective K)
    e6Isogeny_ker_eq_center center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e6_two_exists_section hK E π hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e6 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E6

section E7

theorem e7Isogeny_injective_two (hK : Nat.card K = 2) : Function.Injective (e7Isogeny K) := by
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup K) = ⊥ := by
    have h1 := (MinusculeClosed.card_center_e7 K).1
    rw [hK] at h1
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)
  rw [← MonoidHom.ker_eq_bot_iff, e7Isogeny_ker_eq_center, hZ]

variable [CharP K 2]

theorem e7_two_exists_section (hK : Nat.card K = 2) (E : Type) [Group E] [Finite E]
    (π : E →* e7Data_valid.minGroup K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e7Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  have := finite_minGroup' (K := K) e7Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := e7_conclusionB K
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E7) O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC' h2 => ker_eq_bot_of_injective (e7Isogeny_surjective K)
        (e7Isogeny_injective_two hK) (fun η' hη' hC'' h2' =>
          SimplyLacedCover.ker_eq_bot_of_adjointGroup_two (Or.inr (Or.inl rfl)) hK η' hη' hC''
            h2')
        η hη hC' h2) E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e7Datum_isCTGroupDatum K)
      (e7Datum_steinbergExtras K) (e7_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e7_two_hopfMultiplier (hK : Nat.card K = 2) :
    commutator (AdjointQuotient .E7 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e7Isogeny K) (e7Isogeny_surjective K)
    e7Isogeny_ker_eq_center center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e7_two_exists_section hK E π hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e7 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E7

end CFSG.LieType.Steinberg.CentralExt.FieldTwo
