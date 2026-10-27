module

public import CFSG.Alternating.Multipliers.SpinCover
public import CFSG.Alternating.Multipliers.Small
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.Certificates.CentralizerFinite
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs

public noncomputable section

namespace CFSG.Alternating.Multipliers

open Subgroup CFSG.RankThree.PerfectCover CFSG.LocalAnalysis.ComponentInitial

section Finite

variable {S : Type} [Group S] [Group.IsPerfect S]

theorem card_hopfCover : Nat.card (HopfCover S) = Nat.card S * Nat.card (hopfMultiplier S) := by
  rw [(hopfMultiplier S).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hopfCoverMap_surjective).toEquiv]

theorem finite_hopfCover [Finite S] : Finite (HopfCover S) := by
  have hM : (hopfMultiplier S).FiniteIndex := Subgroup.finiteIndex_ker _
  have : (center (HopfCover S)).FiniteIndex := Subgroup.finiteIndex_of_le hopfMultiplier_le_center
  have := CFSG.Certificates.finite_commutatorSet_of_finiteIndex_center (G := HopfCover S)
  have hc : Finite (commutator (HopfCover S)) := inferInstance
  have : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect
  have htop : commutator (HopfCover S) = ⊤ := Group.IsPerfect.commutator_eq_top
  exact Finite.of_surjective (commutator (HopfCover S)).subtype fun x =>
    ⟨⟨x, htop ▸ mem_top x⟩, rfl⟩

end Finite

theorem isPGroup_two_hopfMultiplier {n : ℕ} (hn : 8 ≤ n) :
    IsPGroup 2 (hopfMultiplier (alternatingGroup (Fin n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Group.IsPerfect (alternatingGroup (Fin (m + 2))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  have : Finite (HopfCover (alternatingGroup (Fin (m + 2)))) := finite_hopfCover
  have : Group.IsPerfect (HopfCover (alternatingGroup (Fin (m + 2)))) := hopfCover_isPerfect
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := alternatingGroup (Fin (m + 2))
  set M := hopfMultiplier S
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := Sylow.nonempty
  set T : Subgroup (HopfCover S) := (P : Subgroup M).map M.subtype
  have hTM : T ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : T.Normal := normal_of_le_center (hTM.trans hopfMultiplier_le_center)
  set η : HopfCover S ⧸ T →* S := QuotientGroup.lift T (hopfCoverMap S) hTM
  have hη : Function.Surjective η := by
    intro s
    obtain ⟨u, hu⟩ := hopfCoverMap_surjective s
    exact ⟨QuotientGroup.mk u, hu⟩
  have hηK : η.ker = M.map (QuotientGroup.mk' T) := QuotientGroup.ker_lift _ _ _
  have hcentral : η.ker ≤ center (HopfCover S ⧸ T) := by
    rw [hηK]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective T y
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hopfMultiplier_le_center hx) u]
  have h1 : Nat.card (HopfCover S) = Nat.card (HopfCover S ⧸ T) * Nat.card T :=
    T.card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (HopfCover S ⧸ T) = Nat.card S * Nat.card η.ker := by
    rw [η.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have h4 : Nat.card T = Nat.card P := Subgroup.card_map_of_injective M.subtype_injective
  set a := (Nat.card M).factorization 2 with ha
  have h5 : Nat.card P = 2 ^ a := Sylow.card_eq_multiplicity P
  have hM : Nat.card M = Nat.card η.ker * 2 ^ a := by
    have e := card_hopfCover.symm.trans h1
    rw [h2, h4, h5, mul_assoc] at e
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e
  have hodd : Odd (Nat.card η.ker) := by
    have hc := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := M)).ne'
    have e : Nat.card M / 2 ^ a = Nat.card η.ker := by
      rw [hM, Nat.mul_div_cancel _ (pow_pos two_pos _)]
    rw [e] at hc
    exact Nat.coprime_two_left.mp hc
  have hK1 := card_ker_eq_one_of_odd (by omega) η hη hcentral hodd
  rw [hK1, one_mul] at hM
  exact IsPGroup.of_card hM

theorem card_hopfMultiplier_alternatingGroup {n : ℕ} (hn : 8 ≤ n) :
    Nat.card (hopfMultiplier (alternatingGroup (Fin n))) = 2 := by
  have : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  have : Finite (HopfCover (alternatingGroup (Fin n))) := finite_hopfCover
  have : Group.IsPerfect (HopfCover (alternatingGroup (Fin n))) := hopfCover_isPerfect
  have hle := alternating_perfect_central_two_kernel_order_at_most_two (by omega)
    (hopfCoverMap (alternatingGroup (Fin n))) hopfCoverMap_surjective hopfMultiplier_le_center
    (isPGroup_two_hopfMultiplier hn)
  have hlt : 1 < Nat.card (hopfMultiplier (alternatingGroup (Fin n))) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr (Spin.hopfMultiplier_ne_bot (by omega))
  exact le_antisymm hle hlt

theorem schurAlternatingMultiplierInput :
    CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput := by
  intro m hm
  rcases (by omega : m = 5 ∨ m = 6 ∨ m = 7 ∨ 8 ≤ m) with rfl | rfl | rfl | hm8
  · simpa using hopfMultiplier_alternatingGroup_five
  · simpa using hopfMultiplier_alternatingGroup_six
  · simpa using hopfMultiplier_alternatingGroup_seven
  · have h67 : ¬(m = 6 ∨ m = 7) := by omega
    rw [ite_eq_right h67]
    have hcard := card_hopfMultiplier_alternatingGroup hm8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨isCyclic_of_prime_card hcard, hcard⟩

end CFSG.Alternating.Multipliers
