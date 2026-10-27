module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Foundations.SylowExistencePrimePower
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M T : Subgroup G}

theorem inf_eq_bot_of_isPiSubgroup {π ρ : Set ℕ} {A B : Subgroup G} (hA : IsPiSubgroup π A)
    (hB : IsPiSubgroup ρ B) (h : π ∩ ρ = ∅) : A ⊓ B = ⊥ := by
  have h1 := isPiSubgroup_iff.1 (hA.of_le (inf_le_left : A ⊓ B ≤ A))
  have h2 := isPiSubgroup_iff.1 (hB.of_le (inf_le_right : A ⊓ B ≤ B))
  have hempty : (Nat.card ↥(A ⊓ B)).primeFactors = ∅ := by
    ext q
    simp only [Finset.notMem_empty, iff_false]
    intro hq
    exact Set.eq_empty_iff_forall_notMem.1 h q ⟨h1 q hq, h2 q hq⟩
  rcases Nat.primeFactors_eq_empty.1 hempty with hc | hc
  · exact absurd hc Nat.card_pos.ne'
  · exact Subgroup.card_eq_one.1 hc

theorem exists_normalizer_eq_of_mem_sigmaPrimes_of_isNilpotent [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hnil : Group.IsNilpotent ↥(sigmaCore M)) (hp : p ∈ sigmaPrimes M) :
    ∃ P : Subgroup G, Nat.card ↥P = p ^ (Nat.card G).factorization p ∧
      normalizer (P : Set G) = M := by
  have hpp := prime_of_mem_sigmaPrimes hp
  have : Fact p.Prime := ⟨hpp⟩
  set N := sigmaCore M with hN
  have hHall : IsHallSubgroup (sigmaPrimes M) N := isHallSubgroup_sigmaCore hna hodd hsolv hM
  have hidx : ¬ p ∣ N.index := fun hd =>
    (isPiNumber_compl_iff.1 hHall.index) p
      (Nat.mem_primeFactors.2 ⟨hpp, hd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hfac : (Nat.card ↥N).factorization p = (Nat.card G).factorization p := by
    have hmul := N.card_mul_index
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  let S : Sylow p ↥N := default
  have hchar : (S : Subgroup ↥N).Characteristic := sylow_characteristic_of_isNilpotent S
  set P : Subgroup G := Subgroup.map N.subtype (S : Subgroup ↥N) with hPdef
  have hPcard : Nat.card ↥P = p ^ (Nat.card G).factorization p := by
    rw [hPdef, Subgroup.card_subtype, S.card_eq_multiplicity, hfac]
  refine ⟨P, hPcard, ?_⟩
  have hMP : M ≤ normalizer (P : Set G) :=
    le_normalizer_map_subtype_of_characteristic (S : Subgroup ↥N) (le_normalizer_sigmaCore M)
  have hpG : p ∣ Nat.card G :=
    (dvd_natCard_of_mem_sigmaPrimes hp).trans M.card_subgroup_dvd_card
  have hPbot : ⊥ < P := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact absurd hPcard.symm
      (Nat.one_lt_pow (hpp.factorization_pos_of_dvd Nat.card_pos.ne' hpG).ne' hpp.one_lt).ne'
  have hPtop : P < ⊤ := lt_of_le_of_lt
    ((Subgroup.map_subtype_le _).trans (sigmaCore_le M)) (lt_top_iff_ne_top.2 hM.1)
  have hlt : normalizer (P : Set G) < ⊤ := normalizer_lt_top_of_isSimpleGroup hPbot hPtop
  rcases eq_or_lt_of_le hMP with h | h
  · exact h.symm
  · exact absurd (hM.2 _ h) (lt_top_iff_ne_top.1 hlt)

theorem notMem_sigmaPrimes_of_mem_sigmaPrimes_of_isNilpotent [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) (hnil : Group.IsNilpotent ↥(sigmaCore M))
    (hp : p ∈ sigmaPrimes M) : p ∉ sigmaPrimes T := by
  intro hpT
  have hpp := prime_of_mem_sigmaPrimes hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨P, hPcard, hPN⟩ :=
    exists_normalizer_eq_of_mem_sigmaPrimes_of_isNilpotent hna hodd hsolv hM hnil hp
  obtain ⟨-, Q, hQT, hQcard, hQN⟩ := (mem_sigmaPrimes_iff_exists_subgroup hpp).1 hpT
  have hQG : Nat.card ↥Q = p ^ (Nat.card G).factorization p :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hpT hQT hQcard
  obtain ⟨g, hg⟩ := exists_conj_smul_eq hPcard hQG
  have h1 : normalizer ((MulAut.conj g • P : Subgroup G) : Set G)
      = MulAut.conj g • normalizer (P : Set G) := normalizer_map_conj P g
  rw [hg, hPN] at h1
  have hnorm : MulAut.conj g • M ≤ T := h1 ▸ hQN
  rcases eq_or_lt_of_le hnorm with h | h
  · exact hMT g h
  · exact hT.1 ((isCoatom_conj_smul hM g).2 T h)

theorem sigmaPrimes_inter_eq_empty_of_isNilpotent [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    sigmaPrimes M ∩ sigmaPrimes T = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hq =>
    notMem_sigmaPrimes_of_mem_sigmaPrimes_of_isNilpotent hna hodd hsolv hM hT hMT hnil hq.1 hq.2

theorem sigmaCore_inf_eq_bot_of_isNilpotent [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    sigmaCore M ⊓ sigmaCore T = ⊥ :=
  inf_eq_bot_of_isPiSubgroup (isPiSubgroup_sigmaCore M) (isPiSubgroup_sigmaCore T)
    (sigmaPrimes_inter_eq_empty_of_isNilpotent hna hodd hsolv hM hT hMT hnil)

theorem FTS_nilpotent_sigma_prime_separation :
    Statements.FTS_nilpotent_sigma_prime_separation.{u} := by
  intro G _ _ hG M T hM hT hMT hnil
  have := hG.isSimpleGroup
  have hMT' : ∀ g : G, MulAut.conj g • M ≠ T := fun g h =>
    hMT g⁻¹ (by rw [← h]; simp [Prep08.conjSubgroup])
  exact ⟨sigmaPrimes_inter_eq_empty_of_isNilpotent hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hT hMT' hnil,
    sigmaCore_inf_eq_bot_of_isNilpotent hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hT hMT' hnil⟩

end

end CFSG.FeitThompson.Proofs
