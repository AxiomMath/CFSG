module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Local.FixedLineCharacteristicChainPrimeFactors
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
import CFSG.FeitThompson.OddOrder.SigmaSylowTransporterFusion
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Foundations.CommutatorMonotone
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M E : Subgroup G}

theorem factorization_eq_of_coprime_relIndex (hp : p.Prime) (hEM : E ≤ M)
    (hHall : Nat.Coprime (Nat.card E) (E.relIndex M)) (hpE : p ∣ Nat.card E) :
    (Nat.card M).factorization p = (Nat.card E).factorization p := by
  have hprod := relIndex_mul_natCard hEM
  have hEne0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
  have hidxne : E.relIndex M ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact Nat.card_pos.ne' hprod.symm
  have hpidx : ¬ p ∣ E.relIndex M := fun h =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hHall ▸ Nat.dvd_gcd hpE h))
  rw [← hprod, Nat.factorization_mul hidxne hEne0]
  simp [Nat.factorization_eq_zero_of_not_dvd hpidx]

theorem exists_mem_map_conj_eq_of_le [Fact p.Prime] {P Q : Subgroup G} (hP : P ≤ E) (hQ : Q ≤ E)
    (hPcard : Nat.card P = p ^ (Nat.card E).factorization p)
    (hQcard : Nat.card Q = p ^ (Nat.card E).factorization p) :
    ∃ e ∈ E, P.map ((MulAut.conj e : MulAut G) : G →* G) = Q := by
  have hP' : Nat.card (P.subgroupOf E) = p ^ (Nat.card E).factorization p := by
    rw [← Subgroup.card_subtype E (P.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hP, hPcard]
  have hQ' : Nat.card (Q.subgroupOf E) = p ^ (Nat.card E).factorization p := by
    rw [← Subgroup.card_subtype E (Q.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hQ, hQcard]
  obtain ⟨m, hm⟩ := exists_conj_smul_eq (G := E) (p := p) hP' hQ'
  refine ⟨(m : G), m.2, ?_⟩
  rw [conj_smul_eq_map_conj] at hm
  have := congrArg (fun X : Subgroup E => X.map E.subtype) hm
  simpa [map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le hP,
    Subgroup.map_subgroupOf_eq_of_le hQ] using this

theorem coprime_relIndex_of_isHallPiSubgroup {π : Set ℕ} (hEM : E ≤ M)
    (hE : IsHallPiSubgroup π (E.subgroupOf M)) : Nat.Coprime (Nat.card E) (E.relIndex M) := by
  have h := hE.coprime_natCard_index
  rwa [natCard_subgroupOf_of_le' hEM, index_subgroupOf] at h

theorem normalizer_le_of_le_sigmaCore (hEbot : E ≠ ⊥) (hE : E ≤ sigmaCore M)
    (hHall : Nat.Coprime (Nat.card E) (E.relIndex M)) : normalizer (E : Set G) ≤ M := by
  have hEM : E ≤ M := hE.trans (sigmaCore_le M)
  obtain ⟨p, hp, hpE⟩ := Nat.exists_prime_and_dvd
    (show Nat.card E ≠ 1 from fun h => hEbot (Subgroup.card_eq_one.1 h))
  have : Fact p.Prime := ⟨hp⟩
  have hpσ : p ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p (Nat.mem_primeFactors.2
      ⟨hp, hpE.trans (Subgroup.card_dvd_of_le hE), Nat.card_pos.ne'⟩)
  have hfact : (Nat.card M).factorization p = (Nat.card E).factorization p :=
    factorization_eq_of_coprime_relIndex hp hEM hHall hpE
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p E))
  set P : Subgroup G := (S : Subgroup E).map E.subtype with hPdef
  have hPE : P ≤ E := Subgroup.map_subtype_le _
  have hPcardE : Nat.card P = p ^ (Nat.card E).factorization p := by
    rw [hPdef, Subgroup.card_subtype, S.card_eq_multiplicity]
  have hPcardM : Nat.card P = p ^ (Nat.card M).factorization p := by rw [hPcardE, hfact]
  have hPN : normalizer (P : Set G) ≤ M := by
    obtain ⟨-, Q, hQle, hQcard, hQN⟩ := (mem_sigmaPrimes_iff_exists_subgroup hp).1 hpσ
    exact normalizer_le_of_normalizer_le_of_card_eq hp hQle hQcard (hPE.trans hEM) hPcardM hQN
  intro g hg
  have hgE : E.map ((MulAut.conj g : MulAut G) : G →* G) = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  have hPgE : P.map ((MulAut.conj g : MulAut G) : G →* G) ≤ E := by
    rw [← hgE]; exact Subgroup.map_mono hPE
  have hPgcard : Nat.card (P.map ((MulAut.conj g : MulAut G) : G →* G))
      = p ^ (Nat.card E).factorization p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcardE]
  obtain ⟨e, heE, he⟩ := exists_mem_map_conj_eq_of_le hPgE hPE hPgcard hPcardE
  rw [map_conj_map_conj] at he
  have h1 : e * g ∈ M := hPN (Subgroup.mem_normalizer_iff_map_conj_eq.2 he)
  simpa using M.mul_mem (M.inv_mem (hEM heE)) h1

theorem normalizer_le_of_isHallPiSubgroup_of_le_sigmaCore {π : Set ℕ} (hEbot : E ≠ ⊥)
    (hE : E ≤ sigmaCore M) (hHall : IsHallPiSubgroup π (E.subgroupOf M)) :
    normalizer (E : Set G) ≤ M :=
  normalizer_le_of_le_sigmaCore hEbot hE
    (coprime_relIndex_of_isHallPiSubgroup (hE.trans (sigmaCore_le M)) hHall)

theorem normalizer_le_of_le_sigmaCore_of_isHallPiSubgroup_sigmaCore (hEbot : E ≠ ⊥)
    (hE : E ≤ sigmaCore M) (hHall : Nat.Coprime (Nat.card E) (E.relIndex M))
    (_hS : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M)) :
    normalizer (E : Set G) ≤ M :=
  normalizer_le_of_le_sigmaCore hEbot hE hHall

end

end CFSG.FeitThompson
