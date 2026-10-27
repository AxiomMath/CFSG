module

public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.FixPlaneGenUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCube

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
open CFSG.Open (IsElemAbelian)

theorem card_map_of_forall_eq_one {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (A : Subgroup G) (hA : ∀ x ∈ A, φ x = 1 → x = 1) : Nat.card (A.map φ) = Nat.card A := by
  have hinj : Function.Injective (φ.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hA x x.2 hx)
  rw [show A.map φ = (φ.comp A.subtype).range by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem exists_cube_twistedA {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 3 ≤ m) (hpq : p ∣ q.card + 1) (hq : q.card ≠ 2 ∨ 5 ≤ m) :
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group,
      IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  obtain ⟨-, -, hn3, hne, K, _, h, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _))
  have hcard : q.p ^ q.exponent = q.card := by rw [TauCeti.PrimePower.card_def]
  obtain ⟨A, hAa, hAc, hAs, -⟩ := exists_hyperGen_su h (n := m + 1) (by omega) hp hp2
    (by rw [hcard]; exact hpq) (by
      rcases hq with hq | hq
      · exact Or.inl (by rw [hcard]; exact hq)
      · exact Or.inr (by omega))
  let ψ : primeFormP h (idGram K (m + 1)) ≃* StatedProj (StatedSU (m + 1) (q.p ^ q.exponent) K) :=
    (Classical.choice (unitary_prime_form_full_semilinear_realization h
      (isPrimeFormGram_idGram (K := K) (n := m + 1)) hn3 hne).1).trans
        (unitaryPSUEquiv h (by omega))
  let π : unitarySU q.p q.exponent K (m + 1) →*
      StatedProj (StatedSU (m + 1) (q.p ^ q.exponent) K) :=
    QuotientGroup.mk'
      ((StatedScalars (Fin (m + 1)) K).subgroupOf (unitarySU q.p q.exponent K (m + 1)))
  refine ⟨((A.map π).map ψ.symm.toMonoidHom).map θ.symm.toMonoidHom,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _) _) _, ?_⟩
  rw [Subgroup.card_map_of_injective θ.symm.injective,
    Subgroup.card_map_of_injective ψ.symm.injective,
    card_map_of_forall_eq_one π A (fun x hx h1 => hAs x hx ((QuotientGroup.eq_one_iff x).1 h1)),
    hAc]

theorem kFactSeitzOuterCubeRankTwoAtPrime_twistedA {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ}
    [Fact p.Prime] (hex : ¬ (p = 3 ∧ m = 2 ∧ 3 ∣ q.card + 1)) :
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.twistedA m q, hv⟩ p := by
  have hp : p.Prime := Fact.out
  refine kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData fun hp2 hpd _ hno => ?_
  obtain ⟨-, -, hn3, hne, K, _, h, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _))
  have hpℓ : p ≠ q.p := by simpa using hpd
  have hcard : q.p ^ q.exponent = q.card := by rw [TauCeti.PrimePower.card_def]
  have hm2 : 2 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hcube : 3 ≤ m → p ∣ q.card + 1 → (q.card ≠ 2 ∨ 5 ≤ m) → False := fun hm hpq hq =>
    hno (exists_cube_twistedA hv hp hp2 hm hpq hq)
  have hg : ¬ p ∣ Nat.gcd (m + 1) (q.p ^ q.exponent + 1) := by
    intro hd
    rw [hcard] at hd
    have h1 := hd.trans (Nat.gcd_dvd_left _ _)
    have h2 := hd.trans (Nat.gcd_dvd_right _ _)
    rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
      exact hex ⟨hp3, rfl, hp3 ▸ h2⟩
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h1)))
    · refine hcube (by omega) h2 ?_
      by_cases hq2 : q.card = 2
      · right
        rw [hq2] at h2
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h2
        rw [hp3] at h1
        omega
      · exact Or.inl hq2
  have h8 : ¬ (p = 3 ∧ q.p ^ q.exponent = 8) := by
    rintro ⟨hp3, h8⟩
    rw [hcard] at h8
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · exact hex ⟨hp3, rfl, by rw [h8]; norm_num⟩
    · exact hcube hm3 (by rw [hp3, h8]; norm_num) (Or.inl (by rw [h8]; norm_num))
  have hpair : SubfieldPairSUOdd :=
    subfieldPairSUOdd
      CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
  exact ⟨(fieldAutData_primeFormP_odd hpair hn3 h hne hp hp2 hpℓ hg).of_mulEquiv θ hp,
    (fixPlaneGen_primeFormP h hn3 hne hp hp2 hpℓ hg h8).of_mulEquiv θ hp⟩

end CFSG.AGLEmbedding
