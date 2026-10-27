module

public import CFSG.LieType.OutStructureRankFreeFive
public import CFSG.LieType.OutStructureLinearSylowNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowFieldNormal
public import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem two_mul_add_one_le_of_prime_of_dvd_sub_one {p ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ.Prime) (h : p ∣ ℓ - 1) : 2 * p + 1 ≤ ℓ := by
  obtain ⟨k, hk⟩ := h
  have hℓ2 := hℓ.two_le
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · omega
    · have hℓeq : ℓ = p + 1 := by omega
      have heven : Even ℓ := by
        rw [hℓeq]
        exact (hp.odd_of_ne_two hp2).add_one
      have := hℓ.even_iff.mp heven
      omega
  · have : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk2
    omega

theorem two_mul_add_one_le_of_prime_dvd_gcd {p ℓ N m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ.Prime) (h : p ∣ ℓ - 1) (hN : N ≠ 0) (hd : ℓ ∣ Nat.gcd N m) : 2 * p + 1 ≤ N :=
  (two_mul_add_one_le_of_prime_of_dvd_sub_one hp hp2 hℓ h).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (hd.trans (Nat.gcd_dvd_left N m)))

@[expose] def OutFiveExceptional (K : Type) [Group K] (p : ℕ) : Prop :=
  (∃ N r f : ℕ, CFSG.Open.StatedClassicalModel K .PSL N r f ∧ 2 * p + 1 ≤ N ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ p ∣ ℓ - 1 ∧ ℓ ∣ Nat.gcd N (r ^ f - 1)) ∨
    ∃ N r f : ℕ, CFSG.Open.StatedClassicalModel K .PSU N r f ∧ 2 * p + 1 ≤ N ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ p ∣ ℓ - 1 ∧ ℓ ∣ Nat.gcd N (r ^ f + 1)

theorem I713ClauseFreeFive.sylow_normal {i : TauCeti.CFSGIndex} (h : I713ClauseFreeFive i)
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (he : Nonempty (K ≃* i.Group)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ S : Sylow p (Outer K), (S : Subgroup (Outer K)).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Outer K) := finite_outer K
  rcases h K hK hnab he p hp hp5 with hOut | ⟨F, hEnorm, hFcyc, -, hEindex, -⟩ | ⟨hp3, -, -⟩
  · exact sylow_normal_of_not_dvd hOut
  · let φ : MulAut K →* Outer K :=
      QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
    have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
    have hEq : (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).map φ =
        F.map φ := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcyc :
        IsCyclic ↥((CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).map φ) := by
      have : IsCyclic ↥F := hFcyc
      rw [hEq]
      exact isCyclic_of_surjective (φ.subgroupMap F) (φ.subgroupMap_surjective F)
    have hidx :
        ¬ p ∣ ((CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).map φ).index := by
      rw [Subgroup.index_map_eq _ hφsurj
        (by rw [QuotientGroup.ker_mk']; exact le_sup_left)]
      exact hEindex
    have : ((CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).map φ).Normal :=
      hEnorm.map φ hφsurj
    exact sylow_normal_of_normal_isCyclic_index _ hcyc hidx
  · omega

theorem sylow_normal_outer_five_or_exceptional
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ S : Sylow p (Outer K), (S : Subgroup (Outer K)).Normal) ∨ OutFiveExceptional K p := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hfree : ∀ {j : TauCeti.CFSGIndex}, I713ClauseFreeFive j → Nonempty (K ≃* j.Group) →
      (∀ S : Sylow p (Outer K), (S : Subgroup (Outer K)).Normal) ∨ OutFiveExceptional K p :=
    fun hj hej => Or.inl (hj.sylow_normal hK hnab hej hp hp5)
  obtain ⟨i, he⟩ := hcat
  cases i with
  | cyclic r hr => exact hfree (i713ClauseFree_cyclic r hr).toFive he
  | alternating n hn => exact hfree (i713ClauseFree_alternating n hn).toFive he
  | sporadic s => exact hfree (i713ClauseFree_sporadic s).toFive he
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A n q =>
      have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      by_cases h1 : n = 1
      · subst h1
        exact hfree (i713ClauseFreeFive_lie_A1 q hv) he
      obtain ⟨eK⟩ := he
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      by_cases hex : ∃ ℓ : ℕ, ℓ.Prime ∧ p ∣ ℓ - 1 ∧
          ℓ ∣ Nat.gcd (n + 1) (q.p ^ q.exponent - 1)
      · obtain ⟨ℓ, hℓ, hpℓ, hℓd⟩ := hex
        exact Or.inr (Or.inl ⟨n + 1, q.p, q.exponent,
          CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv eK,
          two_mul_add_one_le_of_prime_dvd_gcd hp hp2 hℓ hpℓ (by omega) hℓd, ℓ, hℓ, hpℓ, hℓd⟩)
      push Not at hex
      let Fq := GaloisField q.p q.exponent
      have hqcard : Nat.card Fq = q.p ^ q.exponent :=
        GaloisField.card q.p q.exponent q.exponent_pos.ne'
      let ePSL : (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group ≃* projectiveSL (n + 1) Fq :=
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) Fq)
      refine Or.inl (sylow_normal_outer_of_mulEquiv (eK.trans ePSL)
        (linear_outer_sylow_normal_of_not_dvd_sub_one (n + 1) Fq hp (by omega) ?_))
      intro ℓ hℓ hd hpd
      rw [hqcard] at hd
      exact hex ℓ hℓ hpd hd
    | twistedA n q =>
      have hn2 : 2 ≤ n := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      obtain ⟨eK⟩ := he
      have hst := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv eK
      by_cases hex : ∃ ℓ : ℕ, ℓ.Prime ∧ p ∣ ℓ - 1 ∧
          ℓ ∣ Nat.gcd (n + 1) (q.p ^ q.exponent + 1)
      · obtain ⟨ℓ, hℓ, hpℓ, hℓd⟩ := hex
        exact Or.inr (Or.inr ⟨n + 1, q.p, q.exponent, hst,
          two_mul_add_one_le_of_prime_dvd_gcd hp hp2 hℓ hpℓ (by omega) hℓd, ℓ, hℓ, hpℓ, hℓd⟩)
      push Not at hex
      obtain ⟨⟨hpq, hf, -, h32⟩, L, _, _, hL, ⟨eL⟩⟩ := hst
      let hU : UnitaryFieldData q.p q.exponent L :=
        ⟨hpq, hf, by rw [hL, ← pow_mul, mul_comm]⟩
      have hq : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
        rintro ⟨h1, h2⟩
        exact h32 (by rw [h1, h2])
      let eC : K ≃* primeFormP hU
          ((1 : GL (Fin (n + 1)) L) : Matrix (Fin (n + 1)) (Fin (n + 1)) L) :=
        eL.trans ((Classical.choice (nonempty_primeFormP_mulEquiv hU isPrimeFormGram_one)).trans
          (unitaryPSUEquiv hU (by omega))).symm
      exact Or.inl (sylow_normal_outer_of_mulEquiv eC
        (unitary_outer_sylow_normal_of_not_dvd_sub_one hU (by omega) hq hp
          (fun ℓ hℓ hd hpd => hex ℓ hℓ hpd hd)))
    | B n q =>
      have hn2 : 2 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      by_cases h2 : n = 2
      · subst h2
        exact hfree (i713ClauseFree_lie_B2 q hv).toFive he
      by_cases hq2 : q.p = 2
      · exact hfree (i713ClauseFree_lie_B_even n q hv hq2 (by omega)).toFive he
      · exact hfree (i713ClauseFreeFive_lie_B_odd n q hv hq2 (by omega)) he
    | C n q => exact hfree (i713ClauseFree_lie_C n q hv).toFive he
    | D n q => exact hfree (i713ClauseFreeFive_lie_D n q hv) he
    | twistedD n q => exact hfree (i713ClauseFreeFive_lie_twistedD n q hv) he
    | E6 q => exact hfree (i713ClauseFreeFive_lie_E6 q hv) he
    | E7 q => exact hfree (i713ClauseFree_lie_E7 q hv).toFive he
    | E8 q => exact hfree (i713ClauseFree_lie_E8 q hv).toFive he
    | F4 q => exact hfree (i713ClauseFree_lie_F4 q hv).toFive he
    | G2 q => exact hfree (i713ClauseFree_lie_G2 q hv).toFive he
    | twistedE6 q => exact hfree (i713ClauseFreeFive_lie_twistedE6 q hv) he
    | trialityD4 q => exact hfree (i713ClauseFree_lie_trialityD4 q hv).toFive he
    | suzuki m => exact hfree (i713ClauseFree_lie_twistedB2 m hv).toFive he
    | reeG2 m => exact hfree (i713ClauseFree_lie_twistedG2 m hv).toFive he
    | reeF4 m => exact hfree (i713ClauseFree_lie_twistedF4 m hv).toFive he
    | tits => exact hfree (i713ClauseFree_lie_Tits hv).toFive he

end CFSG.LieType.OutStructure
