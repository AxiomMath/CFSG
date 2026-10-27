module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutTowerLinearCover
public import CFSG.LieType.SeitzGeneration.ThreeIndepBlock
public import CFSG.LieType.SeitzGeneration.RankVacuity
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL2E

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial

theorem not_dvd_totient_of_lt {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d)
    (hd : d < 2 * p) : ¬ p ∣ Nat.totient d := by
  rintro ⟨c, hc⟩
  have hpos : 0 < Nat.totient d := Nat.totient_pos.2 hd0
  have hle : Nat.totient d ≤ d := Nat.totient_le d
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith [hp.two_le]
  subst hc1
  rw [mul_one] at hc
  rcases (show d ≤ 2 ∨ 2 < d by omega) with hd2 | hd2
  · have h1 : Nat.totient d = 1 := by interval_cases d <;> simp
    rw [h1] at hc
    exact hp.one_lt.ne hc
  · have heven := Nat.totient_even hd2
    rw [hc] at heven
    exact hp2 ((hp.even_iff).1 heven)

theorem p1OffCharAlmostSimpleNonNormalAt_A {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.A m q, hv⟩ := by
  refine p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 hpd hno => ?_
  have hp : p.Prime := Fact.out
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpℓ : p ≠ q.p := by simpa using hpd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hcardF' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcube : HasThreeIndep (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1))
      (GaloisField q.p q.exponent)) p → False := fun h => hno
    (exists_isElemAbelian_card_of_not_rankLE2 hp (not_rankLE2_of_mulEquiv
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv) hp h)).2
  have htower : ¬ p ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1)) →
      OutTowerAt (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group p ∨
        DetCoverAt (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group p :=
    fun h => Or.inl (outTowerAt_catA hm hv hp h)
  have hgcd0 : 0 < Nat.gcd (m + 1) (q.card - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd (m + 1) (q.card - 1) ≤ m + 1 := Nat.gcd_le_left _ (by omega)
  by_cases hq1 : p ∣ q.card - 1
  · by_cases hm4 : 4 ≤ m
    · exact absurd (exists_isElemAbelian_card_of_not_rankLE2 hp
        (not_rankLE2_linear hv hp hq1 hm4)).2 hno
    · exact htower (not_dvd_totient_of_lt hp hp2 hgcd0 (by omega))
  · by_cases hqn : q.card ^ (m + 1) ≡ 1 [MOD p]
    · set e := Nat.gcd (m + 1) (p - 1) with he
      have he1 : 1 ≤ e := Nat.gcd_pos_of_pos_left _ (by omega)
      have hep : e ≤ p - 1 := Nat.gcd_le_right _ (by omega)
      have hen : e ∣ m + 1 := Nat.gcd_dvd_left _ _
      by_cases h3e : 3 * e ≤ m + 1
      · exfalso
        apply hcube
        have hz : ((q.card : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff, TauCeti.PrimePower.card_def]
          intro hdvd
          exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hdvd))
        have h1 : ((q.card : ℕ) : ZMod p) ^ (m + 1) = 1 := by
          have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hqn
          push_cast at this
          exact this
        have h2 : ((q.card : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
        have h3 : ((q.card : ℕ) : ZMod p) ^ e = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
        have h4 : q.card ^ e ≡ 1 [MOD p] := by
          refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
          push_cast
          exact h3
        have hqpos : 0 < q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact pow_pos q.prime_p.pos _
        have hqe : p ∣ q.card ^ e - 1 :=
          (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hqpos)).1 h4.symm
        let σ : (Fin e × Fin 3) ⊕ Fin (m + 1 - 3 * e) ≃ Fin (m + 1) :=
          (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
            (finSumFinEquiv.trans (finCongr (by omega)))
        exact hasThreeIndep_psl_blocks σ he1 hp (by rwa [hcardF]) (by rwa [hcardF])
      · have hn2e : m + 1 ≤ 2 * e := by
          obtain ⟨t, ht⟩ := hen
          have ht2 : t ≤ 2 := by
            by_contra h
            push Not at h
            have : 3 * e ≤ e * t := by nlinarith
            omega
          rw [ht]
          nlinarith
        exact htower (not_dvd_totient_of_lt hp hp2 hgcd0 (by omega))
    · right
      have hpF : (p : GaloisField q.p q.exponent) ≠ 0 := by
        intro h0
        have := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h0
        exact hpℓ ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 this).symm
      exact (detCoverAt_projectiveSL (n := m + 1) (by omega) q.prime_p q.exponent_pos hcardF'
        hp2 hpF (by rwa [hcardF]) (by rwa [hcardF])).of_mulEquiv
          ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
            (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _))

theorem p1OffCharAlmostSimpleNonNormalAt_A_one
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.A 1 q, hv⟩ := by
  intro p _ Y _ _ Rb Y₀ hR _ K _ _ hnc hC _ _ _ hd hpd
  exfalso
  apply hnc
  have hp : p.Prime := Fact.out
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpℓ : p ≠ q.p := by simpa using hpd
  obtain ⟨e⟩ := nonempty_mulEquiv_of_centralizer_eq_bot hC (Classical.choice hd)
  let e' : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  set P := ((Rb : Subgroup Y) ⊓ K).subgroupOf K with hP
  have hPp : IsPGroup p P :=
    (Rb.isPGroup'.to_le inf_le_left).comap_of_injective K.subtype K.subtype_injective
  have hcyc : IsCyclic (P.map e'.toMonoidHom) :=
    CFSG.Quasithin.H13.NQCore.isCyclic_of_isPGroup_psl2 hpℓ hR.ne_two q.exponent_pos
      (hPp.map e'.toMonoidHom)
  have hcycP : IsCyclic P := isCyclic_of_surjective
    (P.equivMapOfInjective e'.toMonoidHom e'.injective).symm.toMonoidHom (MulEquiv.surjective _)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_right).toMonoidHom
    (MulEquiv.surjective _)

theorem p1OffCharAlmostSimpleNonNormalAt_A_all {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A m q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.A m q, hv⟩ := by
  have hm1 : 1 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
  · exact p1OffCharAlmostSimpleNonNormalAt_A_one hv
  · exact p1OffCharAlmostSimpleNonNormalAt_A hm hv

end CFSG.AGLEmbedding
