module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFixPlane
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCube

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial

theorem kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_oddA {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} [Fact p.Prime]
    (h : p ≠ 2 → p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
      (¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
        Nat.card E = p ^ 3) →
      FieldAutData (TauCeti.CFSGIndex.lie d).Group p ∧
        FixPlaneGen (TauCeti.CFSGIndex.lie d).Group p) :
    KFactSeitzOuterCubeRankTwoAtPrime d p := by
  intro hp2 Y _ _ K hKn hC he hpd hl hno E hE hc
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := he
  have : K.Normal := hKn
  have hnoC : ¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
      Nat.card E = p ^ 3 := by
    rintro ⟨E', hE', hc'⟩
    refine hno ⟨(E'.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE' _) _, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hc']
  obtain ⟨hF, hP⟩ := h hp2 hpd hl hnoC
  exact hyperGen_of_fieldAutData hC hno (hF.of_mulEquiv e hp) (hP.of_mulEquiv e hp) hE hc

theorem kFactSeitzOuterCubeRankTwoAtPrime_A_ge_two
    (hL4 : L4TwoPlanes) {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} [Fact p.Prime]
    (hexc : ¬ (m = 2 ∧ p = 3 ∧ 3 ∣ q.card - 1)) :
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.A m q, hv⟩ p := by
  refine kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_oddA fun hp2 hpd _ hno => ?_
  have hp : p.Prime := Fact.out
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p ≠ q.p := by simpa using hpd
  let e : Cat ⟨.A m q, hv⟩ ≃* LinearFlag.projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have : Finite (Cat ⟨.A m q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hno' : ¬ ∃ E : Subgroup (LinearFlag.projectiveSL (m + 1) (GaloisField q.p q.exponent)),
      IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
    rintro ⟨E, hE, hc⟩
    refine hno ⟨E.map e.symm.toMonoidHom,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hc]
  have hlift : ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1) := by
    rintro hl
    rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hl.2
      exact hexc ⟨rfl, hp3, hp3 ▸ hl.1⟩
    · have hm4 : 4 ≤ m := by
        by_contra hlt
        have h3 : m = 3 := by omega
        subst h3
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hl.2)))
      exact not_rankLE2_linear hv hp hl.1 hm4 (rankLE2_of_not_exists_cube hp hno)
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => hlift ⟨?_, ?_⟩
    · rw [← hcardF]
      exact hd.trans (Nat.gcd_dvd_right _ _)
    · exact hd.trans (Nat.gcd_dvd_left _ _)
  exact ⟨(fieldAutData_projectiveSL_of_cop (by omega) hp hp2 q.prime_p hpq q.exponent_pos hKq
      hcop).of_mulEquiv e hp,
    (fixPlaneGen_projectiveSL hL4 hm hp hp2 q.prime_p hpq q.exponent_pos hKq hcop
      hno').of_mulEquiv e hp⟩

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
