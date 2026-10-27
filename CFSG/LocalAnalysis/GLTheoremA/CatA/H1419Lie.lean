module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Trans
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.PumpDefChar
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (IsL3Kind)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (PQ)

theorem l3u3_exists_L3Kind {X : Type} [Group X] (h : catalogIs X l3u3Index) :
    ∃ (H : Type) (_ : Group H), IsL3Kind 2 H ∧ Nonempty (H ⧸ Subgroup.center H ≃* X) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [l3u3Index, onLie] at hi
  | alternating _ _ => simp [l3u3Index, onLie] at hi
  | sporadic _ => simp [l3u3Index, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | A r q =>
      by_cases hr : r = 2
      · subst hr
        have hi' : q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4) := hi
        obtain ⟨hp2, hk⟩ := hi'
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        obtain ⟨j, hj⟩ : ∃ j, q.exponent = 2 * j := ⟨q.exponent / 2, by omega⟩
        have hchar : CharP (GaloisField q.p q.exponent) 2 := by
          rw [← hp2]
          infer_instance
        have hmod : Nat.card (GaloisField q.p q.exponent) % 3 = 1 := by
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2, hj, pow_mul, Nat.pow_mod]
          norm_num
        refine ⟨Matrix.SpecialLinearGroup (Fin 3) (GaloisField q.p q.exponent), inferInstance,
          Or.inl (Or.inl ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hchar, hmod,
            ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _⟩⟩), ⟨?_⟩⟩
        exact (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm.trans e.symm
      · simp [l3u3Index, onLie, hr] at hi
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        have hi' : q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5) := hi
        obtain ⟨hp2, hk⟩ := hi'
        have hv1 : 2 ≤ 2 ∧ (2 = 2 → 3 ≤ q.card) :=
          (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hq3 : 3 ≤ q.card := hv1.2 rfl
        have hq2 : q.card ≠ 2 := by omega
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        obtain ⟨j, hj⟩ : ∃ j, q.exponent = 2 * j + 1 := ⟨q.exponent / 2, by omega⟩
        haveI : Fintype (GaloisField q.p (2 * q.exponent)) := Fintype.ofFinite _
        have hcardK : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
          rw [GaloisField.card q.p (2 * q.exponent) (by omega), TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
        have hchar : CharP (GaloisField q.p (2 * q.exponent)) 2 := by
          rw [← hp2]
          infer_instance
        have hmod : q.card % 3 = 2 := by
          rw [TauCeti.PrimePower.card_def, hp2, hj, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        obtain ⟨q', hv', hp', hcard', ⟨eSU⟩⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
            (K := GaloisField q.p (2 * q.exponent)) (m := 3) (q := q.card)
            (by rw [← Nat.card_eq_fintype_card]; exact hcardK) (by norm_num)
            (fun h => hq2 (Prod.mk.inj h).2)
        have hringch : ringChar (GaloisField q.p (2 * q.exponent)) = 2 := ringChar.eq_iff.2 hchar
        have hq' : q' = q := by
          apply TauCeti.PrimePower.ext
          · rw [hp', hringch, hp2]
          · have h1 : q'.p ^ q'.exponent = q.p ^ q.exponent := by
              rw [← TauCeti.PrimePower.card_def, ← TauCeti.PrimePower.card_def]
              exact hcard'
            rw [hp', hringch, hp2] at h1
            exact Nat.pow_right_injective (le_refl 2) h1
        subst hq'
        refine ⟨↥(StatedSU 3 q'.card (GaloisField q'.p (2 * q'.exponent))), inferInstance,
          Or.inl (Or.inr ⟨GaloisField q'.p (2 * q'.exponent), inferInstance, inferInstance, q'.card, hchar,
            hcardK, hmod, hq2, ⟨MulEquiv.refl _⟩⟩), ⟨eSU.trans e.symm⟩⟩
      · simp [l3u3Index, onLie, hr] at hi
    | _ => simp [l3u3Index, onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.H1419

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA


theorem lie_holds : I1419UpLieOddFact := by
  intro Q _ _ β J hQ hCat _ hβ3 _ hJ hcat
  obtain ⟨β', J', hβ'3, hJ', ⟨eJ⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.H1419.transfer_pSimple β hβ3 hJ
  obtain ⟨i, hi, ⟨eS⟩⟩ := hCat
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie d =>
    have hi' : d.1.characteristic ≠ 2 := hi
    have hS : IsSimpleGroup (PQ Q ⧸ Subgroup.center (PQ Q)) := hQ.2
    have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQ Q) hQ
    have hD := CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar.kdChevDownQ_odd (p := 3) Nat.prime_three
      (by norm_num) d.1.characteristic
    have hchevS : IsChevSimple d.1.characteristic (PQ Q ⧸ Subgroup.center (PQ Q)) :=
      Or.inl ⟨.lie d, rfl, ⟨eS⟩⟩
    have hX := hD _ hS hna hchevS β' hβ'3 J' hJ'
    have hX' := chev_isChevSimple_of_mulEquiv eJ hX
    obtain ⟨H, hH, hL3, ⟨eH⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.H1419.l3u3_exists_L3Kind hcat
    have hchevH := chev_isChevSimple_of_mulEquiv eH hX'
    exact hi' (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.l3CharUnique_holds 2 _ H Nat.prime_two hL3 hchevH)

end CFSG.LocalAnalysis.GLTheoremA.K1419
end
