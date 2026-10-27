module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def TwistedE6RationalCatalogue :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
      rootDiagUnit Tag.E6 a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ∃ j : ℕ, 1 ≤ j ∧
          CatalogueOver (ringChar L) (S.D.q ^ j) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem compIdxAt_cat_twistedE6_of_rational
    (hres : TwistedE6RationalCatalogue) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) :
    CompIdxAt p (.twistedE6 q) (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  refine compIdxAt_of_mulEquiv eK.symm ?_
  intro β hβ hβp hβ1 J hJ
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
      hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβ
  obtain ⟨h, rfl⟩ := hmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
      q.exponent_pos hp hp2 hpq
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      q.prime_p hp hK hpq) (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    S hp ι hinj hrange _ hconj hT hap h1 hTame hJ
  obtain ⟨Fr, hFr, hFΦ⟩ := hΦ
  obtain ⟨j, hj, hcat⟩ := hres (AlgebraicClosure K) p₀ S
    ⟨Fr, fun c => by rw [hSq]; exact hFr c, hFΦ⟩ p hp hp2 a hT hap h1 i hqi
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  obtain ⟨i', ⟨φ⟩, hidx⟩ := hcat.of_mulEquiv eJ.symm
  have hℓL : ringChar (AlgebraicClosure K) = q.p := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
      (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
      (by rw [hK, ← pow_mul])
  refine ⟨i', ⟨φ⟩, compRelC_of_idxOver hj ?_⟩
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6, ← hℓL]
  have hfs : fieldSize (.twistedE6 q) = S.D.q := by
    rw [hSq]
    simp only [fieldSize, TauCeti.PrimePower.card_def]
  rw [hfs]
  exact hidx

theorem twistedE6CompIdx_of_rational
    (hres : TwistedE6RationalCatalogue) : TwistedE6CompIdx := by
  rintro ⟨e, hv⟩ p hp hp2 hpc ⟨q, rfl⟩
  exact compIdxAt_cat_twistedE6_of_rational hres q hv hp hp2 (by simpa using hpc)

theorem lieCompIdx_excTwisted_of_rational
    (hres : TwistedE6RationalCatalogue) : LieCompIdx isExcTwistedIdx :=
  lieCompIdx_excTwisted_of_twistedE6 (twistedE6CompIdx_of_rational hres)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
