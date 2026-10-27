module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamExcUntw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

set_option linter.unusedSectionVars false


theorem censusBodyTwistedE6 : CensusBodyTwistedE6 := by
  intro q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpq : 3 ≠ q.p := by rw [hq2]; norm_num
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let β : MulAut ↥(twistedE6RootGroup K σ) := MulAut.congr eK η
  have hβmem : β ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eK).2 hmem
  have hβ3 : β ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr eK) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hη1
    exact (MulAut.congr eK).injective (by rw [map_one]; exact h1)
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
  have hmem' : β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβmem
  obtain ⟨h, hh⟩ := hmem'
  have hp1 : h ^ 3 = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
    (by rw [map_pow, hh, hβ3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [← hh, h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime q.prime_p q.exponent_pos hp3 (by norm_num) hpq
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp3
      (by norm_num)
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime q.prime_p q.exponent_pos hK σ hσ hp3 hpq hp₀ hp₀ℓ
      hq₀ hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  have hL3' : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp3 hK hpq
  have hconj' : ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
    intro c
    rw [← hh]
    exact hconj c
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup eK η
  have hJ' : ∀ {J : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group},
      IsComponentOf J (fixSubgroup η) → IsComponentOf (J.map eK.toMonoidHom) (fixSubgroup β) := by
    intro J hJ
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eK hJ
    exact hfix ▸ h1
  have hLT : ∀ {J : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group},
      IsTypeL2 (2 ^ r) ↥J → IsTypeL2 (2 ^ r) ↥(J.map eK.toMonoidHom) :=
    fun {J} h => p6_isTypeL2_of_equiv (J.equivMapOfInjective eK.toMonoidHom eK.injective) h
  have hq8 : 8 ≤ 2 ^ r := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨c, hc⟩ := hr; omega)
  exact exc_three_components_false (τ := .E6) (Or.inr (Or.inl rfl)) excKac_e6
    (by exact_mod_cast hL3') S ι hinj hrange hT hap h1 β hconj' hq8 (hJ' hJ₁) (hJ' hJ₂) (hJ' hJ₃)
    (fun h => h12 (Subgroup.map_injective eK.injective h))
    (fun h => h13 (Subgroup.map_injective eK.injective h))
    (fun h => h23 (Subgroup.map_injective eK.injective h))
    (hLT (isTypeL2_of_catalogIs_isL2n hr hL1)) (hLT (isTypeL2_of_catalogIs_isL2n hr hL2))
    (hLT (isTypeL2_of_catalogIs_isL2n hr hL3))

end CFSG.LocalAnalysis.GLTheoremA.T1428
