module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2SpRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2ReeRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LiePL
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycAll
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExcTwisted

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Blueprint TauCeti
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (KD264InnGood)

section OutAbelian

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Ree CFSG.ComponentClassification.UnbalancedCatalog

theorem outAbelian_sp4 {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid) (hq2 : q.p = 2) :
    OutAbelianAt ⟨.B 2 q, hv⟩ := by
  have hM : LieModel (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group .PSp 2 2 q.exponent :=
    model_B lvCtx_holds hv hq2 (MulEquiv.refl _)
  obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) hM
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hm1 hK
  obtain ⟨-, -, -, -, hcyc, -⟩ := SpChain.exceptionalAut_structure hm1 hFr hord hzp
  exact commutator_le_inner_of_isCyclic (isCyclic_outer_of_mulEquiv e hcyc)

theorem outAbelian_g2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid) (hq2 : q.p = 2) :
    OutAbelianAt ⟨.G2 q, hv⟩ := by
  have hM : LieModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 2 q.exponent :=
    model_G2 lvCtx_holds hv hq2 (MulEquiv.refl _)
  obtain ⟨⟨-, hf1, -, h3⟩, hm⟩ := LieModel.chevalleyExceptionalModel hM (by decide)
  have hf2 : 2 ≤ q.exponent := by
    by_contra hlt
    have : q.exponent = 1 := by omega
    rw [this] at h3
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hK
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact commutator_le_inner_of_isCyclic
    (isCyclic_outer_of_mulEquiv e (isCyclic_outer_of_hom Θ hker))

theorem outAbelian_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) : OutAbelianAt ⟨.reeF4 m, hv⟩ := by
  have hM : LieModel (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group .twistedF4 0 2 (2 * m + 1) :=
    model_reeF4 lvCtx_holds hv (MulEquiv.refl _)
  obtain ⟨-, hR⟩ := LieModel.reeTitsModel hM (by decide)
  obtain ⟨hadm, a, hfa, hmodel⟩ := hR
  have hf3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hX := ReeTag.large_Ree_model_Schreier _ 2 (2 * m + 1) ⟨hadm, a, hfa, hmodel⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := 2 * m + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
  have : Finite (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := hX.1
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv _ E.toEquiv
  exact commutator_le_inner_of_isCyclic (isCyclic_outer_of_mulEquiv E hcyc)

end OutAbelian

theorem kDescFamRes_linear_of_res (hN3 : KD264InnGood) (hL : LinearRes) (p : ℕ) :
    KDescFamRes p fLinear :=
  kDescFamRes_linear_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264OutCyc_holds
    (KD264Lie.kd264OuterIdx_of_families KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary
        KD264Lie.lieOuterIdx_classicalBCD KD264Lie.lieOuterIdx_triality
        KD264Lie.lieOuterIdx_excUntwisted KD264Lie.lieOuterIdx_excTwisted) p
    (td4Ob_linear lvCtx_holds CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds p) hN3
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264PL_holds 3 Nat.prime_three (by norm_num)) hL

theorem kDescFamRes_unitary_of_res (hN3 : KD264InnGood) (hI5 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD264I5Low)
    (hU : UnitaryRes) (p : ℕ) : KDescFamRes p fUnitary :=
  kDescFamRes_unitary_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264OutCyc_holds
    (KD264Lie.kd264OuterIdx_of_families KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary
        KD264Lie.lieOuterIdx_classicalBCD KD264Lie.lieOuterIdx_triality
        KD264Lie.lieOuterIdx_excUntwisted KD264Lie.lieOuterIdx_excTwisted) p
    (td4Ob_unitary lvCtx_holds CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds p) hN3
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264PL_holds 3 Nat.prime_three (by norm_num))
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264LiftLow_holds hI5 Nat.prime_three (by norm_num)) hU

theorem kDescFamRes_symplectic_of_res (hS : SymplecticRes) (p : ℕ) : KDescFamRes p fSymplectic :=
  kDescFamRes_symplectic_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264OutCyc_holds
    (KD264Lie.kd264OuterIdx_of_families KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary
        KD264Lie.lieOuterIdx_classicalBCD KD264Lie.lieOuterIdx_triality
        KD264Lie.lieOuterIdx_excUntwisted KD264Lie.lieOuterIdx_excTwisted) p (td4Ob_symplectic lvCtx_holds p)
    (fun _ hv hq2 => outAbelian_sp4 hv hq2) hS

theorem symplecticRes_holds : SymplecticRes := symplecticRes_of_ctx lvCtx_holds

theorem kDescFamRes_symplectic_holds (p : ℕ) : KDescFamRes p fSymplectic :=
  kDescFamRes_symplectic_of_res symplecticRes_holds p

theorem kDescFamRes_g2_of_res (hG : G2Res) (p : ℕ) : KDescFamRes p fG2 :=
  kDescFamRes_g2_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264OutCyc_holds
    (KD264Lie.kd264OuterIdx_of_families KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary
        KD264Lie.lieOuterIdx_classicalBCD KD264Lie.lieOuterIdx_triality
        KD264Lie.lieOuterIdx_excUntwisted KD264Lie.lieOuterIdx_excTwisted) p (td4Ob_g2 lvCtx_holds p)
    (fun _ hv hq2 => outAbelian_g2 hv hq2) hG

theorem kDescFamRes_reeTits_of_res (hR : ReeTitsRes) (p : ℕ) : KDescFamRes p fReeTits :=
  kDescFamRes_reeTits_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kd264OutCyc_holds
    (KD264Lie.kd264OuterIdx_of_families KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary
        KD264Lie.lieOuterIdx_classicalBCD KD264Lie.lieOuterIdx_triality
        KD264Lie.lieOuterIdx_excUntwisted KD264Lie.lieOuterIdx_excTwisted) p (td4Ob_ree lvCtx_holds p)
    (fun _ hv => outAbelian_reeF4 hv) hR

theorem g2Res_holds : G2Res := g2Res_of_ctx lvCtx_holds

theorem kDescFamRes_g2_holds (p : ℕ) : KDescFamRes p fG2 :=
  kDescFamRes_g2_of_res g2Res_holds p

theorem reeTitsRes_holds : ReeTitsRes := reeTitsRes_of_ctx lvCtx_holds

theorem kDescFamRes_reeTits_holds (p : ℕ) : KDescFamRes p fReeTits :=
  kDescFamRes_reeTits_of_res reeTitsRes_holds p

theorem kDescFamRes_triD4_of_res (hT : TD4Alt) (p : ℕ) : KDescFamRes p fTriD4 :=
  kDescFamRes_triD4_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds hT p

end CFSG.LocalAnalysis.GLTheoremA.HDesc
