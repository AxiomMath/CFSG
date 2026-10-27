module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoProj
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalD4Eight
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Module CFSG CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.GroupTheory.WeirSylow

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem isLocallyBalancedAbs_three_one_matrix_two (hK : Nat.card K = 2) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K (Fin d → K) / 2)) (h5 : 5 ≤ d)
    (htop : matrixProjectiveImage Q = ⊤) :
    IsLocallyBalancedAbs 3 1 (matrixProjectiveDerived Q) := by
  classical
  have := charP_two hK
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived Q hd hQ hT
  set φ := coordBridge Q hd
  haveI : Finite (ProjOrthDerived Q) := Finite.of_surjective
    (QuotientGroup.mk : orthDerived Q → ProjOrthDerived Q) QuotientGroup.mk_surjective
  haveI : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ φ.symm.toEquiv
  refine isLocallyBalancedAbs_one_of_good Nat.prime_three hinj fun x hx3 hx1 => Or.inr ?_
  have hxE : x ∈ matrixProjectiveImage Q := by rw [htop]; exact Subgroup.mem_top x
  exact coreFreeAt_of_mem_matrixProjectiveImage hK hd hQ hT hpar h5
    (fun g _ => ⟨1, by rw [htop]; exact Subgroup.mem_top _⟩) hxE hx3 hx1

end Assembly

section Models

theorem isLocallyBalancedAbs_three_one_plus_two {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n 2 1) (hn : 6 ≤ n) (he : Even n) :
    IsLocallyBalancedAbs 3 1 G := by
  classical
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  refine IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv K e) ?_
  have hd : 0 < 2 * n := by omega
  have hpar : IsPlusType (coordinateQuadPlus n K) ↔ Even (finrank K (Fin (2 * n) → K) / 2) :=
    iff_of_true (CFSG.ComponentClassification.CatFC.omegaPlus_isPlusType n K)
      (by rw [Module.finrank_fin_fun, Nat.mul_div_cancel_left n (by norm_num)]; exact he)
  exact isLocallyBalancedAbs_three_one_matrix_two hK2 hd hnd hT hpar (by omega)
    (matrixProjectiveImage_eq_top_plus K n (by omega))

theorem isLocallyBalancedAbs_three_one_minus_two {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n 2 1) (hn : 5 ≤ n) (ho : ¬ Even n) :
    IsLocallyBalancedAbs 3 1 G := by
  classical
  have h0 := h
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  refine IsLocallyBalancedAbs.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e) ?_
  have hd : 0 < 2 * n := by omega
  have hminus :=
    CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus
      (K := K) n hn1 hirr
  have hpar : IsPlusType (coordinateQuadMinus n K hn1 b c) ↔
      Even (finrank K (Fin (2 * n) → K) / 2) :=
    iff_of_false hminus
      (by rw [Module.finrank_fin_fun, Nat.mul_div_cancel_left n (by norm_num)]; exact ho)
  exact isLocallyBalancedAbs_three_one_matrix_two hK2 hd hnd hT hpar (by omega)
    (matrixProjectiveImage_eq_top_minus K n (by omega) b c hirr)

theorem isLocallyBalancedAbs_three_one_catD_two (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D n q).Valid) (hn : 6 ≤ n) (he : Even n) (hp : q.p = 2)
    (hq : q.exponent = 1) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD n q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group)
  rw [hp, hq] at hm
  exact isLocallyBalancedAbs_three_one_plus_two hm hn he

theorem isLocallyBalancedAbs_three_one_cattwistedD_two (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) (hn : 5 ≤ n) (ho : ¬ Even n)
    (hp : q.p = 2) (hq : q.exponent = 1) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD n q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group)
  rw [hp, hq] at hm
  exact isLocallyBalancedAbs_three_one_minus_two hm hn ho

end Models

section D4

theorem isLocallyBalancedAbs_three_one_d4Two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    IsLocallyBalancedAbs 3 1 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  classical
  have := charP_two hK
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (n := 4) (K := K) (by norm_num)
  have hpar : IsPlusType (coordinateQuadPlus 4 K) ↔ Even (finrank K (Fin (2 * 4) → K) / 2) :=
    iff_of_true ((isPlusType_congr (coordinatePlusIsometry 4 K)).1 (isPlusType_quadPlus K 4))
      (by rw [Module.finrank_fin_fun]; decide)
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived _ hd hQ hT
  set φ := coordBridge (coordinateQuadPlus 4 K) hd
  refine isLocallyBalancedAbs_one_of_good Nat.prime_three hinj fun x hx3 hx1 => Or.inr ?_
  by_cases hxE : x ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)
  · have hE : ∀ g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
        Nat.Coprime 3 (orderOf g) → ∃ β : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
          MulAut.congr φ.symm (β⁻¹ * g * β) ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
      intro g hg
      obtain ⟨β₀, hβ₀⟩ := exists_conj_mem_matrixProjectiveImage_four
        (g := MulAut.congr φ.symm g) (by rwa [MulEquiv.orderOf_eq])
      refine ⟨MulAut.congr φ β₀, ?_⟩
      rwa [map_mul, map_mul, map_inv, congr_symm_congr]
    exact coreFreeAt_of_mem_matrixProjectiveImage hK hd hQ hT hpar (by norm_num) hE hxE hx3 hx1
  · exact d4TrialityCoreFree_holds K (by rw [hK]; decide) x hx3 hxE

theorem isLocallyBalancedAbs_three_one_catD4_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hp : q.p = 2) (hq : q.exponent = 1) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
  rw [hp, hq] at hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (isLocallyBalancedAbs_three_one_d4Two hK2)

end D4

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
