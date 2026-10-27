module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def weylAct (w : WeylGroup τ) (a : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun i => rootChar a (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem eq_sum_single (v : Fin τ.rank → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem smul_eq_sum_single (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [eq_sum_single v]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _

theorem rootChar_single (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  have h := rootChar_nsmul_single a i 1
  rwa [one_smul, pow_one] at h

theorem eq_of_rootChar_eq {a b : Fin τ.rank → Kˣ} (h : ∀ v, rootChar a v = rootChar b v) :
    a = b :=
  funext fun i => by rw [← rootChar_single a i, ← rootChar_single b i, h]

theorem rootChar_weylAct (w : WeylGroup τ) (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (weylAct w a) v = rootChar a (w⁻¹ • v) := by
  rw [smul_eq_sum_single, rootChar_sum]
  conv_lhs => rw [eq_sum_single v, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, rootChar_single]
  rfl

theorem weylAct_one (a : Fin τ.rank → Kˣ) : weylAct (1 : WeylGroup τ) a = a :=
  eq_of_rootChar_eq fun v => by rw [rootChar_weylAct, inv_one, one_smul]

theorem weylAct_mul (w w' : WeylGroup τ) (a : Fin τ.rank → Kˣ) :
    weylAct (w * w') a = weylAct w (weylAct w' a) :=
  eq_of_rootChar_eq fun v => by
    rw [rootChar_weylAct, rootChar_weylAct, rootChar_weylAct, mul_inv_rev, mul_smul]

theorem weylAct_mul_left (w : WeylGroup τ) (a b : Fin τ.rank → Kˣ) :
    weylAct w (a * b) = weylAct w a * weylAct w b :=
  funext fun i => by
    simp only [weylAct, Pi.mul_apply, rootChar, Finset.prod_mul_distrib, mul_zpow]

theorem canonicalRep_conj_rootDiagUnit
    (w : WeylGroup τ) (a : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ a *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = rootDiagUnit τ (weylAct w a) :=
  ((rootDiagUnit_eq_conj_canonicalRep_iff (weylAct w a) a w).2 fun v => by
    rw [rootChar_weylAct, inv_smul_smul]).symm

theorem monomial_conj_rootDiagUnit
    (g : monomialSubgroup τ K) (a : Fin τ.rank → Kˣ) :
    (g : ModGL τ K) * rootDiagUnit τ a * (g : ModGL τ K)⁻¹ =
      rootDiagUnit τ (weylAct (weylQuotientHom τ K g) a) := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2
  have hmaps : MapsRootLines (g : ModGL τ K) w := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  rw [weylQuotientHom_eq hmaps, hgk, mul_inv_rev]
  have hc := canonicalRep_conj_rootDiagUnit (K := K) w a
  have hk' : k * rootDiagUnit τ (weylAct w a) * k⁻¹ = rootDiagUnit τ (weylAct w a) := by
    rw [← rootDiagUnit_mul_comm_of_mem_torusGroup (weylAct w a) hk, mul_inv_cancel_right]
  calc k * canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ a *
        ((canonicalRep (coxeterSystem τ) K w)⁻¹ * k⁻¹) =
      k * (canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ a *
        (canonicalRep (coxeterSystem τ) K w)⁻¹) * k⁻¹ := by group
    _ = rootDiagUnit τ (weylAct w a) := by rw [hc, hk']

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
