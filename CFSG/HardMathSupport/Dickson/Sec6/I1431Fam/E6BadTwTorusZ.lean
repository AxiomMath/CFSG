module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section

variable {K : Type} [Field K]

theorem torusZ_zero (ζ : Kˣ) (hζ : orderOf ζ = 3) : torusZ K ζ hζ 0 = 1 := by
  unfold torusZ
  rw [show Multiplicative.ofAdd (0 : Fin Tag.E6.rank → ZMod 3) = 1 from rfl, map_one, map_one]

theorem torusZ_add (ζ : Kˣ) (hζ : orderOf ζ = 3) (x y : Fin Tag.E6.rank → ZMod 3) :
    torusZ K ζ hζ (x + y) = torusZ K ζ hζ x * torusZ K ζ hζ y := by
  unfold torusZ
  rw [ofAdd_add, map_mul, map_mul]

theorem torusZ_single (ζ : Kˣ) (hζ : orderOf ζ = 3) (k : Fin Tag.E6.rank) :
    torusZ K ζ hζ (Pi.single k 1) = e6Data_valid.hm K k ζ := by
  unfold torusZ
  have : zeta3Pi ζ hζ (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) = Pi.mulSingle k ζ := by
    funext j
    rw [zeta3Pi_apply]
    by_cases hj : j = k
    · subst hj
      haveI : Fact (1 < 3) := ⟨by norm_num⟩
      have h1 : (Pi.single j (1 : ZMod 3) : Fin Tag.E6.rank → ZMod 3) j = 1 :=
        Pi.single_eq_same j 1
      show ζ ^ ((Pi.single j (1 : ZMod 3) : Fin Tag.E6.rank → ZMod 3) j).val =
        (Pi.mulSingle j ζ : Fin Tag.E6.rank → Kˣ) j
      rw [h1, ZMod.val_one, pow_one, Pi.mulSingle_eq_same]
    · simp [Pi.single_apply, hj, Pi.mulSingle_eq_of_ne hj]
  rw [this, minTorus_mulSingle]

theorem vT1_eq : vT1 = (Pi.single (nd 3) 1 : Fin Tag.E6.rank → ZMod 3) := by decide +kernel

theorem vT2_eq : vT2 = (Pi.single (nd 2) 1 + Pi.single (nd 3) 1 + Pi.single (nd 4) 1 :
    Fin Tag.E6.rank → ZMod 3) := by decide +kernel

theorem vT3_eq : vT3 = (Pi.single (nd 0) 1 + Pi.single (nd 2) 1 + Pi.single (nd 3) 1 +
    Pi.single (nd 4) 1 + Pi.single (nd 5) 1 : Fin Tag.E6.rank → ZMod 3) := by decide +kernel

theorem torusZ_vT1 (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    torusZ K ζ hζ vT1 = e6Data_valid.hm K (nd 3) ζ := by
  rw [vT1_eq, torusZ_single]

theorem torusZ_vT2 (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    torusZ K ζ hζ vT2 = e6Data_valid.hm K (nd 2) ζ * e6Data_valid.hm K (nd 3) ζ *
      e6Data_valid.hm K (nd 4) ζ := by
  rw [vT2_eq, torusZ_add, torusZ_add, torusZ_single, torusZ_single, torusZ_single]

theorem torusZ_vT3 (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    torusZ K ζ hζ vT3 = e6Data_valid.hm K (nd 0) ζ * e6Data_valid.hm K (nd 2) ζ *
      e6Data_valid.hm K (nd 3) ζ * e6Data_valid.hm K (nd 4) ζ * e6Data_valid.hm K (nd 5) ζ := by
  rw [vT3_eq, torusZ_add, torusZ_add, torusZ_add, torusZ_add, torusZ_single, torusZ_single,
    torusZ_single, torusZ_single, torusZ_single]

theorem nm_conj_hm_of_cartan_zero (j l : Fin Tag.E6.rank) (h : Tag.E6.cartan l j = 0) (t : Kˣ) :
    e6Data_valid.nm K j * e6Data_valid.hm K l t * (e6Data_valid.nm K j)⁻¹ =
      e6Data_valid.hm K l t := by
  rw [e6Data_valid.nm_conj_hm K j l t, h, neg_zero, zpow_zero, e6Data_valid.hm_one, mul_one]

theorem nm_conj_hm_of_cartan_neg_one (j l : Fin Tag.E6.rank) (h : Tag.E6.cartan l j = -1)
    (t : Kˣ) :
    e6Data_valid.nm K j * e6Data_valid.hm K l t * (e6Data_valid.nm K j)⁻¹ =
      e6Data_valid.hm K l t * e6Data_valid.hm K j t := by
  rw [e6Data_valid.nm_conj_hm K j l t, h, neg_neg, zpow_one]

theorem nHat2_conj_torusZ (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    nHatE K (nf 2) * torusZ K ζ hζ vT1 * (nHatE K (nf 2))⁻¹ = torusZ K ζ hζ vT2 := by
  have e2 : nHatE K (nf 2) = e6Data_valid.nm K (nd 2) * e6Data_valid.nm K (nd 4) := rfl
  rw [e2, torusZ_vT1, torusZ_vT2]
  have h1 := nm_conj_hm_of_cartan_neg_one (K := K) (nd 4) (nd 3) (by decide) ζ
  have h2 := nm_conj_hm_of_cartan_neg_one (K := K) (nd 2) (nd 3) (by decide) ζ
  have h3 := nm_conj_hm_of_cartan_zero (K := K) (nd 2) (nd 4) (by decide) ζ
  calc e6Data_valid.nm K (nd 2) * e6Data_valid.nm K (nd 4) * e6Data_valid.hm K (nd 3) ζ *
        (e6Data_valid.nm K (nd 2) * e6Data_valid.nm K (nd 4))⁻¹
      = e6Data_valid.nm K (nd 2) * (e6Data_valid.nm K (nd 4) * e6Data_valid.hm K (nd 3) ζ *
          (e6Data_valid.nm K (nd 4))⁻¹) * (e6Data_valid.nm K (nd 2))⁻¹ := by group
    _ = e6Data_valid.nm K (nd 2) * (e6Data_valid.hm K (nd 3) ζ * e6Data_valid.hm K (nd 4) ζ) *
          (e6Data_valid.nm K (nd 2))⁻¹ := by rw [h1]
    _ = (e6Data_valid.nm K (nd 2) * e6Data_valid.hm K (nd 3) ζ * (e6Data_valid.nm K (nd 2))⁻¹) *
          (e6Data_valid.nm K (nd 2) * e6Data_valid.hm K (nd 4) ζ *
            (e6Data_valid.nm K (nd 2))⁻¹) := by group
    _ = (e6Data_valid.hm K (nd 3) ζ * e6Data_valid.hm K (nd 2) ζ) * e6Data_valid.hm K (nd 4) ζ := by
          rw [h2, h3]
    _ = e6Data_valid.hm K (nd 2) ζ * e6Data_valid.hm K (nd 3) ζ * e6Data_valid.hm K (nd 4) ζ := by
          rw [(hm_commute (nd 3) (nd 2) ζ ζ).eq]

theorem conj_chain_three {G : Type*} [Group G] (n0 n5 h0 h2 h3 h4 h5 : G)
    (a2 : n5 * h2 * n5⁻¹ = h2) (a3 : n5 * h3 * n5⁻¹ = h3) (a4 : n5 * h4 * n5⁻¹ = h4 * h5)
    (b2 : n0 * h2 * n0⁻¹ = h2 * h0) (b3 : n0 * h3 * n0⁻¹ = h3) (b4 : n0 * h4 * n0⁻¹ = h4)
    (b5 : n0 * h5 * n0⁻¹ = h5) (c : h2 * h0 = h0 * h2) :
    n0 * n5 * (h2 * h3 * h4) * (n0 * n5)⁻¹ = h0 * h2 * h3 * h4 * h5 := by
  have c1 : n5 * (h2 * h3 * h4) * n5⁻¹ = h2 * h3 * (h4 * h5) := by
    calc n5 * (h2 * h3 * h4) * n5⁻¹ = (n5 * h2 * n5⁻¹) * (n5 * h3 * n5⁻¹) * (n5 * h4 * n5⁻¹) := by
          group
      _ = h2 * h3 * (h4 * h5) := by rw [a2, a3, a4]
  have c2 : n0 * (h2 * h3 * (h4 * h5)) * n0⁻¹ = (h2 * h0) * h3 * (h4 * h5) := by
    calc n0 * (h2 * h3 * (h4 * h5)) * n0⁻¹ =
          (n0 * h2 * n0⁻¹) * (n0 * h3 * n0⁻¹) * ((n0 * h4 * n0⁻¹) * (n0 * h5 * n0⁻¹)) := by
          group
      _ = (h2 * h0) * h3 * (h4 * h5) := by rw [b2, b3, b4, b5]
  calc n0 * n5 * (h2 * h3 * h4) * (n0 * n5)⁻¹ = n0 * (n5 * (h2 * h3 * h4) * n5⁻¹) * n0⁻¹ := by
        group
    _ = (h2 * h0) * h3 * (h4 * h5) := by rw [c1, c2]
    _ = h0 * h2 * h3 * h4 * h5 := by rw [c]; group

theorem nHat3_conj_torusZ (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    nHatE K (nf 3) * torusZ K ζ hζ vT2 * (nHatE K (nf 3))⁻¹ = torusZ K ζ hζ vT3 := by
  have e3 : nHatE K (nf 3) = e6Data_valid.nm K (nd 0) * e6Data_valid.nm K (nd 5) := rfl
  rw [e3, torusZ_vT2, torusZ_vT3]
  exact conj_chain_three _ _ _ _ _ _ _
    (nm_conj_hm_of_cartan_zero (K := K) (nd 5) (nd 2) (by decide) ζ)
    (nm_conj_hm_of_cartan_zero (K := K) (nd 5) (nd 3) (by decide) ζ)
    (nm_conj_hm_of_cartan_neg_one (K := K) (nd 5) (nd 4) (by decide) ζ)
    (nm_conj_hm_of_cartan_neg_one (K := K) (nd 0) (nd 2) (by decide) ζ)
    (nm_conj_hm_of_cartan_zero (K := K) (nd 0) (nd 3) (by decide) ζ)
    (nm_conj_hm_of_cartan_zero (K := K) (nd 0) (nd 4) (by decide) ζ)
    (nm_conj_hm_of_cartan_zero (K := K) (nd 0) (nd 5) (by decide) ζ)
    (hm_commute (nd 2) (nd 0) ζ ζ).eq

theorem cartanCoord_neg (γ : Fin Tag.E6.rank → ℤ) (k : Fin Tag.E6.rank) :
    ExceptionalCover.cartanCoord (-γ) k = -ExceptionalCover.cartanCoord γ k := by
  simp [ExceptionalCover.cartanCoord, Finset.sum_neg_distrib]

theorem rootChar_neg (γ : Fin Tag.E6.rank → ℤ) (u : Fin Tag.E6.rank → Kˣ) :
    ExceptionalCover.rootChar K (-γ) u = (ExceptionalCover.rootChar K γ u)⁻¹ := by
  rw [ExceptionalCover.rootChar_apply, ExceptionalCover.rootChar_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [cartanCoord_neg, zpow_neg]

theorem commute_minTorus_rootGroup {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    {u : Fin Tag.E6.rank → Kˣ} (hu : ExceptionalCover.rootChar K γ u = 1)
    {y : e6Data_valid.minGroup K} (hy : y ∈ e6Data_valid.rootGroup K γ) :
    Commute (minTorus e6Data_valid K u) y := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hy
  have h := minTorus_conj_xm e6Data_valid K u hγ c
  rw [hu, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem commute_minTorus_rootPair {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    {u : Fin Tag.E6.rank → Kˣ} (hu : ExceptionalCover.rootChar K γ u = 1)
    {y : e6Data_valid.minGroup K} (hy : y ∈ rootPair K γ) :
    Commute (minTorus e6Data_valid K u) y := by
  have hu' : ExceptionalCover.rootChar K (-γ) u = 1 := by rw [rootChar_neg, hu, inv_one]
  have hle : rootPair K γ ≤ Subgroup.centralizer {minTorus e6Data_valid K u} := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_minTorus_rootGroup hγ hu hy).eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_minTorus_rootGroup (CFSG.LieType.Chevalley.IsRoot.neg hγ) hu' hy).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem rootChar_zeta3Pi (ζ : Kˣ) (hζ : orderOf ζ = 3) (γ : Fin Tag.E6.rank → ℤ)
    (x : Fin Tag.E6.rank → ZMod 3) :
    ExceptionalCover.rootChar K γ (zeta3Pi ζ hζ (Multiplicative.ofAdd x)) =
      ζ ^ (∑ k, ((x k).val : ℤ) * ExceptionalCover.cartanCoord γ k) := by
  rw [ExceptionalCover.rootChar_apply, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zeta3Pi_apply, ← zpow_natCast, ← zpow_mul]
  rfl

theorem commute_torusZ_rootPair (ζ : Kˣ) (hζ : orderOf ζ = 3) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : (3 : ℤ) ∣ ∑ k, ((x k).val : ℤ) * ExceptionalCover.cartanCoord γ k)
    {y : e6Data_valid.minGroup K} (hy : y ∈ rootPair K γ) : Commute (torusZ K ζ hζ x) y := by
  refine commute_minTorus_rootPair hγ ?_ hy
  rw [rootChar_zeta3Pi]
  have hdvd : (orderOf ζ : ℤ) ∣ ∑ k, ((x k).val : ℤ) * ExceptionalCover.cartanCoord γ k := by
    rw [hζ]
    exact_mod_cast hx
  exact orderOf_dvd_iff_zpow_eq_one.1 hdvd

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
