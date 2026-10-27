module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.LeviMatrices
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.Link

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg Matrix

variable {n : ℕ}

theorem spinMatrix_apply_eq_spinMat {K : Type} [Field K] {σ : Type} [Fintype σ] [DecidableEq σ]
    (Q : QuadraticForm K (σ → K)) (x : spinGroup Q) (a b : σ) :
    ((spinMatrix Q x : GL σ K) : Matrix σ σ K) a b = spinMat Q x a b := by
  rw [spinMat_apply, coe_spinMatrix, LinearMap.toMatrix'_apply]
  rfl

theorem coe_ωp (hn : 3 ≤ n) (k : Fin n) :
    (((ωp (F := ZMod 2) hn k : StatedOmega (StatedQuadPlus n (ZMod 2))) :
      GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      posM n k := by
  ext a b
  have := (isCoord_plusFrame_flag (K := ZMod 2) hn).spinMat_longRoot
    (rootIdxD_ne n (by omega) k) true (rootSignD n k) (1 : ZMod 2) a b
  rw [← spinMatrix_apply_eq_spinMat] at this
  simpa [posM, lrM, ωp, genΩ, rootD] using this

theorem coe_ωn (hn : 3 ≤ n) (k : Fin n) :
    (((ωn (F := ZMod 2) hn k : StatedOmega (StatedQuadPlus n (ZMod 2))) :
      GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      negM n k := by
  ext a b
  have := (isCoord_plusFrame_flag (K := ZMod 2) hn).spinMat_longRoot
    (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false (1 : ZMod 2) a b
  rw [← spinMatrix_apply_eq_spinMat] at this
  simpa [negM, lrM, ωn, genΩ, negRootD] using this


section Scalar

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem statedQuadPlus_smul (c : F) (v : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F (c • v) = c ^ 2 * StatedQuadPlus n F v := by
  simp only [StatedQuadPlus, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_one_of_mem_statedScalars_plus (hn : 1 ≤ n) {A : StatedOmega (StatedQuadPlus n F)}
    (hA : (A : GL (Fin n ⊕ Fin n) F) ∈ StatedScalars (Fin n ⊕ Fin n) F) : A = 1 := by
  obtain ⟨u, hu⟩ := hA
  have hQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadPlus n F) A.2
  set v : Fin n ⊕ Fin n → F :=
    Pi.single (.inl ⟨0, by omega⟩) 1 + Pi.single (.inr ⟨0, by omega⟩) 1 with hvdef
  have hv : StatedQuadPlus n F v = 1 := by
    simp only [StatedQuadPlus, hvdef, Pi.add_apply, Pi.single_apply]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
    · simp
    · intro b _ hb
      have h1 : (Sum.inl b : Fin n ⊕ Fin n) ≠ .inl ⟨0, by omega⟩ := by
        intro h; exact hb (Sum.inl.inj h)
      have h2 : (Sum.inr b : Fin n ⊕ Fin n) ≠ .inr ⟨0, by omega⟩ := by
        intro h; exact hb (Sum.inr.inj h)
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hAv : ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v =
      (u : F) • v := by
    rw [← hu]
    funext i
    simp [Matrix.mulVec_diagonal, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hu2 : (u : F) * u = 1 := by
    have h1 := hQ v
    rw [hAv, statedQuadPlus_smul, hv] at h1
    linear_combination h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hu1 : (u : F) = 1 := by
    have : ((u : F) - 1) * ((u : F) - 1) = 0 := by linear_combination hu2 + (1 - (u : F)) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hu, show u = 1 from Units.ext hu1, map_one]

theorem eq_of_mk_eq_plus (hn : 1 ≤ n) {A B : StatedOmega (StatedQuadPlus n F)}
    (h : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n F))) =
      QuotientGroup.mk B) : A = B := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have := eq_one_of_mem_statedScalars_plus hn (A := A⁻¹ * B) h
  exact inv_mul_eq_one.1 this

end Scalar

theorem false_of_cyc_levi_nodes (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) {J : Subgroup Y}
    (hcyc : CycPerfect 3 J) (Ag : StatedOmega (StatedQuadPlus n (ZMod 2))) {h a b : Fin n}
    (hid : LeviIdentities (posM n h) (negM n h) (posM n a) (negM n a) (posM n b) (negM n b))
    (hJ : ∀ i ∈ ({h, a, b} : Set (Fin n)),
      e.symm (QuotientGroup.mk (Ag * ωp (by omega) i * Ag⁻¹)) ∈ J ∧
        e.symm (QuotientGroup.mk (Ag * ωn (by omega) i * Ag⁻¹)) ∈ J) : False := by
  have hn3 : 3 ≤ n := by omega
  let Θ : StatedOmega (StatedQuadPlus n (ZMod 2)) →* Y :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (MulAut.conj Ag).toMonoidHom)
  have hΘ : ∀ x, Θ x = e.symm (QuotientGroup.mk (Ag * x * Ag⁻¹)) := fun x => rfl
  have hinj : Function.Injective Θ := by
    intro x y hxy
    rw [hΘ, hΘ] at hxy
    have h1 := e.symm.injective hxy
    have h2 := eq_of_mk_eq_plus (n := n) (F := ZMod 2) (by omega) h1
    simpa using h2
  let ψ : StatedOmega (StatedQuadPlus n (ZMod 2)) →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
    (Units.coeHom _).comp (StatedOmega (StatedQuadPlus n (ZMod 2))).subtype
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext (Units.ext hxy)
  have hψp : ∀ k, ψ (ωp hn3 k) = posM n k := fun k => coe_ωp hn3 k
  have hψn : ∀ k, ψ (ωn hn3 k) = negM n k := fun k => coe_ωn hn3 k
  have hid' : LeviIdentities (ωp (F := ZMod 2) hn3 h) (ωn (F := ZMod 2) hn3 h)
      (ωp (F := ZMod 2) hn3 a) (ωn (F := ZMod 2) hn3 a) (ωp (F := ZMod 2) hn3 b)
      (ωn (F := ZMod 2) hn3 b) := by
    refine LeviIdentities.of_injective ψ hψinj ?_
    simpa only [hψp, hψn] using hid
  refine false_of_cyc_levi hcyc Θ hinj hid' ?_
  obtain ⟨h1, h2⟩ := hJ h (by simp)
  obtain ⟨a1, a2⟩ := hJ a (by simp)
  obtain ⟨b1, b2⟩ := hJ b (by simp)
  exact ⟨by rw [hΘ]; exact h1, by rw [hΘ]; exact h2, by rw [hΘ]; exact a1,
    by rw [hΘ]; exact a2, by rw [hΘ]; exact b1, by rw [hΘ]; exact b2⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD
