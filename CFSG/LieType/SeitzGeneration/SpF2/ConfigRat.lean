module

public import CFSG.LieType.SeitzGeneration.RootPairSp

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LieType.SeitzGeneration.RootPair
  CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

variable {r : ℕ} {K : Type} [Field K] {k : Subfield K}

theorem ratVec_add (u v : Fin r ⊕ Fin r → k) : ratVec (u + v) = ratVec u + ratVec v := by
  funext a
  simp [ratVec]

theorem ratVec_dualVec (l : Fin r ⊕ Fin r) :
    ratVec (dualVec l : Fin r ⊕ Fin r → k) = (dualVec l : Fin r ⊕ Fin r → K) :=
  (dualVec_rat l).symm

theorem spForm_ratVec (u v : Fin r ⊕ Fin r → k) :
    spForm r K (ratVec u) (ratVec v) = ((spForm r k u v : k) : K) :=
  spForm_map k.subtype u v

theorem spTransvection_mem_conj [NeZero r] (A : gsp r K) {ν : K}
    (hν : ν * ν = (((multiplier r K A)⁻¹ : Kˣ) : K)) (w₀ : Fin r ⊕ Fin r → k) :
    spTransvection (ν • (((A : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ ratVec w₀)) 1 ∈
      (spSub r k).map (conjSp r K A).toMonoidHom := by
  refine ⟨subfieldSpHom r k (spTransvection w₀ 1), ⟨_, rfl⟩, ?_⟩
  change conjSp r K A (subfieldSpHom r k (spTransvection w₀ 1)) = _
  rw [subfieldSpHom_spTransvection, conjSp_spTransvection, spTransvection_smul, hν,
    OneMemClass.coe_one]
  rfl

theorem spForm_smul_mulVec [NeZero r] (A : gsp r K) {ν : K}
    (hν : ν * ν = (((multiplier r K A)⁻¹ : Kˣ) : K)) (x y : Fin r ⊕ Fin r → K) :
    spForm r K (ν • (((A : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x))
      (ν • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y)) =
      spForm r K x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, spForm_gsp]
  have hμ : (((multiplier r K A)⁻¹ : Kˣ) : K) * (multiplier r K A : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination ((multiplier r K A : K) * spForm r K x y) * hν + spForm r K x y * hμ

theorem mul_mem_of_spForm {c d s : K} {u₀ v₀ : Fin r ⊕ Fin r → k} (hs : s ∈ k) (hs0 : s ≠ 0)
    (h : spForm r K (c • ratVec u₀) (d • ratVec v₀) = s) : c * d ∈ k ∧ c * d ≠ 0 := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, spForm_ratVec] at h
  have ht0 : ((spForm r k u₀ v₀ : k) : K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at h
    exact hs0 h.symm
  have hcd : c * d = s / ((spForm r k u₀ v₀ : k) : K) := by
    rw [eq_div_iff ht0, ← h]
    ring
  rw [hcd]
  exact ⟨k.div_mem hs (spForm r k u₀ v₀).2, div_ne_zero hs0 ht0⟩

theorem sq_mem_of_spForm {f : (Fin r ⊕ Fin r → K) → Fin r ⊕ Fin r → K}
    (hf : ∀ x y, spForm r K (f x) (f y) = spForm r K x y)
    (hrat : ∀ w₀ : Fin r ⊕ Fin r → k, ∃ (c : K) (u₀ : Fin r ⊕ Fin r → k),
      f (ratVec w₀) = c • ratVec u₀)
    {x₀ y₀ : Fin r ⊕ Fin r → k} (hxy : spForm r K (ratVec x₀) (ratVec y₀) ≠ 0) {d : K}
    {v₀ : Fin r ⊕ Fin r → k} (hy : f (ratVec y₀) = d • ratVec v₀) : d ^ 2 ∈ k := by
  obtain ⟨c, u₀, hx⟩ := hrat x₀
  obtain ⟨e, z₀, hz⟩ := hrat (x₀ + y₀)
  have hsk : spForm r K (ratVec x₀) (ratVec y₀) ∈ k := by
    rw [spForm_ratVec]
    exact (spForm r k x₀ y₀).2
  have h1 := hf (ratVec x₀) (ratVec y₀)
  rw [hx, hy] at h1
  obtain ⟨hcd, hcd0⟩ := mul_mem_of_spForm hsk hxy h1
  have h2 := hf (ratVec x₀) (ratVec (x₀ + y₀))
  rw [hx, hz, ratVec_add, map_add, spForm_isAlt.self_eq_zero, zero_add] at h2
  obtain ⟨hce, hce0⟩ := mul_mem_of_spForm hsk hxy h2
  have h3 := hf (ratVec y₀) (ratVec (x₀ + y₀))
  rw [hy, hz, ratVec_add, map_add, spForm_isAlt.self_eq_zero, add_zero,
    ← spForm_isAlt.neg_eq (ratVec x₀) (ratVec y₀)] at h3
  obtain ⟨hde, -⟩ := mul_mem_of_spForm (k.neg_mem hsk) (neg_ne_zero.mpr hxy) h3
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcd0
  have he0 : e ≠ 0 := right_ne_zero_of_mul hce0
  have hsq : d ^ 2 = c * d * (d * e) / (c * e) := by
    field_simp
  rw [hsq]
  exact k.div_mem (k.mul_mem hcd hde) hce

theorem sq_entry_mem [NeZero r] (A : gsp r K) {ν : K}
    (hν : ν * ν = (((multiplier r K A)⁻¹ : Kˣ) : K))
    (hrat : ∀ w₀ : Fin r ⊕ Fin r → k, ∃ (c : K) (u₀ : Fin r ⊕ Fin r → k),
      ν • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        ratVec w₀) = c • ratVec u₀)
    (i j : Fin r ⊕ Fin r) :
    (((multiplier r K A)⁻¹ : Kˣ) : K) *
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j) ^ 2 ∈ k := by
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  obtain ⟨d, v₀, hd⟩ := hrat (Pi.single j 1)
  have hxy : spForm r K (ratVec (dualVec j : Fin r ⊕ Fin r → k))
      (ratVec (Pi.single j 1 : Fin r ⊕ Fin r → k)) ≠ 0 := by
    rw [ratVec_dualVec, ← single_one_rat, spForm_dualVec]
    simp
  have hd2 : d ^ 2 ∈ k :=
    sq_mem_of_spForm (f := fun x => ν • (Am *ᵥ x)) (spForm_smul_mulVec A hν) hrat hxy hd
  have hij : ν * Am i j = d * (v₀ i : K) := by
    have h := congrFun hd i
    rw [← single_one_rat, Matrix.mulVec_single_one] at h
    exact h
  have hsq : (((multiplier r K A)⁻¹ : Kˣ) : K) * Am i j ^ 2 = d ^ 2 * (v₀ i : K) ^ 2 := by
    linear_combination (-(Am i j) ^ 2) * hν + (ν * Am i j + d * (v₀ i : K)) * hij
  rw [hsq]
  exact k.mul_mem hd2 (k.pow_mem (v₀ i).2 2)

end CFSG.LieType.SeitzGeneration.SpF2
