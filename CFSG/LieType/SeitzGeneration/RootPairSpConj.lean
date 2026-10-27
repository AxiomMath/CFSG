module

public import CFSG.LieType.SeitzGeneration.RootPairSL2
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

namespace RootPair

section Conj

variable {r : ℕ} {K : Type} [Field K]

theorem spForm_gsp [NeZero r] (A : gsp r K) (x z : Fin r ⊕ Fin r → K) :
    spForm r K ((A : GL (Fin r ⊕ Fin r) K) *ᵥ x) ((A : GL (Fin r ⊕ Fin r) K) *ᵥ z) =
      (multiplier r K A : K) * spForm r K x z := by
  rw [spForm_mulVec]
  have h := multiplier_spec A
  have h' : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K r *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (multiplier r K A : K) • CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K r := h
  rw [h', map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

theorem conjSp_spTransvection [NeZero r] (A : gsp r K) (u : Fin r ⊕ Fin r → K) (t : K) :
    conjSp r K A (spTransvection u t) =
      spTransvection (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u)
        ((((multiplier r K A)⁻¹ : Kˣ) : K) * t) := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (conjSp r K A (spTransvection u t)) y = _
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set Aim : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAim
  have hAA : Am * Aim = 1 := by
    rw [hAm, hAim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv : Am *ᵥ (Aim *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have h1 : spEnd (conjSp r K A (spTransvection u t)) y =
      Am *ᵥ (spEnd (spTransvection u t) (Aim *ᵥ y)) := by
    rw [spEnd_apply, coe_conjSp, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, spEnd_apply (spTransvection u t)]
  rw [h1, spEnd_spTransvection, spEnd_spTransvection, Matrix.mulVec_add, Matrix.mulVec_smul,
    hinv]
  have h2 : spForm r K y (Am *ᵥ u) = (multiplier r K A : K) * spForm r K (Aim *ᵥ y) u := by
    conv_lhs => rw [← hinv]
    exact spForm_gsp A (Aim *ᵥ y) u
  rw [h2]
  congr 2
  have hμ : ((multiplier r K A)⁻¹ : Kˣ) * (multiplier r K A : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (-(t * spForm r K (Aim *ᵥ y) u)) * hμ

theorem spEnd_subfieldSpHom' {k : Subfield K} (g : StatedSp r k) (w : Fin r ⊕ Fin r → k) :
    spEnd (subfieldSpHom r k g) (fun i => (w i : K)) = fun i => ((spEnd g w i : k) : K) := by
  rw [spEnd_apply, spEnd_apply]
  funext i
  have h := RingHom.map_mulVec k.subtype
    ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) w i
  exact h.symm

end Conj

section Rational

variable {r : ℕ} {K : Type} [Field K] [Finite K] [NeZero r]

theorem conj_spSub_le {k : Subfield K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (A : gsp r K)
    (h : ∀ i j, (((multiplier r K A)⁻¹ : Kˣ) : K) *
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j) ^ 2 ∈ k) :
    (spSub r k).map (conjSp r K A).toMonoidHom ≤ spSub r k := by
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set μ : K := (multiplier r K A : K) with hμdef
  have hμ0 : μ ≠ 0 := Units.ne_zero _
  have hμμ : (((multiplier r K A)⁻¹ : Kˣ) : K) = μ⁻¹ := by
    rw [hμdef, Units.val_inv_eq_inv_val]
  rw [hμμ] at h
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, Am i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hAA : Am * (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
      rw [hAm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h0 : Am = 0 := Matrix.ext fun i j => hcon i j
    rw [h0, zero_mul] at hAA
    have := congrFun (congrFun hAA (Sum.inl ⟨0, NeZero.pos r⟩)) (Sum.inl ⟨0, NeZero.pos r⟩)
    simp at this
  set lam : K := Am i₀ j₀ with hlam
  have hrat : ∀ i j, Am i j / lam ∈ k := by
    intro i j
    have hq : (Am i j / lam) ^ 2 ∈ k := by
      have e : (Am i j / lam) ^ 2 = (μ⁻¹ * (Am i j) ^ 2) / (μ⁻¹ * lam ^ 2) := by
        field_simp
      rw [e]
      exact k.div_mem (h i j) (h i₀ j₀)
    exact mem_of_quadratic hp hp2 hK (α := 0) (β := -((Am i j / lam) ^ 2)) k.zero_mem
      (k.neg_mem hq) (by ring)
  have hlam2 : μ⁻¹ * lam ^ 2 ∈ k := h i₀ j₀
  have hcol : ∀ u₀ : Fin r ⊕ Fin r → k, ∃ w₀ : Fin r ⊕ Fin r → k,
      Am *ᵥ (fun a => (u₀ a : K)) = lam • (fun a => (w₀ a : K)) := by
    intro u₀
    refine ⟨fun i => ⟨∑ j, Am i j / lam * (u₀ j : K),
      k.sum_mem fun j _ => k.mul_mem (hrat i j) (u₀ j).2⟩, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hgen : ∀ (u₀ : Fin r ⊕ Fin r → k) (t₀ : k),
      conjSp r K A (subfieldSpHom r k (spTransvection u₀ t₀)) ∈ spSub r k := by
    intro u₀ t₀
    obtain ⟨w₀, hw₀⟩ := hcol u₀
    rw [subfieldSpHom_spTransvection, conjSp_spTransvection, hw₀, spTransvection_smul, hμμ]
    refine ⟨spTransvection w₀ ⟨μ⁻¹ * lam ^ 2 * t₀, k.mul_mem hlam2 t₀.2⟩, ?_⟩
    rw [subfieldSpHom_spTransvection]
    congr 1
    simp only
    ring
  have hS : ∀ g₀ : StatedSp r k, conjSp r K A (subfieldSpHom r k g₀) ∈ spSub r k := by
    let S : Subgroup (StatedSp r k) :=
      (spSub r k).comap ((conjSp r K A).toMonoidHom.comp (subfieldSpHom r k))
    have hle : Subgroup.closure {g : StatedSp r k | ∃ (v : Fin r ⊕ Fin r → k) (t : k),
        g = spTransvection v t} ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, t, rfl⟩
      exact hgen v t
    intro g₀
    have : g₀ ∈ S := hle (by rw [closure_spTransvection_eq_top]; trivial)
    exact this
  rintro _ ⟨g, ⟨g₀, rfl⟩, rfl⟩
  exact hS g₀

end Rational

end RootPair

end CFSG.LieType.SeitzGeneration
