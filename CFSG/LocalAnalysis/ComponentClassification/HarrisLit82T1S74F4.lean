module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Cen

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

noncomputable def torusUnit (c d : Kˣ) : Fin 3 ⊕ Fin 3 ⊕ Unit → Kˣ :=
  Sum.elim (fun i => if i = 0 then d else if i = 2 then c else 1)
    (Sum.elim (fun i => if i = 0 then d⁻¹ else if i = 2 then c⁻¹ else 1) fun _ => 1)

noncomputable def torusEquiv (c d : Kˣ) : VEnd K :=
  LinearEquiv.piCongrRight fun σ => LinearEquiv.smulOfUnit (torusUnit c d σ)

theorem torusEquiv_apply (c d : Kˣ) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (σ : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    torusEquiv c d x σ = (torusUnit c d σ : K) * x σ := by
  simp [torusEquiv, LinearEquiv.smulOfUnit, Units.smul_def]

theorem torusEquiv_mem (c d : Kˣ) :
    torusEquiv c d ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  have hc : (c : K) * (c : K)⁻¹ = 1 := mul_inv_cancel₀ c.ne_zero
  have hd : (d : K) * (d : K)⁻¹ = 1 := mul_inv_cancel₀ d.ne_zero
  rw [quadOdd_apply, quadOdd_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [torusEquiv_apply, torusUnit]
  simp
  linear_combination (x (.inl 0) * x (.inr (.inl 0))) * hd +
    (x (.inl 2) * x (.inr (.inl 2))) * hc

theorem torusEquiv_vec (c d : Kˣ) :
    torusEquiv c d (oddVec 3 K 2 true) = (c : K) • oddVec 3 K 2 true ∧
      torusEquiv c d (oddZ 3 K) = oddZ 3 K ∧
      torusEquiv c d (oddVec 3 K 1 true) = oddVec 3 K 1 true ∧
      torusEquiv c d (oddVec 3 K 0 true) = (d : K) • oddVec 3 K 0 true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext σ <;> rcases σ with i | i | ⟨⟩ <;>
    (try fin_cases i) <;> simp [torusEquiv_apply, torusUnit, oddZ]

theorem torus_conj_gTwo (c d : Kˣ) :
    torusEquiv c d * gTwo K * (torusEquiv c d)⁻¹ =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) ((c : K) • oddZ 3 K) *
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) ((d : K) • oddVec 3 K 0 true) := by
  obtain ⟨h1, h2, h3, h4⟩ := torusEquiv_vec (K := K) c d
  have e1 := eichler_conj (torusEquiv_mem (K := K) c d) (oddVec 3 K 2 true) (oddZ 3 K)
  have e2 := eichler_conj (torusEquiv_mem (K := K) c d) (oddVec 3 K 1 true) (oddVec 3 K 0 true)
  rw [h1, h2, eichler_smul_left] at e1
  rw [h3, h4] at e2
  rw [← e1, ← e2, gTwo]
  group

theorem spinAction_xTwo (c d : K) :
    spinAction (quadOdd 3 K) (shortSeven K (upperSL2 c) *
        (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 d)) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (c • oddZ 3 K) *
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (d • oddVec 3 K 0 true) := by
  rw [map_mul, shortSeven, OddFrame.shortSL2_upperSL2, OddFrame.spinAction_shortRoot_eq_eichler,
    HypFrame.longSL2_upperSL2, HypFrame.spinAction_longRoot_eq_eichler]
  rfl

noncomputable abbrev xImage (c d : K) : VEnd K :=
  eichler (quadOdd 3 K) (oddVec 3 K 2 true) (c • oddZ 3 K) *
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (d • oddVec 3 K 0 true)

variable [Finite K]

theorem card_cen_xTwo_le (h2 : (2 : K) ≠ 0) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓ centralizer {xImage c d} :
      Subgroup (VEnd K)) ≤ 2 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by
  have := finite_VEnd (K := K)
  have hτO := torusEquiv_mem (K := K) (Units.mk0 c hc) (Units.mk0 d hd)
  have hconj := torus_conj_gTwo (K := K) (Units.mk0 c hc) (Units.mk0 d hd)
  simp only [Units.val_mk0] at hconj
  set τ := torusEquiv (K := K) (Units.mk0 c hc) (Units.mk0 d hd) with hτ
  have hG : gTwo K = τ⁻¹ * xImage c d * τ := by rw [xImage, ← hconj]; group
  let φ : (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓ centralizer {xImage c d} :
      Subgroup (VEnd K)) → cenGTwo K := fun g =>
    ⟨τ⁻¹ * g * τ, by
      obtain ⟨hgO, hgc⟩ := mem_inf.mp g.2
      have hg := mem_centralizer_singleton_iff.mp hgc
      refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hτO) hgO) hτO,
        mem_centralizer_singleton_iff.mpr ?_⟩
      rw [hG]
      calc τ⁻¹ * g * τ * (τ⁻¹ * xImage c d * τ) = τ⁻¹ * ((g : VEnd K) * xImage c d) * τ := by
            group
        _ = τ⁻¹ * (xImage c d * g) * τ := by rw [hg]
        _ = τ⁻¹ * xImage c d * τ * (τ⁻¹ * g * τ) := by group⟩
  have hφ : Function.Injective φ := by
    intro g g' h
    have h' : τ⁻¹ * (g : VEnd K) * τ = τ⁻¹ * g' * τ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  exact (Nat.card_le_card_of_injective φ hφ).trans (card_cenGTwo_le_mul h2)

theorem f4_holds : F4 := by
  intro K _ _ hodd h5 c d hc hd
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Finite (spinGroup (quadOdd 3 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have := finite_VEnd (K := K)
  set x := shortSeven K (upperSL2 c) *
    (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 d) with hx
  set C := centralizer ({x} : Set (spinGroup (quadOdd 3 K))) with hC
  let ψ : C →* VEnd K := (spinAction (quadOdd 3 K)).comp C.subtype
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hle : ψ.ker.map C.subtype ≤ (spinAction (quadOdd 3 K)).ker := by
      rintro _ ⟨g, hg, rfl⟩
      exact hg
    have hk : (spinAction (quadOdd 3 K)).ker = zpowers (spinZ K) := by
      rw [← center_spinGroup_quadOdd_eq_ker h2 (le_refl 3), center_spinGroup_quadOdd h2 (le_refl 3)]
    rw [← card_map_of_injective C.subtype_injective]
    calc Nat.card (ψ.ker.map C.subtype) ≤ Nat.card (spinAction (quadOdd 3 K)).ker :=
          card_le_of_le hle
      _ = 2 := by rw [hk, Nat.card_zpowers, orderOf_spinZ h2]
  have hrange : ψ.range ≤ (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
      centralizer {xImage c d} : Subgroup (VEnd K)) := by
    rintro _ ⟨g, rfl⟩
    refine mem_inf.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (map_spinAction _ _), mem_centralizer_singleton_iff.mpr ?_⟩
    have hg := mem_centralizer_singleton_iff.mp g.2
    rw [xImage, ← spinAction_xTwo]
    show spinAction (quadOdd 3 K) (g : spinGroup (quadOdd 3 K)) * spinAction (quadOdd 3 K) x =
      spinAction (quadOdd 3 K) x * spinAction (quadOdd 3 K) (g : spinGroup (quadOdd 3 K))
    rw [← map_mul, ← map_mul, hg]
  calc Nat.card C = Nat.card ψ.ker * Nat.card ψ.range := (card_ker_mul_card_range ψ).symm
    _ ≤ 2 * (2 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1)) :=
        Nat.mul_le_mul hker ((card_le_of_le hrange).trans (card_cen_xTwo_le h2 hc hd))
    _ = 4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by ring

end CFSG.ComponentClassification.HarrisLit.T1.S74
