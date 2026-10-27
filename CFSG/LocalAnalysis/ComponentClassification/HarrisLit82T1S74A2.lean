module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ADefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73I
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Rad

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem yThree_eq_smul_oddZ (h2 : (2 : K) ≠ 0)
    {h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hf : (frame01 K).La (-1) (h (oddVec 3 K 2 false)) = h (oddVec 3 K 2 false)) :
    yThree h = yThree h (.inr (.inr ())) • oddZ 3 K := by
  have hfix : (frame01 K).La (-1) (yThree h) = yThree h := by
    simp only [yThree, wThree, map_smul, map_sub, hf, La_neg_one_apply_e2, La_neg_one_apply_f2]
  have e := eq_of_La_neg_one_apply_eq h2 hfix
  have he : yThree h (.inr (.inl 2)) = 0 := by
    have h1 := polar_eTwo_yThree (h := h)
    rwa [polar_comm, oddVec_true, polar_quadOdd_single_inl] at h1
  have hf' : yThree h (.inl 2) = 0 := by
    have h1 := polar_fTwo_yThree (h := h)
    rwa [polar_comm, oddVec_false, polar_quadOdd_single_inr_inl] at h1
  rw [he, hf', zero_smul, zero_smul, zero_add, zero_add] at e
  exact e

section Odd

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem orthogonalDet_perpHom_spinCent_odd (h2 : (2 : K) ≠ 0)
    (c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    QuadraticMap.orthogonalDet (quadOdd 1 K) (perpHom h2 (spinCent K c)) = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hodd := odd_card_spin hp hp2 hK
  let δ : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →* Kˣ :=
    (QuadraticMap.orthogonalDet (quadOdd 1 K)).comp ((perpHom h2).comp (spinCent K))
  have hδ : ∀ y, δ y = QuadraticMap.orthogonalDet (quadOdd 1 K) (perpHom h2 (spinCent K y)) :=
    fun _ => rfl
  have hsep : (QuadraticMap.polarBilin (quadOdd 1 K)).SeparatingLeft :=
    (QuadraticMap.nondegenerate_polar_iff.mpr (nondegenerate_quadOdd 1 K)).1
  have hsq : ∀ y, δ y * δ y = 1 := fun y => by
    rw [← pow_two, hδ]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hsep _
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  have key : ∀ ρ : SL(2, K) →* spinGroup (quadOdd 3 K),
      ρ.range ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →
      ρ.range.subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ≤
        δ.ker := by
    intro ρ hρ
    have e : ρ.range.subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) =
        (ρ.codRestrict _ fun x => hρ ⟨x, rfl⟩).range := by
      ext x
      rw [mem_subgroupOf]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
    rw [e]
    refine (range_le_closure_mul_self_sl2 hodd _).trans ?_
    rw [closure_le]
    rintro _ ⟨y, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul]
    exact hsq y
  have hE : (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ≤
      δ.ker := by
    rw [subgroupOf_sup (sup_le l1 l2) l3, subgroupOf_sup l1 l2]
    exact sup_le (sup_le (key _ l1) (key _ l2)) (key _ l3)
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hτE : (⟨spinTau ν hν0, hτC⟩ : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ∉
      (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :=
    fun h => spinNormC_spinTau_ne_one ν hν0 hνs hτC (spinE_le_ker_spinNormC_odd hp hp2 hK h)
  have hτδ : δ ⟨spinTau ν hν0, hτC⟩ = 1 := by
    let _ : Invertible (quadOdd 1 K (tauW₃ ν)) :=
      invertibleOfNonzero (by rw [quadOdd_tauW₃]; exact inv_ne_zero hν0)
    let _ : Invertible (quadOdd 1 K (tauW₄ K)) :=
      invertibleOfNonzero (by rw [quadOdd_tauW₄]; exact one_ne_zero)
    have hP : perpHom h2 (spinCent K ⟨spinTau ν hν0, hτC⟩) =
        TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) (tauW₃ ν) *
          TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) (tauW₄ K) := by
      apply Subtype.ext
      refine LinearEquiv.ext fun w => ?_
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      exact perpTransport_spinTau ν hν0 w
    rw [hδ, hP, map_mul, QuadraticMap.orthogonalDet_reflectionOrthogonal,
      QuadraticMap.orthogonalDet_reflectionOrthogonal, neg_one_mul, neg_neg]
  have hidx := index_spinE_eq_two_odd hp hp2 hK
  show δ c = 1
  by_cases hc : c ∈ (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))
  · exact MonoidHom.mem_ker.mp (hE hc)
  · have h1 := MonoidHom.mem_ker.mp
      (hE ((mul_mem_iff_of_index_two hidx).mpr (iff_of_false hc hτE)))
    rwa [map_mul, hτδ, mul_one] at h1

theorem mem_spinE_of_commute_qThree [Invertible (2 : K)] {c : spinGroup (quadOdd 3 K)}
    (hct : c ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))
    (hcq : c * qThree K = qThree K * c) : c ∈ spinE K := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hh : CommThree (spinAction (quadOdd 3 K) c) := ⟨h2, map_spinAction _ c, by
    rw [← spinAction_qThree, ← map_mul, ← map_mul, hcq]⟩
  obtain ⟨γ, hy⟩ : ∃ γ : K, yThree (spinAction (quadOdd 3 K) c) = γ • oddZ 3 K :=
    ⟨_, yThree_eq_smul_oddZ h2 (La_neg_one_apply_spinAction hct La_neg_one_apply_f2)⟩
  have hjact : spinAction (quadOdd 3 K) (shortSeven K (upperSL2 γ)) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree (spinAction (quadOdd 3 K) c)) := by
    rw [hy, OddFrame.shortSL2_upperSL2]
    exact OddFrame.spinAction_shortRoot_eq_eichler _ 2 true γ
  have hjC : shortSeven K (upperSL2 γ) ∈
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) :=
    mem_centralizer_singleton_iff.mpr (commute_shortSeven_longSL2 true _ (-1)).eq
  have hc'C : (shortSeven K (upperSL2 γ))⁻¹ * c ∈
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) :=
    mul_mem (inv_mem hjC) hct
  have hc'act : spinAction (quadOdd 3 K) ((shortSeven K (upperSL2 γ))⁻¹ * c) =
      ellThree (spinAction (quadOdd 3 K) c) := by
    rw [map_mul, map_inv, hjact]
  have hperp : ∀ w : Fin 1 ⊕ Fin 1 ⊕ Unit → K,
      (perpHom h2 (spinCent K ⟨_, hc'C⟩) :
        (Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) w =
        lamThree (spinAction (quadOdd 3 K) c) • w := by
    intro w
    show perpCoords (spinAction (quadOdd 3 K) ((shortSeven K (upperSL2 γ))⁻¹ * c)
      (perpIncl w)) = _
    rw [hc'act, hh.ell_apply_of_fix (La_neg_one_perpIncl w), map_smul, perpCoords_perpIncl]
  have hlam : lamThree (spinAction (quadOdd 3 K) c) = 1 := by
    have hdet := orthogonalDet_perpHom_spinCent_odd hp hp2 hK h2 ⟨_, hc'C⟩
    rw [QuadraticMap.orthogonalDet_apply] at hdet
    have h1 := congrArg Units.val hdet
    have hlin : ((perpHom h2 (spinCent K ⟨_, hc'C⟩) :
        (Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) :
          (Fin 1 ⊕ Fin 1 ⊕ Unit → K) →ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) =
        lamThree (spinAction (quadOdd 3 K) c) • LinearMap.id :=
      LinearMap.ext fun w => hperp w
    rw [LinearEquiv.coe_det, Units.val_one, hlin, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Module.finrank_fintype_fun_eq_card,
      show Fintype.card (Fin 1 ⊕ Fin 1 ⊕ Unit) = 3 from rfl] at h1
    calc lamThree (spinAction (quadOdd 3 K) c) =
        lamThree (spinAction (quadOdd 3 K) c) *
          (lamThree (spinAction (quadOdd 3 K) c) * lamThree (spinAction (quadOdd 3 K) c)) := by
          rw [hh.lam, mul_one]
      _ = lamThree (spinAction (quadOdd 3 K) c) ^ 3 := by ring
      _ = 1 := h1
  have hP : perpHom h2 (spinCent K ⟨_, hc'C⟩) = 1 := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => ?_
    rw [hperp, hlam, one_smul]
    rfl
  have hsn : spinNormC K ⟨_, hc'C⟩ = 1 := by
    show CliffordAlgebra.orthogonalSpinorNorm (quadOdd 1 K) (nondegenerate_quadOdd 1 K)
      (perpHom h2 (spinCent K ⟨_, hc'C⟩)) = 1
    rw [hP, map_one]
  have hc'E : (shortSeven K (upperSL2 γ))⁻¹ * c ∈ spinE K := by
    have hk := MonoidHom.mem_ker.mpr hsn
    rw [ker_spinNormC_odd hp hp2 hK, mem_subgroupOf] at hk
    exact hk
  have hjE : shortSeven K (upperSL2 γ) ∈ spinE K := mem_sup_left (mem_sup_left ⟨_, rfl⟩)
  have hmem := mul_mem hjE hc'E
  rwa [mul_inv_cancel_left] at hmem

end Odd

theorem a2_holds : A2 := by
  intro K _ _ hodd
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp2 : ringChar K ≠ 2 := fun h => by
    rw [hK, h] at hodd
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' n.ne_zero).2 even_two)
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_spin hp hp2 hK)
  rintro c ⟨hct, hcq⟩
  exact mem_spinE_of_commute_qThree hp hp2 hK hct (mem_centralizer_singleton_iff.mp hcq)

end CFSG.ComponentClassification.HarrisLit.T1.S74
