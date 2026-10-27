module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RT
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73O

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem squareClassGroup_mul_self (m : Multiplicative (TauCeti.SquareClassGroup K)) :
    m * m = 1 := by
  have h : (2 : ZMod 2) • Multiplicative.toAdd m = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [two_smul] at h
  exact congrArg Multiplicative.ofAdd h

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem det_transportHom_spinCent_odd
    (c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    QuadraticMap.orthogonalDet (detQ (K := K))
      (transportHom (two_ne_zero_spin hp hp2 hK) (spinCent K c)) = 1 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  set g := spinAction (quadOdd 3 K) (c : spinGroup (quadOdd 3 K)) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ _)
  have hgc : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g :=
    comm_of_mem_isoCentLa (spinCent K c).2
  have hn := (normal_subgroupOf_iff (spinJ_le_centralizer (K := K) hp hp2 hK).2.1).mp
    (normal_spinJ_odd (K := K) hp hp2 hK).2.1
  have hmap := CFSG.ClassicalInvolution.ModelFacts.map_longSL2_range
    (oddFrame 3 K).toHypFrame fin3_zero_ne_one true true
  have hconj : conjSubgroup g (frame01 K).La.range = (frame01 K).La.range := by
    rw [← hmap]
    ext x
    rw [mem_conjSubgroup]
    constructor
    · rintro ⟨j, hj, hjx⟩
      refine ⟨(c : spinGroup (quadOdd 3 K)) * j * (c : spinGroup (quadOdd 3 K))⁻¹,
        hn j c hj c.2, ?_⟩
      rw [map_mul, map_mul, map_inv, hjx, ← hg]
      group
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(c : spinGroup (quadOdd 3 K))⁻¹ * j * (c : spinGroup (quadOdd 3 K))⁻¹⁻¹,
        hn j _ hj (inv_mem c.2), ?_⟩
      rw [inv_inv, map_mul, map_mul, map_inv]
  rcases Frame.conjSubgroup_La_range h2 hgO hgc with ⟨hd, -, -⟩ | ⟨-, h1, -⟩
  · rw [QuadraticMap.orthogonalDet_apply]
    exact hd
  · exact absurd (hconj.symm.trans h1) (Frame.La_range_ne_swap_La_range _)

theorem card_centralizer_tSeven_le_odd :
    Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ≤
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  set C := centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  set φ₁ : C →* TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) :=
    (transportHom h2).comp (spinCent K) with hφ₁
  have hrange : φ₁.range ≤ (QuadraticMap.orthogonalDet (detQ (K := K))).ker := by
    rintro _ ⟨c, rfl⟩
    exact det_transportHom_spinCent_odd hp hp2 hK c
  let _ : Invertible (detQ (K := K) 1) := invertibleOfNonzero (by simp [detQ_apply])
  have hneg : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h' : (-1 : K) = 1 := by simpa using congrArg Units.val h
    calc (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [h']; ring)
  have hdet := two_mul_card_ker_le (QuadraticMap.orthogonalDet (detQ (K := K)))
    (x := TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := K)) 1)
    (by rw [QuadraticMap.orthogonalDet_reflectionOrthogonal]; exact hneg)
  rw [card_orthogonalGroup_detQ h2] at hdet
  have hR : Nat.card φ₁.range ≤ Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    have := card_le_of_le hrange
    nlinarith
  set φ₂ : φ₁.ker →* TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) :=
    (perpHom h2).comp ((spinCent K).comp φ₁.ker.subtype) with hφ₂
  have hrange₂ : φ₂.range ≤ (detSpinorNorm (nondegenerate_quadOdd 1 K)).ker := by
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker, ← detSpinorNorm_perpEmbO]
    apply detSpinorNorm_eq_one_of_mem_elementaryGroup
    rw [coe_perpEmbO, ← range_spinAction_quadOdd h2 (le_refl 3)]
    refine ⟨(c : C), ?_⟩
    exact spinAction_eq_perpEmb h2 c.2
  have hker₂ : Nat.card φ₂.ker ≤ 2 := by
    have hZ : Nat.card (center (spinGroup (quadOdd 3 K))) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [center_spinGroup_quadOdd h2 le_rfl, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact spinGroup.negOne_mul_self _ _)
          (spinGroup.negOne_ne_one _ _)]
    refine le_trans (Nat.card_le_card_of_injective
      (fun k => (⟨((k : φ₁.ker) : C), ker_spinAction_le_center _ ?_⟩ :
        center (spinGroup (quadOdd 3 K)))) ?_) hZ.le
    · rw [MonoidHom.mem_ker]
      apply spinAction_eq_one_of_resHom_eq_one h2
      exact Prod.ext (k : φ₁.ker).2 k.2
    · intro k k' h
      have h' := congrArg Subtype.val h
      dsimp only at h'
      apply Subtype.ext
      apply Subtype.ext
      exact Subtype.ext h'
  have h4 := four_mul_card_ker_detSpinorNorm_le (K := K)
  rw [card_orthogonalGroup_quadOdd_one h2] at h4
  have hK₁ : Nat.card φ₁.ker ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
    have e := card_ker_mul_card_range φ₂
    have := card_le_of_le hrange₂
    nlinarith
  calc Nat.card C = Nat.card φ₁.ker * Nat.card φ₁.range := (card_ker_mul_card_range φ₁).symm
    _ ≤ (Nat.card K * (Nat.card K ^ 2 - 1)) * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) :=
      Nat.mul_le_mul hK₁ hR
    _ = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by ring

theorem spinE_le_ker_spinNormC_odd [Invertible (2 : K)] :
    (spinE K).subgroupOf (centralizer {tSeven K}) ≤ (spinNormC K).ker := by
  have hodd := odd_card_spin hp hp2 hK
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  have key : ∀ ρ : SL(2, K) →* spinGroup (quadOdd 3 K), ρ.range ≤ centralizer {tSeven K} →
      ρ.range.subgroupOf (centralizer {tSeven K}) ≤ (spinNormC K).ker := by
    intro ρ hρ
    have e : ρ.range.subgroupOf (centralizer {tSeven K}) =
        (ρ.codRestrict _ fun x => hρ ⟨x, rfl⟩).range := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
    rw [e]
    exact le_ker_of_mul_self _ squareClassGroup_mul_self (range_le_closure_mul_self_sl2 hodd _)
  rw [subgroupOf_sup (sup_le l1 l2) l3, subgroupOf_sup l1 l2]
  exact sup_le (sup_le (key _ l1) (key _ l2)) (key _ l3)

theorem index_spinE_eq_two_odd :
    ((spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index =
      2 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hτ : (⟨spinTau ν hν0, hτC⟩ : centralizer {tSeven K}) ∉
      (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :=
    fun h => spinNormC_spinTau_ne_one ν hν0 hνs hτC (spinE_le_ker_spinNormC_odd hp hp2 hK h)
  have hC := card_centralizer_tSeven_le_odd hp hp2 hK
  have hE := card_spinE_odd hp hp2 hK
  have hEC := card_mul_index ((spinE K).subgroupOf
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv] at hEC
  have hpos : 0 < Nat.card (spinE K) := Nat.card_pos
  rw [mul_pow] at hE
  have hle : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≤ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [hEC]
    omega
  have hne1 : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≠ 1 := fun h =>
    hτ (by rw [index_eq_one.mp h]; exact mem_top _)
  have hne0 : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≠ 0 :=
    index_ne_zero_of_finite
  omega

theorem card_centralizer_tSeven_odd :
    Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hE := card_spinE_odd hp hp2 hK
  have hEC := card_mul_index ((spinE K).subgroupOf
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv,
    index_spinE_eq_two_odd hp hp2 hK] at hEC
  rw [← hEC, ← mul_pow, ← hE, mul_comm]

theorem ker_spinNormC_odd [Invertible (2 : K)] :
    (spinNormC K).ker = (spinE K).subgroupOf (centralizer {tSeven K}) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hle := spinE_le_ker_spinNormC_odd hp hp2 hK
  have hidx := index_spinE_eq_two_odd hp hp2 hK
  have hne : (spinNormC K).ker ≠ ⊤ := fun h =>
    spinNormC_spinTau_ne_one ν hν0 hνs hτC (by rw [← MonoidHom.mem_ker, h]; exact mem_top _)
  have hdvd := index_dvd_of_le hle
  rw [hidx] at hdvd
  have hk2 : (spinNormC K).ker.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (index_eq_one.mp h) hne
    · exact h
  refine (eq_of_le_of_card_ge hle ?_).symm
  have e1 := card_mul_index (spinNormC K).ker
  have e2 := card_mul_index ((spinE K).subgroupOf (centralizer ({tSeven K} :
    Set (spinGroup (quadOdd 3 K)))))
  rw [hk2] at e1
  rw [hidx] at e2
  omega

end Card

end CFSG.ComponentClassification.HarrisLit.T1
