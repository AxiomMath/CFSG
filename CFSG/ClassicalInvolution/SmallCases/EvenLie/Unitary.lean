module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents

public noncomputable section

namespace CFSG.ClassicalInvolution

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents

section Radical

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
  (hC : IsPrimeFormGram C)

include hC in
theorem exists_two_radical_primeFormConj (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {H : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))}
    (hH : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤ H)
    (s : gramSU h (C : Matrix (Fin n) (Fin n) K)) (hs1 : (s : GL (Fin n) K) ≠ 1)
    (hss : (s : GL (Fin n) K) * s = 1) :
    ∃ R : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))),
      R ≤ H ⊓ Subgroup.centralizer
        ({primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩} : Set _) ∧
      (∀ β ∈ H ⊓ Subgroup.centralizer
        ({primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩} : Set _),
          β ∈ Subgroup.normalizer (R : Set _)) ∧
      (∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1) ∧
      (∀ x ∈ H ⊓ Subgroup.centralizer
        ({primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩} : Set _),
          x ∈ Subgroup.centralizer (R : Set _) → ∃ k : ℕ, x ^ 2 ^ k = 1) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := finite_mulAut_primeFormP (C := C) h
  set B := gramForm h (C : Matrix (Fin n) (Fin n) K) with hB
  set M : Matrix (Fin n) (Fin n) K := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := M - 1 with hN
  set α := primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ with hα
  obtain ⟨hsymm, hsep, -⟩ := unitary_prime_form_automorphism_data h hC
  have hMM : ∀ v, M *ᵥ (M *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hM, ← Units.val_mul, hss, Units.val_one, one_mulVec]
  have hNv : ∀ v, N *ᵥ v = M *ᵥ v - v := fun v => by rw [hN, sub_mulVec, one_mulVec]
  have hadd : ∀ w : Fin n → K, w + w = 0 := fun w => funext fun i => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  have hNN : ∀ v, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [hNv, hNv, mulVec_sub, hMM,
      show v - M *ᵥ v - (M *ᵥ v - v) = (v + v) - (M *ᵥ v + M *ᵥ v) by abel, hadd, hadd,
      sub_zero]
  have hs : (M.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * M = C := s.2.1
  have hiso : ∀ x y, B (M *ᵥ x) (M *ᵥ y) = B x y := fun x y => by
    rw [hB, gramForm_mulVec, hs]
  have hadj : ∀ x y, B (N *ᵥ x) y = B x (N *ᵥ y) := fun x y => by
    have h1 : B (M *ᵥ x) y = B x (M *ᵥ y) := by
      conv_lhs => rw [← hMM y]
      exact hiso x (M *ᵥ y)
    rw [hNv, hNv, map_sub, LinearMap.sub_apply, map_sub, h1]
  have hsepR : ∀ w, (∀ u, B u w = 0) → w = 0 := fun w hw =>
    hsep w fun u => by rw [← hsymm.eq u w, hw u, map_zero]
  set W : Submodule K (Fin n → K) := LinearMap.range N.mulVecLin with hW
  have hmemW : ∀ u, N *ᵥ u ∈ W := fun u => ⟨u, rfl⟩
  have hW0 : W ≠ ⊥ := by
    obtain ⟨v, hv⟩ : ∃ v, M *ᵥ v ≠ v := by
      by_contra hc
      push Not at hc
      refine hs1 (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_)))
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_one, one_mulVec]
      exact hc v
    refine (Submodule.ne_bot_iff W).mpr ⟨N *ᵥ v, hmemW v, fun h0 => hv ?_⟩
    rw [hNv, sub_eq_zero] at h0
    exact h0
  have hWiso : ∀ v ∈ W, ∀ w ∈ W, B v w = 0 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    change B (N *ᵥ a) (N *ᵥ b) = 0
    rw [hadj, hNN, map_zero]
  have hL : ∀ v, v ∈ W.orthogonalBilin B ↔ N *ᵥ v = 0 := fun v => by
    rw [Submodule.mem_orthogonalBilin]
    constructor
    · intro hv
      refine hsepR _ fun u => ?_
      rw [← hadj]
      exact hv _ (hmemW u)
    · rintro hv _ ⟨u, rfl⟩
      change B (N *ᵥ u) v = 0
      rw [hadj, hv, map_zero]
  obtain ⟨hR0, -, -, hnormR, -, hcentR, -⟩ :=
    even_unitary_isotropic_radical_centralizer h hC hn hq W hW0 hWiso
  set R := radicalImage h (C : Matrix (Fin n) (Fin n) K) W with hRdef
  have hcomm : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
        M * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro g hg
    obtain ⟨h1, -, h3⟩ := mem_isotropicRadical.mp hg
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec]
    have hMv : ∀ v, M *ᵥ v = v + N *ᵥ v := fun v => by rw [hNv]; abel
    have hNg : N *ᵥ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = N *ᵥ v := by
      have h4 := (hL _).mp (h3 v)
      rw [mulVec_sub, sub_eq_zero] at h4
      exact h4
    rw [hMv v, mulVec_add, h1 _ (hmemW v), hMv, hNg]
  have hRX : R ≤ H ⊓ Subgroup.centralizer ({α} : Set _) := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨hH ((mem_inner_primeFormP h (C : Matrix (Fin n) (Fin n) K) _).mpr ⟨g, rfl⟩), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, radicalConjHom_apply, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Units.ext (hcomm g g.2))
  have hnorm : ∀ β ∈ H ⊓ Subgroup.centralizer ({α} : Set _),
      β ∈ Subgroup.normalizer (R : Set _) := by
    intro β hβ'
    have hβ := (Subgroup.mem_inf.mp hβ').2
    obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq β
    rw [Subgroup.mem_centralizer_singleton_iff] at hβ
    set S : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := ⟨s, s.2.1⟩ with hS
    set c := primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) with hc
    set fφ := primeFormFieldHom h hC φ with hfφ
    have hconj : c (A * primeFormFieldU h hC φ S * A⁻¹) = c S := by
      rw [map_mul, map_mul, map_inv, ← primeFormField_conj_eq h hC φ S, ← hα]
      have e : primeFormPsi h hC ⟨A, φ⟩ * α * (primeFormPsi h hC ⟨A, φ⟩)⁻¹ = α := by
        rw [hβ, mul_inv_cancel_right]
      rw [primeFormPsi_apply] at e
      have e' : c A * (fφ * α * fφ⁻¹) * (c A)⁻¹ = c A * fφ * α * (c A * fφ)⁻¹ := by group
      rw [e', e]
    have hS2 : S * S = 1 := Subtype.ext hss
    have hS2' : S ^ 2 = 1 := by rw [sq, hS2]
    have hφS2 : primeFormFieldU h hC φ S ^ 2 = 1 := by rw [← map_pow, hS2', map_one]
    have hX4 : (A * primeFormFieldU h hC φ S * A⁻¹) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, conj_pow, hφS2, mul_one, mul_inv_cancel,
        one_pow]
    have hY4 : S ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hS2', one_pow]
    have hXY := eq_of_primeFormConjHom_eq h hC hn hconj hX4 hY4
    set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hAm
    have hAM : Am * M.map φ = M * Am := by
      have h1 := congrArg (fun X : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) =>
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Am) hXY
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_primeFormFieldU,
        coe_glAut] at h1
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h1
      exact h1
    have hmapN : ∀ v, (fun i => φ ((N *ᵥ v) i)) = N.map φ *ᵥ fun i => φ (v i) := fun v =>
      funext fun i => RingHom.map_mulVec (φ : K →+* K) N v i
    have hNmap : N.map φ = M.map φ - 1 := by
      ext i j
      rw [hN, Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub,
        Matrix.one_apply]
      split_ifs <;> simp
    have hTN : ∀ v, Am *ᵥ (fun i => φ ((N *ᵥ v) i)) = N *ᵥ (Am *ᵥ fun i => φ (v i)) :=
      fun v => by
        rw [hmapN, hNmap, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hAM,
          hN, Matrix.sub_mul, Matrix.one_mul]
    refine hnormR A φ ?_ ?_
    · rintro _ ⟨u, rfl⟩
      change Am *ᵥ (fun i => φ ((N *ᵥ u) i)) ∈ W
      rw [hTN]
      exact hmemW _
    · intro v hv
      rw [hL] at hv ⊢
      rw [← hTN, hv]
      simp only [Pi.zero_apply, map_zero]
      exact mulVec_zero _
  refine ⟨R, hRX, hnorm, ?_, fun x _ hx => ?_⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hR0 g
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · obtain ⟨k, hk⟩ := hcentR ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Radical

theorem noNonsolvableClassical_unitaryPSU {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    NoNonsolvableClassical (unitaryPSU h n) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h hC
  have hconj := conj_injective_primeFormP h hC hn
  have : Finite K := h.finite
  refine NoNonsolvableClassical.of_mulEquiv e.symm ?_
  intro t ht
  have hα2 : orderOf (MulAut.conj t) = 2 := by
    rw [orderOf_injective _ hconj]
    exact ht
  have hαinn : MulAut.conj t ∈ inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    ⟨t, rfl⟩
  have hF : primeFormFieldFactor h hC hn hq (MulAut.conj t) = RingEquiv.refl K := by
    have hαD : MulAut.conj t ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ (MulAut.conj t)).mp hαinn
      exact ⟨_, hs.symm⟩
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at hαD
    exact hαD
  obtain ⟨s, hs1, hss, hαs⟩ :=
    (even_unitary_involution_matrix_lifts h hC hn hq (MulAut.conj t) hα2).2.1 hF
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_primeFormConj h hC hn hq le_rfl s hs1 hss
  rw [← hαs] at hRX hnorm hcent
  exact NoNonsolvableClassicalAt.of_two_radical (MulAut.conj : _ →* _) hconj R hRX hnorm hR hcent ht

theorem noNonsolvableClassical_of_psu_model {X : Type} [Group X] {n f : ℕ}
    (hT : StatedClassicalModel X .PSU n 2 f) : NoNonsolvableClassical X := by
  obtain ⟨⟨-, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬ (n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  exact NoNonsolvableClassical.of_mulEquiv (eT.trans (unitaryPSUEquiv h (by omega)).symm)
    (noNonsolvableClassical_unitaryPSU h hn hq')

end CFSG.ClassicalInvolution
