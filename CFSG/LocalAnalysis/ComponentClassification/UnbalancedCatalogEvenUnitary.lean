module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadicalNode
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenInvolutionLifts

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace EvenCatalog

theorem eq_one_of_mem_oddCore_of_pow_eq_one {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ CFSG.oddCore G) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card (CFSG.oddCore G) := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr odd_card_oddCore)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem oddCore_eq_bot_of_two_radical {M : Type*} [Group M] [Finite M] {X R : Subgroup M}
    (hRX : R ≤ X) (hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ Subgroup.centralizer (R : Set M), ∃ k : ℕ, x ^ 2 ^ k = 1) :
    CFSG.oddCore X = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hqR : (q : M) ∈ Subgroup.centralizer (R : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    set c : X := q * ⟨r, hRX hr⟩ * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹
    have hcQ : c ∈ CFSG.oddCore X := by
      have h1 : (⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹ ∈ CFSG.oddCore X :=
        (inferInstance : (CFSG.oddCore X).Normal).conj_mem _ (inv_mem hq) _
      have h2 := mul_mem hq h1
      rwa [show q * ((⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹) = c by
        simp only [c]; group] at h2
    have hcR : (c : M) ∈ R := by
      have h1 : (q : M) * r * (q : M)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hnorm q q.2) r).mp hr
      have h2 := mul_mem h1 (inv_mem hr)
      simpa [c] using h2
    obtain ⟨k, hk⟩ := hR _ hcR
    have hc1 : c = 1 :=
      eq_one_of_mem_oddCore_of_pow_eq_one hcQ (Subtype.ext (by simpa using hk))
    have hc1' : (q : M) * r * (q : M)⁻¹ * r⁻¹ = 1 := by
      simpa [c] using congrArg Subtype.val hc1
    have := mul_inv_eq_one.mp hc1'
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨k, hk⟩ := hcent _ hqR
  exact eq_one_of_mem_oddCore_of_pow_eq_one hq (Subtype.ext (by simpa using hk))

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
  (hC : IsPrimeFormGram C)

theorem finite_mulAut_primeFormP :
    Finite (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) := by
  have : Finite K := h.finite
  exact Finite.of_injective (fun e : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) =>
    (e : primeFormP h (C : Matrix (Fin n) (Fin n) K) → primeFormP h _))
    fun a b hab => MulEquiv.ext (congrFun hab)

include hC in
theorem oddCore_inf_centralizer_conj_eq_bot (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {H : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))}
    (hH : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤ H)
    (s : gramSU h (C : Matrix (Fin n) (Fin n) K)) (hs1 : (s : GL (Fin n) K) ≠ 1)
    (hss : (s : GL (Fin n) K) * s = 1) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
      ({primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩} : Set _)) = ⊥ := by
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
  refine oddCore_eq_bot_of_two_radical hRX hnorm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hR0 g
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · intro x hx
    obtain ⟨k, hk⟩ := hcentR ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end EvenCatalog

open EvenCatalog

theorem even_unitary_inner_involution_full_centralizer_odd_core {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {H : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))}
    (hH : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤ H) :
    (∀ α ∈ H, α ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) → orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({α} : Set _)) = ⊥) ∧
    ∀ α ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)), orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({α} : Set _)) = ⊥ := by
  have hmain : ∀ α ∈ H, α ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) → orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({α} : Set _)) = ⊥ := by
    intro α _ hαD hα
    have hF : primeFormFieldFactor h hC hn hq α = RingEquiv.refl K := by
      rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at hαD
      exact hαD
    obtain ⟨s, hs1, hss, rfl⟩ := (even_unitary_involution_matrix_lifts h hC hn hq α hα).2.1 hF
    exact oddCore_inf_centralizer_conj_eq_bot h hC hn hq hH s hs1 hss
  refine ⟨hmain, fun α hα hα2 => hmain α (hH hα) ?_ hα2⟩
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ α).mp hα
  exact ⟨_, rfl⟩

end CFSG.ComponentClassification.UnbalancedCatalog
