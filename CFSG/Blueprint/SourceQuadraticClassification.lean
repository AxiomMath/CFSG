module

public import CFSG.Blueprint.SourceClassicalModels
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap
open LinearMap (BilinForm)
open CFSG.LieType.Universal.Spin (quadPlus quadOdd quadMinus coe_quadPlus coe_quadOdd
  coe_quadMinus)
open CFSG.GroupTheory.WeirSylow (IsPlusType)


open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap
open LinearMap (BilinForm)

section Forms

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def IsSourceQuadratic.toQuadraticForm {Q : V → K} (hQ : IsSourceQuadratic Q) :
    QuadraticForm K V where
  toFun := Q
  toFun_smul a x := by rw [hQ.1, smul_eq_mul, _root_.sq]
  exists_companion' := by
    obtain ⟨B, hB⟩ := hQ.2.1
    exact ⟨B, fun x y => by rw [hB]; ring⟩

theorem IsSourceQuadratic.coe_toQuadraticForm {Q : V → K} (hQ : IsSourceQuadratic Q) :
    ⇑hQ.toQuadraticForm = Q :=
  rfl

theorem isSourceQuadratic_of_nondegenerate (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) : IsSourceQuadratic ⇑Q := by
  refine ⟨fun a x => by rw [QuadraticMap.map_smul, smul_eq_mul, _root_.sq],
    ⟨polarBilin Q, fun x y => rfl⟩,
    ?_⟩
  ext x
  refine ⟨fun hx => Set.mem_singleton_iff.mpr (hQ.1 x fun y => hx.2 y), fun hx => ?_⟩
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨QuadraticMap.map_zero Q, fun y => by rw [zero_add, QuadraticMap.map_zero, sub_zero,
    sub_self]⟩

theorem IsSourceQuadratic.nondegenerate [Finite K] [FiniteDimensional K V] {Q : V → K}
    (hQ : IsSourceQuadratic Q) (h : ringChar K ≠ 2 ∨ Even (finrank K V)) :
    (polarBilin hQ.toQuadraticForm).Nondegenerate := by
  set Q' := hQ.toQuadraticForm with hQ'
  have hpol : ∀ x y, polarBilin Q' x y = Q (x + y) - Q x - Q y := fun x y => rfl
  have hrad : ∀ x, (∀ y, polarBilin Q' x y = 0) → Q x = 0 → x = 0 := fun x hx hx0 => by
    have : x ∈ {x | Q x = 0 ∧ ∀ y, Q (x + y) - Q x - Q y = 0} :=
      ⟨hx0, fun y => by rw [← hpol]; exact hx y⟩
    rwa [hQ.2.2, Set.mem_singleton_iff] at this
  have hsymm : ∀ x y, polarBilin Q' x y = polarBilin Q' y x := fun x y => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]
  suffices hsep : ∀ x, (∀ y, polarBilin Q' x y = 0) → x = 0 from
    ⟨hsep, fun y hy => hsep y fun x => by rw [hsymm]; exact hy x⟩
  by_cases h2 : ringChar K = 2
  ·
    have : CharP K 2 := ringChar.of_eq h2
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have hev : Even (finrank K V) := h.resolve_left (not_not.mpr h2)
    set R := LinearMap.ker (polarBilin Q') with hR
    have hmemR : ∀ x, x ∈ R ↔ ∀ y, polarBilin Q' x y = 0 := fun x => by
      rw [hR, LinearMap.mem_ker]
      exact ⟨fun hx y => by rw [hx, LinearMap.zero_apply], fun hx => LinearMap.ext hx⟩
    have hR1 : finrank K R ≤ 1 := by
      by_cases hR0 : ∃ x ∈ R, x ≠ 0
      · obtain ⟨x, hxR, hx0⟩ := hR0
        have hQx : Q x ≠ 0 := fun h0 => hx0 (hrad x ((hmemR x).mp hxR) h0)
        have hle : R ≤ K ∙ x := by
          intro y hyR
          obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q y / Q x)
          have hz : a • x + y ∈ R := add_mem (R.smul_mem a hxR) hyR
          have hQz : Q (a • x + y) = 0 := by
            have h1 := hpol (a • x) y
            rw [(hmemR (a • x)).mp (R.smul_mem a hxR) y, hQ.1] at h1
            have h3 : a * a * Q x = Q y := by rw [← ha, div_mul_cancel₀ _ hQx]
            linear_combination -h1 + h3 + Q y * h2K
          have hz0 := hrad _ ((hmemR _).mp hz) hQz
          rw [Submodule.mem_span_singleton]
          exact ⟨-a, by rw [neg_smul, neg_eq_iff_add_eq_zero]; exact hz0⟩
        calc finrank K R ≤ finrank K (K ∙ x) := Submodule.finrank_mono hle
          _ ≤ 1 := (finrank_span_singleton hx0).le
      · push Not at hR0
        rw [Submodule.finrank_eq_zero.mpr (eq_bot_iff.mpr fun x hx =>
          (Submodule.mem_bot K).mpr (hR0 x hx))]
        exact zero_le_one
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl R
    have hsum := Submodule.finrank_add_eq_of_isCompl hW
    set Bw := LinearMap.BilinForm.restrict (polarBilin Q') W with hBw
    have halt : Bw.IsAlt := fun w => by
      rw [hBw, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        polarBilin_apply_apply, polar_self, nsmul_eq_mul, Nat.cast_ofNat, h2K, zero_mul]
    have hsepW : ∀ w : W, (∀ w' : W, Bw w w' = 0) → w = 0 := by
      intro w hw
      have hwR : (w : V) ∈ R := (hmemR _).mpr fun v => by
        have hv : v ∈ R ⊔ W := hW.sup_eq_top ▸ Submodule.mem_top
        obtain ⟨r, hr, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add, hsymm, (hmemR r).mp hr, zero_add]
        exact hw ⟨w', hw'⟩
      have : (w : V) ∈ R ⊓ W := ⟨hwR, w.2⟩
      rw [hW.inf_eq_bot, Submodule.mem_bot] at this
      exact Subtype.ext this
    have hndW : Bw.Nondegenerate := ⟨hsepW, fun w hw => hsepW w fun w' => by
      rw [hBw, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hsymm]
      exact hw w'⟩
    have hWev : Even (finrank K W) := LinearMap.BilinForm.IsAlt.even_finrank halt hndW
    have hR0 : finrank K R = 0 := by
      have hRev : Even (finrank K R) := by
        rw [← hsum] at hev
        exact (Nat.even_add.mp hev).mpr hWev
      obtain ⟨k, hk⟩ := hRev
      omega
    intro x hx
    have hxR : x ∈ R := (hmemR x).mpr hx
    rw [Submodule.finrank_eq_zero.mp hR0] at hxR
    exact (Submodule.mem_bot K).mp hxR
  ·
    intro x hx
    refine hrad x hx ?_
    have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero h2
    have h1 := hx x
    rw [polarBilin_apply_apply, polar_self, nsmul_eq_mul, Nat.cast_ofNat] at h1
    exact (mul_eq_zero.mp h1).resolve_left h2K

theorem two_mul_finrank_le_of_singular [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V} (hW : ∀ x ∈ W, Q x = 0) :
    2 * finrank K W ≤ finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal hQ W
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
      change polarBilin Q y x = 0
      rw [polarBilin_apply_apply, QuadraticMap.polar, hW _ (add_mem hy hx), hW y hy, hW x hx,
        sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_le W
  omega

end Forms




section Witt

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem two_mul_sourceWittIndex_le [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) : 2 * sourceWittIndex ⇑Q ≤ finrank K V := by
  obtain ⟨W, hW, hWd⟩ := exists_sourceWittIndex (Q := ⇑Q) (QuadraticMap.map_zero Q)
  rw [← hWd]
  exact two_mul_finrank_le_of_singular hQ hW

theorem finrank_le_sourceWittIndex_of_injective [FiniteDimensional K V] {U : Type*}
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] (Q : V → K) (φ : U →ₗ[K] V)
    (hφ : Function.Injective φ) (h0 : ∀ u, Q (φ u) = 0) : finrank K U ≤ sourceWittIndex Q := by
  rw [← LinearMap.finrank_range_of_inj hφ]
  exact le_sourceWittIndex Q fun x ⟨u, hu⟩ => hu ▸ h0 u

theorem IsSourceQuadratic.isPlusType [FiniteDimensional K V] {Q : V → K}
    (hQ : IsSourceQuadratic Q) {n : ℕ} (hdim : finrank K V = 2 * n)
    (hw : sourceWittIndex Q = n) : IsPlusType hQ.toQuadraticForm := by
  obtain ⟨W, hW, hWd⟩ := exists_sourceWittIndex hQ.map_zero
  exact ⟨W, by rw [hWd, hw, hdim], hW⟩

theorem IsSourceQuadratic.not_isPlusType [FiniteDimensional K V] {Q : V → K}
    (hQ : IsSourceQuadratic Q) {n : ℕ} (hn : 1 ≤ n) (hdim : finrank K V = 2 * n)
    (hw : sourceWittIndex Q = n - 1) : ¬IsPlusType hQ.toQuadraticForm := by
  rintro ⟨W, hW, hWs⟩
  have := le_sourceWittIndex Q (W := W) hWs
  omega

end Witt

section Native

variable (n : ℕ) (K : Type) [Field K]

theorem sourceWittIndex_statedQuadPlus : sourceWittIndex (StatedQuadPlus n K) = n := by
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K
  have hdim : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  have h1 := two_mul_sourceWittIndex_le (quadPlus n K) hnd
  rw [coe_quadPlus, hdim] at h1
  obtain ⟨W, hW, hWs⟩ := CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K n
  have h2 := le_sourceWittIndex (StatedQuadPlus n K) (W := W) fun x hx => by
    rw [← coe_quadPlus]
    exact hWs x hx
  rw [hdim] at hW
  omega

@[expose] def oddHalf : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K) where
  toFun y := Sum.elim y 0
  map_add' _ _ := by
    funext j
    rcases j with i | i <;> simp
  map_smul' _ _ := by
    funext j
    rcases j with i | i <;> simp

@[expose] def minusHalf : (Fin (n - 1) → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun y := Sum.elim y 0
  map_add' _ _ := by
    funext j
    rcases j with i | i <;> simp
  map_smul' _ _ := by
    funext j
    rcases j with i | i <;> simp

theorem sourceWittIndex_statedQuadOdd (h2 : (2 : K) ≠ 0) :
    sourceWittIndex (StatedQuadOdd n K) = n := by
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K h2
  have hdim : finrank K (Fin n ⊕ Fin n ⊕ Unit → K) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have h1 := two_mul_sourceWittIndex_le (quadOdd n K) hnd
  rw [coe_quadOdd, hdim] at h1
  have h2' := finrank_le_sourceWittIndex_of_injective (StatedQuadOdd n K) (oddHalf n K)
    (fun x y hxy => funext fun i => congrFun hxy (.inl i)) fun y => by
      simp [StatedQuadOdd, oddHalf]
  rw [Module.finrank_fin_fun] at h2'
  omega

theorem sourceWittIndex_statedQuadMinus [Finite K] (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    sourceWittIndex (StatedQuadMinus n K b c) = n - 1 := by
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hdim : finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have h1 := two_mul_sourceWittIndex_le (quadMinus n K b c) hnd
  rw [coe_quadMinus, hdim] at h1
  have h2 := finrank_le_sourceWittIndex_of_injective (StatedQuadMinus n K b c) (minusHalf n K)
    (fun x y hxy => funext fun i => congrFun hxy (.inl i)) fun y => by
      simp [StatedQuadMinus, minusHalf]
  rw [Module.finrank_fin_fun] at h2
  by_contra hne
  have hw : sourceWittIndex (StatedQuadMinus n K b c) = n := by omega
  obtain ⟨W, hW, hWd⟩ := exists_sourceWittIndex (Q := StatedQuadMinus n K b c)
    (by rw [← coe_quadMinus]; exact QuadraticMap.map_zero _)
  apply CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn hirr
  refine ⟨W, by rw [hWd, hw, hdim], fun x hx => ?_⟩
  rw [coe_quadMinus]
  exact hW x hx

end Native

end CFSG.Blueprint.EvenSource
