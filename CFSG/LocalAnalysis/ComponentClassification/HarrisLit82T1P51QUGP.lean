module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutant
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QTrv

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {E : Type} [Field E]

theorem unitLambdaDiag_left {m : ℕ} (c : E) {i j : Fin m} :
    unitLambdaDiag c i j i = c := by
  simp [unitLambdaDiag]

theorem unitLambdaDiag_right {m : ℕ} (c : E) {i j : Fin m} (hij : i ≠ j) :
    unitLambdaDiag c i j j = c⁻¹ := by
  simp [unitLambdaDiag, Ne.symm hij]

theorem snd_eq_of_single {W : Type*} [AddCommGroup W] [Module E W] {s : ℕ}
    (g : W × (Fin s → E) →ₗ[E] W × (Fin s → E)) {a : E}
    (h : ∀ i, g (0, Pi.single i 1) = (0, Pi.single i a)) (v : Fin s → E) :
    g (0, v) = (0, a • v) := by
  have hv : ((0 : W), v) = ∑ i, v i • ((0 : W), (Pi.single i 1 : Fin s → E)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp
    · rw [Prod.snd_sum]
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp_rw [map_smul, h]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp
  · rw [Prod.snd_sum]
    funext k
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]

theorem prod_unitary_commutant {W : Type*} [AddCommGroup W] [Module E W] {s : ℕ}
    (hs : 2 ≤ s) {c : E} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcc : c * c ≠ 1)
    (g : W × (Fin s → E) →ₗ[E] W × (Fin s → E))
    (hd : ∀ i j : Fin s, i ≠ j → ∀ w : W × (Fin s → E),
      g (w.1, diagonal (unitLambdaDiag c i j) *ᵥ w.2) =
        ((g w).1, diagonal (unitLambdaDiag c i j) *ᵥ (g w).2))
    (hw : ∀ i j : Fin s, i ≠ j → ∀ w : W × (Fin s → E),
      g (w.1, unitSignedSwapMatrix i j *ᵥ w.2) = ((g w).1, unitSignedSwapMatrix i j *ᵥ (g w).2)) :
    (∃ a : E, ∀ v, g (0, v) = (0, a • v)) ∧ ∀ u, (g (u, 0)).2 = 0 := by
  have hc1' : (1 : E) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hcinv : c - c⁻¹ ≠ 0 := by
    intro h0
    apply hcc
    have h1 : c = c⁻¹ := sub_eq_zero.mp h0
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel₀ hc0
  refine ⟨?_, fun u => funext fun k => ?_⟩
  ·
    have hsingle : ∀ i : Fin s, g (0, Pi.single i 1) = (0, Pi.single i ((g (0, Pi.single i 1)).2 i))
        := by
      intro i
      obtain ⟨j, hji⟩ := exists_ne_of_two_le hs i
      have hD : ∀ j : Fin s,
          diagonal (unitLambdaDiag c i j) *ᵥ Pi.single i (1 : E) = c • Pi.single i 1 := by
        intro j
        funext k
        rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases hki : k = i
        · subst hki
          rw [unitLambdaDiag_left]
        · simp [hki]
      have hlin : g ((0 : W), c • (Pi.single i 1 : Fin s → E)) = c • g (0, Pi.single i 1) := by
        rw [← map_smul, Prod.smul_mk, smul_zero]
      refine Prod.ext ?_ (funext fun k => ?_)
      · have h1 := congrArg Prod.fst (hd i j (Ne.symm hji) (0, Pi.single i 1))
        simp only at h1
        rw [hD j, hlin, Prod.smul_fst] at h1
        have h2 : ((1 : E) - c) • (g (0, Pi.single i 1)).1 = 0 := by
          rw [sub_smul, one_smul, h1, sub_self]
        exact (smul_eq_zero.mp h2).resolve_left hc1'
      · by_cases hki : k = i
        · subst hki
          simp
        · have h1 := congrArg (fun p => p.2 k) (hd i k (Ne.symm hki) (0, Pi.single i 1))
          simp only at h1
          rw [hD k, hlin, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mulVec_diagonal,
            unitLambdaDiag_right c (Ne.symm hki)] at h1
          have h2 : (c - c⁻¹) * (g (0, Pi.single i 1)).2 k = 0 := by
            linear_combination h1
          rw [(mul_eq_zero.mp h2).resolve_left hcinv]
          simp [Pi.single_eq_of_ne hki]
    set a : Fin s → E := fun i => (g (0, Pi.single i 1)).2 i with hadef
    have heq : ∀ i j : Fin s, i ≠ j → a i = a j := by
      intro i j hij
      have h1 := hw i j hij (0, Pi.single i 1)
      simp only at h1
      rw [unitSignedSwapMatrix_mulVec, unitSignedSwap_single hij, hsingle j, hsingle i] at h1
      simp only [unitSignedSwapMatrix_mulVec, unitSignedSwap_single hij] at h1
      have h2 := congrArg (fun p => p.2 j) h1
      simpa [hadef] using h2.symm
    set i₀ : Fin s := ⟨0, by omega⟩
    have ha : ∀ i, g (0, Pi.single i 1) = (0, Pi.single i (a i₀)) := by
      intro i
      rw [hsingle i]
      by_cases hi : i = i₀
      · rw [hi]
      · rw [show (g (0, Pi.single i 1)).2 i = a i from rfl, heq i i₀ hi]
    exact ⟨a i₀, snd_eq_of_single g ha⟩
  ·
    obtain ⟨j, hjk⟩ := exists_ne_of_two_le hs k
    have h1 := congrArg (fun p => p.2 k) (hd k j (Ne.symm hjk) (u, 0))
    simp only [mulVec_zero, mulVec_diagonal, unitLambdaDiag_left] at h1
    have h2 : ((1 : E) - c) * (g (u, 0)).2 k = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left hc1'

theorem prod_unitary_commutant_fst {W : Type*} [AddCommGroup W] [Module E W] {r : ℕ}
    (hr : 2 ≤ r) {c : E} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcc : c * c ≠ 1)
    (g : (Fin r → E) × W →ₗ[E] (Fin r → E) × W)
    (hd : ∀ i j : Fin r, i ≠ j → ∀ w : (Fin r → E) × W,
      g (diagonal (unitLambdaDiag c i j) *ᵥ w.1, w.2) =
        (diagonal (unitLambdaDiag c i j) *ᵥ (g w).1, (g w).2))
    (hw : ∀ i j : Fin r, i ≠ j → ∀ w : (Fin r → E) × W,
      g (unitSignedSwapMatrix i j *ᵥ w.1, w.2) = (unitSignedSwapMatrix i j *ᵥ (g w).1, (g w).2)) :
    (∃ a : E, ∀ u, g (u, 0) = (a • u, 0)) ∧ ∀ v, (g (0, v)).1 = 0 := by
  let sw : ((Fin r → E) × W) ≃ₗ[E] (W × (Fin r → E)) := LinearEquiv.prodComm E (Fin r → E) W
  let G : (W × (Fin r → E)) →ₗ[E] (W × (Fin r → E)) :=
    sw.toLinearMap ∘ₗ g ∘ₗ sw.symm.toLinearMap
  have hG : ∀ w, G w = ((g (w.2, w.1)).2, (g (w.2, w.1)).1) := fun _ => rfl
  obtain ⟨⟨a, ha⟩, h2⟩ := prod_unitary_commutant hr hc0 hc1 hcc G
    (fun i j hij w => by rw [hG, hG]; simp only [hd i j hij (w.2, w.1)])
    (fun i j hij w => by rw [hG, hG]; simp only [hw i j hij (w.2, w.1)])
  refine ⟨⟨a, fun u => ?_⟩, fun v => ?_⟩
  · have := ha u
    rw [hG] at this
    exact Prod.ext (congrArg Prod.snd this) (congrArg Prod.fst this)
  · have := h2 v
    rw [hG] at this
    exact this

theorem prod_twisted_commutant {m : ℕ} (hm : 2 ≤ m) (σ : E →+* E) {t₀ : E} (ht₀ : σ t₀ ≠ t₀)
    (g : (Fin m → E) × (Fin m → E) →ₗ[E] (Fin m → E) × (Fin m → E))
    (hT : ∀ i j : Fin m, i ≠ j → ∀ (t : E) (w : (Fin m → E) × (Fin m → E)),
      g (transvection i j t *ᵥ w.1, transvection j i (-σ t) *ᵥ w.2) =
        (transvection i j t *ᵥ (g w).1, transvection j i (-σ t) *ᵥ (g w).2)) :
    ∃ α β : E, ∀ w, g w = (α • w.1, β • w.2) := by
  have key : ∀ i j : Fin m, i ≠ j → ∀ (t : E) (w : (Fin m → E) × (Fin m → E)),
      g (Pi.single i (t * w.1 j), Pi.single j (-σ t * w.2 i)) =
        (Pi.single i (t * (g w).1 j), Pi.single j (-σ t * (g w).2 i)) := by
    intro i j hij t w
    have h1 := hT i j hij t w
    rw [transvection_mulVec, transvection_mulVec, transvection_mulVec, transvection_mulVec] at h1
    have h2 : (w.1 + Pi.single i (t * w.1 j), w.2 + Pi.single j (-σ t * w.2 i)) =
        w + (Pi.single i (t * w.1 j), Pi.single j (-σ t * w.2 i)) := by ext <;> simp
    have h3 : ((g w).1 + Pi.single i (t * (g w).1 j), (g w).2 + Pi.single j (-σ t * (g w).2 i)) =
        g w + (Pi.single i (t * (g w).1 j), Pi.single j (-σ t * (g w).2 i)) := by ext <;> simp
    rw [h2, h3, map_add] at h1
    exact add_left_cancel h1
  have hst : σ t₀ - t₀ ≠ 0 := sub_ne_zero.mpr ht₀
  have hfst : ∀ i : Fin m, g (Pi.single i 1, 0) =
      (Pi.single i ((g (Pi.single i 1, 0)).1 i), 0) := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne_of_two_le hm i
    have hk : ∀ t : E, g (Pi.single i t, 0) = (Pi.single i (t * (g (Pi.single j 1, 0)).1 j),
        Pi.single j (-σ t * (g (Pi.single j 1, 0)).2 i)) := by
      intro t
      have := key i j (Ne.symm hji) t (Pi.single j 1, 0)
      simpa using this
    have hlin : ∀ t : E, g (Pi.single i t, 0) = t • g (Pi.single i 1, 0) := by
      intro t
      rw [← map_smul, Prod.smul_mk, smul_zero, ← Pi.single_smul, smul_eq_mul, mul_one]
    have hY : (g (Pi.single j 1, 0)).2 i = 0 := by
      have h1 := congrArg (fun p => p.2 j) ((hlin t₀).symm.trans (hk t₀))
      have h2 := congrArg (fun p => p.2 j) (hk 1)
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, map_one]
        at h1 h2
      rw [h2] at h1
      have h3 : (σ t₀ - t₀) * (g (Pi.single j 1, 0)).2 i = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h3).resolve_left hst
    have h1 := hk 1
    rw [hY, mul_zero, Pi.single_zero, one_mul] at h1
    rw [h1]
    simp
  set α : Fin m → E := fun i => (g (Pi.single i 1, 0)).1 i
  have hsnd : ∀ j : Fin m, g (0, Pi.single j 1) =
      (0, Pi.single j ((g (0, Pi.single j 1)).2 j)) := by
    intro j
    obtain ⟨i, hij⟩ := exists_ne_of_two_le hm j
    have hk : ∀ t : E, g (0, Pi.single j (-σ t)) = (Pi.single i (t * (g (0, Pi.single i 1)).1 j),
        Pi.single j (-σ t * (g (0, Pi.single i 1)).2 i)) := by
      intro t
      have := key i j hij t (0, Pi.single i 1)
      simpa using this
    have hlin : ∀ t : E, g (0, Pi.single j t) = t • g (0, Pi.single j 1) := by
      intro t
      rw [← map_smul, Prod.smul_mk, smul_zero, ← Pi.single_smul, smul_eq_mul, mul_one]
    have hX : (g (0, Pi.single i 1)).1 j = 0 := by
      have h1 := congrArg (fun p => p.1 i) ((hlin (-σ t₀)).symm.trans (hk t₀))
      have h2 := congrArg (fun p => p.1 i) ((hlin (-σ 1)).symm.trans (hk 1))
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, map_one]
        at h1 h2
      have h4 : (g (0, Pi.single j 1)).1 i = (g (0, Pi.single i 1)).1 j * -1 := by
        linear_combination -h2
      rw [h4] at h1
      have h3 : (σ t₀ - t₀) * (g (0, Pi.single i 1)).1 j = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h3).resolve_left hst
    have h1 : (-1 : E) • g (0, Pi.single j 1) =
        (0, Pi.single j (-1 * (g (0, Pi.single i 1)).2 i)) := by
      rw [← hlin (-1)]
      have := hk 1
      rw [hX, mul_zero, Pi.single_zero, map_one] at this
      exact this
    have h2 : g (0, Pi.single j 1) = (0, Pi.single j ((g (0, Pi.single i 1)).2 i)) := by
      have := congrArg (fun x => (-1 : E) • x) h1
      simpa [smul_smul, Pi.single_neg] using this
    rw [h2]
    simp
  set β : Fin m → E := fun j => (g (0, Pi.single j 1)).2 j
  have hα : ∀ i j : Fin m, i ≠ j → α i = α j := by
    intro i j hij
    have := key i j hij 1 (Pi.single j 1, 0)
    simp only [Pi.single_eq_same, mul_one, Pi.zero_apply, mul_zero, Pi.single_zero, one_mul]
      at this
    rw [hfst j] at this
    have h1 := congrArg (fun p => p.1 i) this
    rw [hfst i] at h1
    simpa [α] using h1
  have hβ : ∀ i j : Fin m, i ≠ j → β i = β j := by
    intro i j hij
    have := key i j hij 1 (0, Pi.single i 1)
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero, Pi.single_eq_same, mul_one,
      map_one] at this
    rw [hsnd i] at this
    have h1 := congrArg (fun p => p.2 j) this
    rw [show g (0, Pi.single j (-1)) = (-1 : E) • g (0, Pi.single j 1) by
      rw [← map_smul, Prod.smul_mk, smul_zero, ← Pi.single_smul, smul_eq_mul, mul_one],
      hsnd j] at h1
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h1
    simp only [β]
    linear_combination h1
  set i₀ : Fin m := ⟨0, by omega⟩
  have hαc : ∀ i, α i = α i₀ := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
    · exact hα i i₀ hi
  have hβc : ∀ j, β j = β i₀ := fun j => by
    by_cases hj : j = i₀
    · rw [hj]
    · exact hβ j i₀ hj
  refine ⟨α i₀, β i₀, fun w => ?_⟩
  have hw : w = (w.1, 0) + (0, w.2) := by simp
  have h1 : g (0, w.2) = (0, β i₀ • w.2) :=
    snd_eq_of_single g (fun j => by rw [hsnd j]; exact Prod.ext rfl (by rw [← hβc j])) w.2
  have h2 : g (w.1, 0) = (α i₀ • w.1, 0) := by
    let sw : ((Fin m → E) × (Fin m → E)) ≃ₗ[E] ((Fin m → E) × (Fin m → E)) :=
      LinearEquiv.prodComm E (Fin m → E) (Fin m → E)
    have h3 := snd_eq_of_single (sw.toLinearMap ∘ₗ g ∘ₗ sw.toLinearMap) (a := α i₀)
      (fun i => by
        change sw (g (Pi.single i 1, 0)) = _
        rw [hfst i]
        exact Prod.ext rfl (by
          change (Pi.single i (α i) : Fin m → E) = Pi.single i (α i₀)
          rw [hαc i])) w.1
    have h4 := congrArg sw h3
    change sw (sw (g (sw (0, w.1)))) = sw (0, α i₀ • w.1) at h4
    simpa [sw] using h4
  rw [hw, map_add, h1, h2]
  simp

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
