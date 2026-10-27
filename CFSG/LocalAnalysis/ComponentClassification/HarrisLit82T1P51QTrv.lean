module

public import Mathlib.LinearAlgebra.Matrix.Transvection

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix

theorem transvection_mulVec {E : Type*} [Field E] {s : ℕ} (i j : Fin s) (t : E)
    (v : Fin s → E) : transvection i j t *ᵥ v = v + Pi.single i (t * v j) := by
  rw [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem exists_ne_of_two_le {s : ℕ} (hs : 2 ≤ s) (j : Fin s) : ∃ i : Fin s, i ≠ j := by
  by_cases h : (j : ℕ) = 0
  · exact ⟨⟨1, by omega⟩, fun h' => by
      have := congrArg Fin.val h'
      simp only at this
      omega⟩
  · exact ⟨⟨0, by omega⟩, fun h' => h (congrArg Fin.val h').symm⟩

theorem prod_transvection_commutant {W E : Type*} [AddCommGroup W] [Field E] {s : ℕ}
    (hs : 2 ≤ s) (g : W × (Fin s → E) →+ W × (Fin s → E))
    (hg : ∀ i j : Fin s, i ≠ j → ∀ (t : E) (w : W × (Fin s → E)),
      g (w.1, transvection i j t *ᵥ w.2) = ((g w).1, transvection i j t *ᵥ (g w).2)) :
    (∃ c : E, ∀ v, g (0, v) = (0, c • v)) ∧ ∀ u, (g (u, 0)).2 = 0 := by
  have key : ∀ i j : Fin s, i ≠ j → ∀ (t : E) (w : W × (Fin s → E)),
      g (0, Pi.single i (t * w.2 j)) = (0, Pi.single i (t * (g w).2 j)) := by
    intro i j hij t w
    have h1 := hg i j hij t w
    rw [transvection_mulVec, transvection_mulVec] at h1
    have h2 : (w.1, w.2 + Pi.single i (t * w.2 j)) = w + (0, Pi.single i (t * w.2 j)) := by
      ext <;> simp
    have h3 : ((g w).1, (g w).2 + Pi.single i (t * (g w).2 j)) =
        g w + (0, Pi.single i (t * (g w).2 j)) := by
      ext <;> simp
    rw [h2, h3, map_add] at h1
    exact add_left_cancel h1
  refine ⟨?_, fun u => funext fun j => ?_⟩
  · set c : Fin s → E := fun j => (g (0, Pi.single j 1)).2 j with hc
    have h1 : ∀ i j : Fin s, i ≠ j → ∀ t : E,
        g (0, Pi.single i t) = (0, Pi.single i (t * c j)) := by
      intro i j hij t
      have := key i j hij t (0, Pi.single j 1)
      simpa only [Pi.single_eq_same, mul_one] using this
    have h2 : ∀ i j : Fin s, i ≠ j → c i = c j := by
      intro i j hij
      change (g (0, Pi.single i 1)).2 i = c j
      rw [h1 i j hij 1]
      simp
    set j₀ : Fin s := ⟨0, by omega⟩
    have hc0 : ∀ j : Fin s, c j = c j₀ := fun j => by
      by_cases hj : j = j₀
      · rw [hj]
      · exact h2 j j₀ hj
    have h3 : ∀ i : Fin s, ∀ t : E, g (0, Pi.single i t) = (0, Pi.single i (t * c j₀)) := by
      intro i t
      obtain ⟨j, hj⟩ := exists_ne_of_two_le hs i
      rw [h1 i j (Ne.symm hj) t, hc0 j]
    refine ⟨c j₀, fun v => ?_⟩
    have hv : ((0 : W), v) = ∑ i, ((0 : W), Pi.single i (v i)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        simp
      · rw [Prod.snd_sum, Finset.univ_sum_single]
    rw [hv, map_sum]
    simp_rw [h3]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp
    · rw [Prod.snd_sum]
      funext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  · obtain ⟨i, hij⟩ := exists_ne_of_two_le hs j
    have := key i j hij 1 (u, 0)
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero, Prod.mk_zero_zero, map_zero,
      one_mul] at this
    have h0 := congrArg (fun p : W × (Fin s → E) => p.2 i) this
    simpa using h0.symm

theorem prod_transvection_commutant_fst {W E : Type*} [AddCommGroup W] [Field E] {r : ℕ}
    (hr : 2 ≤ r) (g : (Fin r → E) × W →+ (Fin r → E) × W)
    (hg : ∀ i j : Fin r, i ≠ j → ∀ (t : E) (w : (Fin r → E) × W),
      g (transvection i j t *ᵥ w.1, w.2) = (transvection i j t *ᵥ (g w).1, (g w).2)) :
    (∃ c : E, ∀ u, g (u, 0) = (c • u, 0)) ∧ ∀ v, (g (0, v)).1 = 0 := by
  let sw : (Fin r → E) × W ≃+ W × (Fin r → E) := AddEquiv.prodComm
  let G : W × (Fin r → E) →+ W × (Fin r → E) :=
    sw.toAddMonoidHom.comp (g.comp sw.symm.toAddMonoidHom)
  have hG : ∀ w, G w = ((g (w.2, w.1)).2, (g (w.2, w.1)).1) := fun _ => rfl
  obtain ⟨⟨c, hc⟩, h2⟩ := prod_transvection_commutant hr G (fun i j hij t w => by
    rw [hG, hG]
    have := hg i j hij t (w.2, w.1)
    simp only at this
    rw [this])
  refine ⟨⟨c, fun u => ?_⟩, fun v => ?_⟩
  · have := hc u
    rw [hG] at this
    exact Prod.ext (congrArg Prod.snd this) (congrArg Prod.fst this)
  · have := h2 v
    rw [hG] at this
    exact this

theorem linear_fin_le_one {K : Type*} [Field K] {r : ℕ} (hr : r ≤ 1)
    (φ : (Fin r → K) →ₗ[K] (Fin r → K)) : ∃ c : K, ∀ u, φ u = c • u := by
  rcases Nat.lt_or_ge r 1 with h | h
  · obtain rfl : r = 0 := by omega
    exact ⟨0, fun u => funext fun i => i.elim0⟩
  · obtain rfl : r = 1 := by omega
    refine ⟨φ (fun _ => 1) 0, fun u => ?_⟩
    have hu : u = u 0 • (fun _ => 1 : Fin 1 → K) := funext fun i => by
      rw [Subsingleton.elim i 0]
      simp
    rw [hu, map_smul]
    funext i
    rw [Subsingleton.elim i 0]
    simp [mul_comm]

theorem transvection_commutant {E : Type*} [Field E] {m : ℕ} (hm : 2 ≤ m)
    (g : (Fin m → E) →+ (Fin m → E))
    (hg : ∀ i j : Fin m, i ≠ j → ∀ (t : E) (w : Fin m → E),
      g (transvection i j t *ᵥ w) = transvection i j t *ᵥ g w) :
    ∃ c : E, ∀ v, g v = c • v := by
  let G : Unit × (Fin m → E) →+ Unit × (Fin m → E) :=
    (AddMonoidHom.inr Unit (Fin m → E)).comp (g.comp (AddMonoidHom.snd Unit (Fin m → E)))
  obtain ⟨⟨c, hc⟩, -⟩ := prod_transvection_commutant hm G (fun i j hij t w => by
    simp only [G, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_snd,
      AddMonoidHom.inr_apply, hg i j hij t w.2])
  exact ⟨c, fun v => congrArg Prod.snd (hc v)⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
