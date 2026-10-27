module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Subgroup CFSG.Open

variable {K : Type} [Field K]

theorem torusHom_diag_injective_sp4 [CharP K 2] {t : Fin 2 → Kˣ} (h0 : t 0 ≠ 1) (h1 : t 1 ≠ 1)
    (h01 : t 0 ≠ t 1) (h01' : t 0 ≠ (t 1)⁻¹) :
    Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) := by
  have hinv : ∀ u : Kˣ, u ≠ 1 → u ≠ u⁻¹ := fun u hu h =>
    hu (((Units.inv_eq_self_iff u).mp h.symm).resolve_right fun h' =>
      hu (h'.trans (Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq]))))
  have h00 : t 0 ≠ (t 0)⁻¹ := hinv _ h0
  have h11 : t 1 ≠ (t 1)⁻¹ := hinv _ h1
  have h10' : t 1 ≠ (t 0)⁻¹ := fun h => h01' (by rw [h, inv_inv])
  have hU : Function.Injective (Sum.elim t fun i => (t i)⁻¹ : Fin 2 ⊕ Fin 2 → Kˣ) := by
    rintro (a | a) (b | b) h <;> fin_cases a <;> fin_cases b <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.isValue, Fin.mk_one,
        inv_inj] at h <;>
      first
        | rfl
        | exact absurd h h01 | exact absurd h.symm h01
        | exact absurd h h00 | exact absurd h.symm h00
        | exact absurd h h11 | exact absurd h.symm h11
        | exact absurd h h01' | exact absurd h.symm h01'
        | exact absurd h h10' | exact absurd h.symm h10'
  have hc : (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) =
      Units.val ∘ (Sum.elim t fun i => (t i)⁻¹ : Fin 2 ⊕ Fin 2 → Kˣ) := by
    funext x
    rcases x with x | x <;> rfl
  rw [hc]
  exact Units.val_injective.comp hU

theorem mem_torus_of_commute_torusHom_sp4 {t : Fin 2 → Kˣ}
    (hinj : Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)))
    {y : StatedSp 2 K} (hy : y * torusHom t = torusHom t * y) : y ∈ torus 2 K := by
  have hcomm : Matrix.diagonal (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) *
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        Matrix.diagonal (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) := by
    have h := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hy
    simp only [coe_mul_statedSp, coe_torusHom] at h
    exact h.symm
  have hdiag : ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.diagonal fun x =>
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x x := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm (hinj.ne hab)
  have hsp := mem_statedSp_iff.mp y.2
  have hprod : ∀ i,
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          (Sum.inl i) (Sum.inl i) *
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun hsp (Sum.inl i)) (Sum.inr i)
    rw [hdiag, Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  refine ⟨fun i => Units.mkOfMulEqOne _ _ (hprod i), statedSp_ext ?_⟩
  rw [coe_torusHom]
  refine (congrArg Matrix.diagonal ?_).trans hdiag.symm
  funext x
  rcases x with i | i <;> rfl

theorem centralizer_torusHom_eq_torus_sp4 {t : Fin 2 → Kˣ}
    (hinj : Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K))) :
    centralizer ({torusHom t} : Set (StatedSp 2 K)) = torus 2 K := by
  apply le_antisymm
  · intro y hy
    rw [mem_centralizer_singleton_iff] at hy
    exact mem_torus_of_commute_torusHom_sp4 hinj hy
  · rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mul_comm]

theorem exists_regular_torus_sp4 [Finite K] [CharP K 2] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrd : r ∣ Nat.card K - 1) :
    ∃ y : StatedSp 2 K, centralizer ({y} : Set (StatedSp 2 K)) = torus 2 K ∧
      orderOf y = r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hpow : ∀ k : ℕ, ζ ^ k = 1 ↔ r ∣ k := fun k => by rw [← hζ, orderOf_dvd_iff_pow_eq_one]
  have hζ1 : ζ ≠ 1 := fun h => hr.one_lt.ne' (by rw [← hζ, h, orderOf_one])
  have hζ2 : ζ ^ 2 ≠ 1 := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp ((hpow 2).mp h))
  have hζ3 : ζ ^ 3 ≠ 1 := fun h =>
    hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp ((hpow 3).mp h))
  refine ⟨torusHom ![ζ, ζ ^ 2],
    centralizer_torusHom_eq_torus_sp4 (torusHom_diag_injective_sp4 ?_ ?_ ?_ ?_), ?_⟩
  · simpa using hζ1
  · simpa using hζ2
  · show ζ ≠ ζ ^ 2
    intro h
    apply hζ1
    have h' : ζ * 1 = ζ * ζ := by rw [mul_one, ← sq]; exact h
    exact (mul_left_cancel h').symm
  · show ζ ≠ (ζ ^ 2)⁻¹
    intro h
    apply hζ3
    calc ζ ^ 3 = ζ * ζ ^ 2 := by group
      _ = (ζ ^ 2)⁻¹ * ζ ^ 2 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  · have hζr : ζ ^ r = 1 := (hpow r).mpr dvd_rfl
    have ht : (![ζ, ζ ^ 2] : Fin 2 → Kˣ) ^ r = 1 := by
      funext i
      fin_cases i
      · exact hζr
      · show (ζ ^ 2) ^ r = 1
        rw [← pow_mul, mul_comm, pow_mul, hζr, one_pow]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ht, map_one]
    · intro h1
      have h2 : (![ζ, ζ ^ 2] : Fin 2 → Kˣ) = 1 :=
        torusHom_injective (r := 2) (k := K) (by rw [h1, map_one])
      have h3 := congrFun h2 0
      simp only [Fin.isValue, Matrix.cons_val_zero, Pi.one_apply] at h3
      exact hζ1 h3

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
