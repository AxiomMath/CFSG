module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU2Torus
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Curtis.Coordinator

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f n : ℕ} {F : Type} [Field F] [Finite F] {h : UnitaryFieldData ℓ f F}

omit [Finite F] in
theorem primeFormConjHom_torus (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    (y' : primeFormUnitary h (idGram F n))
    (hy' : ((y' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (a : Fin 3 → Fˣ) :
    primeFormConjHom h (idGram F n) y'
        (torusSU (n := n) h hq (by omega) a : primeFormP h (idGram F n)) =
      (torusSU (n := n) h hq (by omega) a : primeFormP h (idGram F n)) := by
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (y' : GL (Fin n) F) * (torusSU (n := n) h hq (by omega) a : GL (Fin n) F) *
    (y' : GL (Fin n) F)⁻¹ = (torusSU (n := n) h hq (by omega) a : GL (Fin n) F)
  have hc : (y' : GL (Fin n) F) * (torusSU (n := n) h hq (by omega) a : GL (Fin n) F) =
      (torusSU (n := n) h hq (by omega) a : GL (Fin n) F) * y' := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_torusSU, ← hy'.diagonal_diag,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hc, mul_inv_cancel_right]

theorem exists_torus_fixed (hq : ℓ ^ f = 2) (hn : 5 ≤ n) (y' : primeFormUnitary h (idGram F n))
    (hy' : ((y' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) :
    ∃ Q : Subgroup (primeFormP h (idGram F n)),
      (∀ x ∈ Q, primeFormConjHom h (idGram F n) y' x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q := by
  set φ := (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram F n)) n)).comp
    (torusSU h hq (by omega : 4 ≤ n)) with hφ
  have hinj : Function.Injective φ := torus_injective h hq hn
  have hcard : Nat.card φ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp [card_units_eq_three_of_pow_eq_two h hq]
  refine ⟨φ.range, ?_, ?_, hcard.ge⟩
  · rintro _ ⟨a, rfl⟩
    exact primeFormConjHom_torus hq hn y' hy' a
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (IsPGroup.iff_card).2 ⟨3, by rw [hcard]; norm_num⟩

theorem unitary_two_diag_false (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (hn : n = 6 ∨ n = 9)
    (y : primeFormUnitary h (idGram F n)) (c : Fˣ)
    (hyc : (y : GL (Fin n) F) ^ 3 = GeneralLinearGroup.scalar (Fin n) c) :
    (∃ R : Subgroup (primeFormP h (idGram F n)),
      (∀ x ∈ R, primeFormConjHom h (idGram F n) y x = x) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R) ∨
    (∃ Q : Subgroup (primeFormP h (idGram F n)),
      (∀ x ∈ Q, primeFormConjHom h (idGram F n) y x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q) := by
  by_cases hc : c = 1
  · right
    subst hc
    have hn5 : 5 ≤ n := by omega
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hyc, map_one, Subgroup.coe_one]
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three
      (by rw [hq]) (Subgroup.zpowers y)
      (fun x hx z hz => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact (Commute.zpow_zpow_self y k m).eq)
      (fun x hx => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hy3,
          _root_.one_zpow])
    obtain ⟨Q', hQ'fix, hQ'p, hQ'card⟩ := exists_torus_fixed (h := h) hq hn5 (P⁻¹ * y * P)
      (hP y (Subgroup.mem_zpowers y))
    have hinj : Function.Injective (primeFormConjHom h (idGram F n) P).toMonoidHom :=
      (primeFormConjHom h (idGram F n) P).injective
    have hcard : Nat.card (Q'.map (primeFormConjHom h (idGram F n) P).toMonoidHom) =
        Nat.card Q' := Subgroup.card_map_of_injective hinj
    refine ⟨Q'.map (primeFormConjHom h (idGram F n) P).toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨x', hx', rfl⟩
      have key : ∀ y' : primeFormUnitary h (idGram F n), y * P = P * y' →
          primeFormConjHom h (idGram F n) y (primeFormConjHom h (idGram F n) P x') =
            primeFormConjHom h (idGram F n) P (primeFormConjHom h (idGram F n) y' x') := by
        intro y' hmul
        have := congrArg (fun g => primeFormConjHom h (idGram F n) g x') hmul
        simpa only [map_mul, MulAut.mul_apply] using this
      change primeFormConjHom h (idGram F n) y (primeFormConjHom h (idGram F n) P x') =
        primeFormConjHom h (idGram F n) P x'
      rw [key (P⁻¹ * y * P) (by group), hQ'fix x' hx']
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ'p
      exact (IsPGroup.iff_card).2 ⟨k, by rw [hcard, hk]⟩
    · rw [hcard]
      exact hQ'card
  · left
    obtain ⟨R, hR, hperf, h3⟩ := exists_perfect_three_dvd_autFix_of_unitary_two hq hn y c hc hyc
    exact ⟨R, fun x hx => (mem_autFix _ _).1 (hR hx), hperf, h3⟩

end CFSG.HardMathSupport.Malle.E27Lie
