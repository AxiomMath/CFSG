module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section Unipotent

variable {K : Type*} [Field K]

@[expose] def upperUnipotent (a : K) : SL(2, K) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
theorem coe_upperUnipotent (a : K) :
    (upperUnipotent a : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1] :=
  rfl

@[expose] def lowerUnipotent (b : K) : SL(2, K) :=
  ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
theorem coe_lowerUnipotent (b : K) :
    (lowerUnipotent b : Matrix (Fin 2) (Fin 2) K) = !![1, 0; b, 1] :=
  rfl

theorem upperUnipotent_mul (a b : K) :
    upperUnipotent a * upperUnipotent b = upperUnipotent (a + b) := by
  apply Subtype.ext
  simp [add_comm]

theorem upperUnipotent_zero : upperUnipotent (0 : K) = 1 := by
  apply Subtype.ext
  simp [Matrix.one_fin_two]

def upperUnipotentHom : Multiplicative K →* SL(2, K) where
  toFun a := upperUnipotent (Multiplicative.toAdd a)
  map_one' := upperUnipotent_zero
  map_mul' a b := (upperUnipotent_mul (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm

theorem eq_zero_of_upperUnipotent_mem_center {a : K}
    (h : upperUnipotent a ∈ Subgroup.center SL(2, K)) : a = 0 := by
  have hcomm := Subgroup.mem_center_iff.mp h (lowerUnipotent 1)
  have h00 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hcomm
  simpa [Matrix.mul_fin_two] using h00

def pslUnipotentHom : Multiplicative K →* PSL(2, K) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, K))).comp upperUnipotentHom

theorem pslUnipotentHom_injective : Function.Injective (pslUnipotentHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hcentral : upperUnipotent (Multiplicative.toAdd a) ∈ Subgroup.center SL(2, K) :=
    (QuotientGroup.eq_one_iff _).1 ha
  exact toAdd_eq_zero.1 (eq_zero_of_upperUnipotent_mem_center hcentral)

theorem pslUnipotentHom_pow_prime (p : ℕ) [CharP K p] (a : Multiplicative K) :
    pslUnipotentHom a ^ p = 1 := by
  have hpow : a ^ p = 1 := by
    rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [← map_pow, hpow, map_one]

end Unipotent

theorem le_pRank_psl_two (p m : ℕ) [Fact p.Prime] (hm : m ≠ 0) :
    m ≤ CFSG.Open.pRank p (⊤ : Subgroup PSL(2, GaloisField p m)) := by
  have hp : p.Prime := Fact.out
  have hinj := pslUnipotentHom_injective (K := GaloisField p m)
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove p hp.one_lt _)
    ⟨(pslUnipotentHom (K := GaloisField p m)).range, le_top, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact pslUnipotentHom_pow_prime p a
  · calc
      Nat.card (pslUnipotentHom (K := GaloisField p m)).range
          = Nat.card (Multiplicative (GaloisField p m)) :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ = Nat.card (GaloisField p m) := Nat.card_congr Multiplicative.toAdd
      _ = p ^ m := GaloisField.card p m hm

end CFSG.LocalAnalysis.RankThreeTheoremC
