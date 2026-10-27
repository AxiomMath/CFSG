module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Local.GeneralLinearTwoPrimeFieldOrder
public import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Eigenspace.Zero

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module LinearMap Submodule

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
variable {Q : Type*} [Group Q]

private theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {N : R} (hN : N * N = 0)
    (k : ℕ) : (1 + N) ^ k = 1 + k • N := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsucc : (k + 1) • N = k • N + N := succ_nsmul N k
      have h : (1 + k • N) * (1 + N) = 1 + (k • N + N) + k • (N * N) := by
        simp only [nsmul_eq_mul]; noncomm_ring
      rw [pow_succ, ih, h, hN, smul_zero, add_zero, hsucc]

private theorem finiteDimensional_of_finrank_eq_two (hV : finrank (ZMod p) V = 2) :
    FiniteDimensional (ZMod p) V :=
  FiniteDimensional.of_finrank_pos (by rw [hV]; norm_num)

private theorem charP_end_of_finrank_eq_two (hV : finrank (ZMod p) V = 2) :
    CharP (Module.End (ZMod p) V) p := by
  have := finiteDimensional_of_finrank_eq_two hV
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hV]; norm_num)
  refine charP_of_injective_algebraMap (R := ZMod p) (A := Module.End (ZMod p) V) ?_ p
  intro a b hab
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : a • v = b • v := by
    have := congrArg (fun f : Module.End (ZMod p) V => f v) hab
    simpa [Module.algebraMap_end_apply] using this
  rcases smul_eq_zero.1 (show (a - b) • v = 0 by rw [sub_smul, h, sub_self]) with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hv

private theorem finite_generalLinearGroup (hV : finrank (ZMod p) V = 2) :
    Finite (LinearMap.GeneralLinearGroup (ZMod p) V) := by
  have := finiteDimensional_of_finrank_eq_two hV
  have : Finite V := Module.finite_of_finite (ZMod p) (M := V)
  have : Finite (V →ₗ[ZMod p] V) :=
    Finite.of_injective (fun f => (f : V → V)) fun f g h => by ext v; exact congrFun h v
  infer_instance

theorem card_generalLinearGroup_eq_card_GL_two (hV : finrank (ZMod p) V = 2) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod p) V) = Nat.card (GL (Fin 2) (ZMod p)) := by
  have := finiteDimensional_of_finrank_eq_two hV
  exact (Nat.card_congr
    (Matrix.GeneralLinearGroup.toLin' (finBasisOfFinrankEq (ZMod p) V hV)).toEquiv).symm

theorem card_range_eq_one_or_eq_prime (hV : finrank (ZMod p) V = 2) (hQ : IsPGroup p Q)
    (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V) :
    Nat.card ρ.range = 1 ∨ Nat.card ρ.range = p := by
  have := finite_generalLinearGroup (V := V) hV
  have hpg : IsPGroup p ρ.range :=
    IsPGroup.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective (hG := hQ)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hpg
  have hdvd : p ^ n ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
    rw [← card_generalLinearGroup_eq_card_GL_two (V := V) hV, ← hn]
    exact natCard_range_dvd_natCard_codomain ρ
  have hle : n ≤ 1 := (pow_dvd_card_GL_two_zmod_iff p).1 hdvd
  interval_cases n
  · left; simpa using hn
  · right; simpa using hn

theorem exists_sq_eq_zero_range_coe_eq (hV : finrank (ZMod p) V = 2)
    (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V) (hcard : Nat.card ρ.range = p) :
    ∃ N : Module.End (ZMod p) V, N ≠ 0 ∧ N * N = 0 ∧
      (Set.range fun q : Q => (ρ q : Module.End (ZMod p) V))
        = Set.range fun c : ZMod p => 1 + c • N := by
  have hfd := finiteDimensional_of_finrank_eq_two hV
  have hchar := charP_end_of_finrank_eq_two hV
  have hfin : Finite ρ.range :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.out.ne_zero)
  have hntriv : Nontrivial ρ.range := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; exact hp.out.one_lt
  obtain ⟨J, hJ⟩ := exists_ne (1 : ρ.range)
  set A : Module.End (ZMod p) V :=
    ((J : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V) with hA
  have hAne : A ≠ 1 := fun h => hJ (Subtype.ext (Units.ext h))
  set N : Module.End (ZMod p) V := A - 1 with hNdef
  have hJp : (J : ρ.range) ^ p = 1 := by
    have h := pow_card_eq_one' (x := J); rwa [hcard] at h
  have hAp : A ^ p = 1 := by
    have h := congrArg (fun x : ρ.range =>
      ((x : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)) hJp
    simpa [hA] using h
  have hNp : N ^ p = 0 := by
    rw [hNdef, sub_pow_char_of_commute (R := Module.End (ZMod p) V) p (Commute.one_right A),
      hAp, one_pow, sub_self]
  have hN2 : N * N = 0 := by
    have h := (LinearMap.isNilpotent_iff_charpoly (R := ZMod p) (M := V) N).1 ⟨p, hNp⟩
    have h2 := LinearMap.aeval_self_charpoly N
    rw [h, hV] at h2
    simpa [pow_two] using h2
  have hAN : A = 1 + N := by rw [hNdef]; abel
  refine ⟨N, sub_ne_zero.2 hAne, hN2, ?_⟩
  ext f
  simp only [Set.mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨n, hn⟩ : (⟨ρ q, ⟨q, rfl⟩⟩ : ρ.range) ∈ Submonoid.powers J :=
      mem_powers_of_prime_card hcard hJ
    refine ⟨(n : ZMod p), ?_⟩
    have h := congrArg (fun x : ρ.range =>
      ((x : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)) hn
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] at h
    rw [← h, ← hA, hAN, one_add_pow_of_mul_self_eq_zero hN2 n,
      Nat.cast_smul_eq_nsmul (ZMod p) n N]
  · rintro ⟨c, rfl⟩
    obtain ⟨q, hq⟩ : (J : LinearMap.GeneralLinearGroup (ZMod p) V) ^ c.val ∈ ρ.range :=
      pow_mem J.2 _
    refine ⟨q, ?_⟩
    have hval : ((ρ q : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
        = A ^ c.val := by simp [hq, hA]
    rw [hval, hAN, one_add_pow_of_mul_self_eq_zero hN2 c.val,
      ← Nat.cast_smul_eq_nsmul (ZMod p) c.val N, ZMod.natCast_val, ZMod.cast_id]

theorem injective_one_add_smul {N : Module.End (ZMod p) V} (hN : N ≠ 0) :
    Function.Injective fun c : ZMod p => 1 + c • N := by
  intro c d hcd
  have h : (c - d) • N = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel hcd
  rcases smul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hN

theorem ker_eq_range_of_mul_self_eq_zero (hV : finrank (ZMod p) V = 2)
    {N : Module.End (ZMod p) V} (hN : N ≠ 0) (hN2 : N * N = 0) :
    LinearMap.ker N = LinearMap.range N := by
  have := finiteDimensional_of_finrank_eq_two hV
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro v ⟨w, rfl⟩
    have : (N * N) w = 0 := by rw [hN2]; rfl
    simpa [LinearMap.mem_ker] using this
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) N
  have hpos : 0 < finrank (ZMod p) (LinearMap.range N) := by
    rw [finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
    simpa [LinearMap.range_eq_bot] using hN
  have heq : finrank (ZMod p) (LinearMap.range N) = finrank (ZMod p) (LinearMap.ker N) := by
    rw [hV] at hrk
    have := Submodule.finrank_mono hle
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

theorem finrank_ker_eq_one_of_mul_self_eq_zero (hV : finrank (ZMod p) V = 2)
    {N : Module.End (ZMod p) V} (hN : N ≠ 0) (hN2 : N * N = 0) :
    finrank (ZMod p) (LinearMap.ker N) = 1 := by
  have := finiteDimensional_of_finrank_eq_two hV
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) N
  rw [← ker_eq_range_of_mul_self_eq_zero hV hN hN2, hV] at hrk
  omega

theorem apply_eq_self_of_mem_ker {N : Module.End (ZMod p) V}
    (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hrange : (Set.range fun q : Q => (ρ q : Module.End (ZMod p) V))
      = Set.range fun c : ZMod p => 1 + c • N)
    (q : Q) {v : V} (hv : v ∈ LinearMap.ker N) : (ρ q : Module.End (ZMod p) V) v = v := by
  obtain ⟨c, hc⟩ : (ρ q : Module.End (ZMod p) V) ∈ Set.range fun c : ZMod p => 1 + c • N :=
    hrange ▸ ⟨q, rfl⟩
  have hc' : ((ρ q : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
      = 1 + c • N := hc.symm
  rw [hc']
  simp [LinearMap.mem_ker.1 hv]

theorem span_displacement_eq_ker (hV : finrank (ZMod p) V = 2) {N : Module.End (ZMod p) V}
    (hN : N ≠ 0) (hN2 : N * N = 0) (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hrange : (Set.range fun q : Q => (ρ q : Module.End (ZMod p) V))
      = Set.range fun c : ZMod p => 1 + c • N) :
    Submodule.span (ZMod p)
        {w : V | ∃ (q : Q) (v : V), (ρ q : Module.End (ZMod p) V) v - v = w}
      = LinearMap.ker N := by
  rw [ker_eq_range_of_mul_self_eq_zero hV hN hN2]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro w ⟨q, v, rfl⟩
    obtain ⟨c, hc⟩ : (ρ q : Module.End (ZMod p) V) ∈ Set.range fun c : ZMod p => 1 + c • N :=
      hrange ▸ ⟨q, rfl⟩
    have hc' : ((ρ q : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
        = 1 + c • N := hc.symm
    have h : (ρ q : Module.End (ZMod p) V) v - v = c • N v := by rw [hc']; simp
    rw [SetLike.mem_coe, h]
    exact Submodule.smul_mem _ _ ⟨v, rfl⟩
  · obtain ⟨q, hq⟩ : (1 + (1 : ZMod p) • N)
        ∈ Set.range fun q : Q => (ρ q : Module.End (ZMod p) V) := hrange ▸ ⟨1, rfl⟩
    have hq' : ((ρ q : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
        = 1 + (1 : ZMod p) • N := hq
    rintro w ⟨v, rfl⟩
    exact Submodule.subset_span ⟨q, v, by rw [hq']; simp⟩

theorem card_range_eq_one_or_exists_sq_eq_zero (hV : finrank (ZMod p) V = 2) (hQ : IsPGroup p Q)
    (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V) :
    Nat.card ρ.range = 1 ∨
      (Nat.card ρ.range = p ∧ ∃ N : Module.End (ZMod p) V, N ≠ 0 ∧ N * N = 0 ∧
        (Set.range fun q : Q => (ρ q : Module.End (ZMod p) V))
            = Set.range (fun c : ZMod p => 1 + c • N) ∧
        LinearMap.ker N = LinearMap.range N ∧
        finrank (ZMod p) (LinearMap.ker N) = 1 ∧
        (∀ q : Q, ∀ v ∈ LinearMap.ker N, (ρ q : Module.End (ZMod p) V) v = v) ∧
        Submodule.span (ZMod p)
            {w : V | ∃ (q : Q) (v : V), (ρ q : Module.End (ZMod p) V) v - v = w}
          = LinearMap.ker N) := by
  rcases card_range_eq_one_or_eq_prime hV hQ ρ with h | h
  · exact Or.inl h
  · obtain ⟨N, hN, hN2, hrange⟩ := exists_sq_eq_zero_range_coe_eq hV ρ h
    exact Or.inr ⟨h, N, hN, hN2, hrange, ker_eq_range_of_mul_self_eq_zero hV hN hN2,
      finrank_ker_eq_one_of_mul_self_eq_zero hV hN hN2,
      fun q v hv => apply_eq_self_of_mem_ker ρ hrange q hv,
      span_displacement_eq_ker hV hN hN2 ρ hrange⟩

end CFSG.FeitThompson
