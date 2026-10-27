module

public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

section Frobenius

variable {k : Type*} [Field k] [CharP k 2]

theorem frob_pow_injective (b : ℕ) {x y : k} (h : x ^ (2 ^ b) = y ^ (2 ^ b)) : x = y := by
  have : (x - y) ^ (2 ^ b) = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 this)

theorem pow_two_pow_sub {c : k} {a b : ℕ} (hab : b ≤ a) (ha : c ^ (2 ^ a) = c)
    (hb : c ^ (2 ^ b) = c) : c ^ (2 ^ (a - b)) = c := by
  apply frob_pow_injective b
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab, ha, hb]

theorem pow_two_pow_add {c : k} {a b : ℕ} (ha : c ^ (2 ^ a) = c) (hb : c ^ (2 ^ b) = c) :
    c ^ (2 ^ (a + b)) = c := by
  rw [pow_add, pow_mul, ha, hb]

theorem pow_two_pow_mul {c : k} {a : ℕ} (ha : c ^ (2 ^ a) = c) (j : ℕ) :
    c ^ (2 ^ (a * j)) = c := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ]; exact pow_two_pow_add ih ha

theorem pow_two_pow_gcd (c : k) (a b : ℕ) (ha : c ^ (2 ^ a) = c) (hb : c ^ (2 ^ b) = c) :
    c ^ (2 ^ Nat.gcd a b) = c := by
  induction a, b using Nat.gcd.induction with
  | H0 n => simpa using hb
  | H1 a b hpos ih =>
    rw [Nat.gcd_rec]
    refine ih ?_ ha
    rw [Nat.mod_def]
    exact pow_two_pow_sub (Nat.mul_div_le b a) hb (pow_two_pow_mul ha (b / a))

end Frobenius

section Rep

variable {S : Type*} [Group S] {k : Type*} [Field k] [CharP k 2] {m : ℕ}

theorem frob_act (δ : ℕ) (ρ : Representation k S (Fin m → k))
    (hent : ∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i)
    (s : S) (v : Fin m → k) :
    (fun i => (ρ s v i) ^ (2 ^ δ)) = ρ s (fun i => (v i) ^ (2 ^ δ)) := by
  funext i
  have hexp : ∀ w : Fin m → k, ρ s w i = ∑ j, w j * ρ s (Pi.single j 1) i := by
    intro w
    have hv : w = ∑ j, w j • (Pi.single j 1 : Fin m → k) := by
      funext l; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  rw [hexp v, hexp (fun l => (v l) ^ (2 ^ δ)), sum_pow_char_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, hent]

end Rep

section Chi


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem chi_pow_of_entries (δ : ℕ) {ρ : Representation k (adjointGroup τ K) (Fin m → k)}
    (hρ : IsSimpleRep ρ)
    (hent : ∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) :
    ∀ h ∈ (chevDatum τ K 2 hw).H, χ h ^ (2 ^ δ) = χ h := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  set ty : Fin m → k := fun i => (y i) ^ (2 ^ δ) with hty
  have hy : ∀ g, ρ g ty = fun i => (ρ g y i) ^ (2 ^ δ) := fun g => (frob_act δ ρ hent g y).symm
  have hty_fix : ty ∈ (chevDatum τ K 2 hw).fixU ρ := by
    intro u hu
    rw [hy, ht.1 u hu]
  have hty0 : ty ≠ 0 := by
    intro h0
    apply ht.2.1
    funext i
    have := congrFun h0 i
    simp only [hty, Pi.zero_apply] at this
    exact pow_eq_zero_iff (by positivity) |>.1 this
  obtain ⟨c, hc⟩ := (chevDatum τ K 2 hw).fixU_eq_smul hρ hμ hty_fix
  intro h hh
  have e1 : ρ h ty = (χ h ^ (2 ^ δ)) • ty := by
    rw [hy, ht.2.2.1 h hh]
    funext i
    simp [hty, mul_pow]
  have e2 : ρ h ty = χ h • ty := by
    rw [hc, map_smul, ht.2.2.1 h hh, smul_comm]
  have := e1.symm.trans e2
  exact smul_left_injective k hty0 this

end Chi

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
