module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem two_mul_add_one_le_pow {p : ℕ} (hp : 3 ≤ p) (a : ℕ) : 2 * a + 1 ≤ p ^ a := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

theorem arith_contra {p n β q a : ℕ} (hp : 3 ≤ p) (h1 : p ^ 3 ≤ n) (h2 : p ^ 2 * β ≤ n + p ^ 2)
    (hq : q = (n - 4) / p) (h4 : q * p ^ a ≤ a + β) : False := by
  have hpa := two_mul_add_one_le_pow hp a
  have hp3 : p ^ 3 = p * p * p := by ring
  have hp2' : p ^ 2 = p * p := by ring
  rw [hp3] at h1
  rw [hp2'] at h2
  have hp9 : 9 * p ≤ p * p * p := by nlinarith
  have hn4 : 4 + p + 3 ≤ n := by nlinarith
  have hq1 : p * q ≤ n - 4 := by rw [hq]; exact Nat.mul_div_le _ _
  have hq2 : n - 4 < p * (q + 1) := by
    rw [hq]
    exact Nat.lt_mul_div_succ (n - 4) (show 0 < p by omega)
  have hn4' : n - 4 + 4 = n := by omega
  have hqpos : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    subst this
    nlinarith
  have hqβ : q ≤ β := by
    by_contra h
    have h5 : β + 1 ≤ q := by omega
    have h6 : q * (2 * a + 1) ≤ q * p ^ a := Nat.mul_le_mul_left q hpa
    nlinarith
  have h7 : n < p * β + p + 4 := by
    have : p * (q + 1) ≤ p * (β + 1) := Nat.mul_le_mul_left p (by omega)
    nlinarith
  have h8 : p * p - 2 ≤ β := by
    by_contra h
    have hh : 2 ≤ p * p := by nlinarith
    have h9 : β + 3 ≤ p * p := by omega
    nlinarith
  nlinarith

variable {G : Type*} [Group G]

theorem isElemAbelian_autBar {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B)
    (L : Subgroup G) : IsElemAbelian p (autBar p B L) := by
  have hBc := hB.1
  have hxB : ∀ x : ↥(Subgroup.normalizer (L : Set G)),
      x ∈ (B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G)) →
        (x : G) ∈ B := fun x hx =>
    (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hx)).1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    show (a : MulAut (barOf p L)) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have h1 := hBc.is_comm.comm (⟨(x : G), hxB x hx⟩ : ↥B) ⟨(y : G), hxB y hy⟩
    have h2 : (x : G) * (y : G) = (y : G) * (x : G) := by
      have := congrArg Subtype.val h1
      simpa using this
    exact Subtype.ext h2
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := by
      apply Subtype.ext
      simpa using hB.2 _ (hxB x hx)
    rw [this, map_one]

theorem center_eq_bot_of_odd {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] {n : ℕ}
    (hn : 8 ≤ n) (e : (P ⧸ Subgroup.center P) ≃* alternatingGroup (Fin n))
    (hodd : Odd (Nat.card (Subgroup.center P))) : Subgroup.center P = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let η : P →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center P))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center P := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hη hker.le
    (hker ▸ hodd)
  rw [hker] at h1
  exact Subgroup.card_eq_one.1 h1

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
