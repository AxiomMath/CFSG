module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.CertCases
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Open
open scoped Matrix

theorem toVec_negWorbit (j : ℕ) :
    toVec Tag.E7.rank (negWorbit j) =
      ((((-1 : ℤ) • e7T3W) ^ j) *ᵥ toVec Tag.E7.rank sigma0) := by
  induction j with
  | zero => simp [negWorbit]
  | succ j ih =>
    have h : negWorbit (j + 1) = lmulVec Tag.E7.rank negWList (negWorbit j) := by
      simp only [negWorbit, Function.iterate_succ_apply']
    have hm : toMat Tag.E7.rank negWList = (-1 : ℤ) • e7T3W := by
      rw [negWList, e7T3W_eq]
      ext i j
      simp [toMat, lsmul, lofFn, lget]
    rw [h, toVec_lmulVec, hm, pow_succ', ← Matrix.mulVec_mulVec, ih]

section Root


theorem sigma0_isRoot : IsRoot Tag.E7 (toVec Tag.E7.rank sigma0) :=
  isRoot_toVec (by decide +kernel)

end Root

theorem eq_sigma0_of_toVec_eq : ∀ l ∈ Tag.E7.artifactRoots,
    toVec Tag.E7.rank l = toVec Tag.E7.rank sigma0 → l = sigma0 := by
  intro l hl h
  have hlen : l.length = 7 := by
    revert l; decide +kernel
  have h1 : ∀ i : Fin 7, vget l i = vget sigma0 i := fun i => congrFun h i
  apply List.ext_getElem (by simpa [sigma0] using hlen)
  intro i hi hi'
  have := h1 ⟨i, by simpa [hlen] using hi⟩
  simpa [vget, List.getD_eq_getElem?_getD, hi, hi'] using this

section Cube

variable {Y : Type*} [Group Y] {p : ℕ} [hp : Fact p.Prime]

theorem two_le_card_ker {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {M : Type*} [Field M] (χ : E →* Mˣ) : p ^ 2 ≤ Nat.card χ.ker := by
  classical
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hrange : χ.range ≤ rootsOfUnity p M := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, hpE x, map_one]
  have hcr : Nat.card χ.range ≤ p := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have : Finite (rootsOfUnity p M) := inferInstance
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity M p)
  have hmul := Subgroup.card_mul_index χ.ker
  rw [Subgroup.index_ker, hcard] at hmul
  by_contra h
  push Not at h
  have h1 : Nat.card χ.ker * Nat.card χ.range < p ^ 2 * p := by
    calc Nat.card χ.ker * Nat.card χ.range ≤ Nat.card χ.ker * p := Nat.mul_le_mul_left _ hcr
      _ < p ^ 2 * p := Nat.mul_lt_mul_of_pos_right h hp.out.pos
  rw [hmul] at h1
  have : p ^ 3 = p ^ 2 * p := by ring
  omega

theorem exists_subgroup_card_sq {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (h : p ^ 2 ≤ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ 2 := by
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  have h2 : 2 ≤ m := by
    by_contra h'
    push Not at h'
    rw [hm] at h
    have := Nat.pow_lt_pow_right hp.out.one_lt h'
    omega
  exact Sylow.exists_subgroup_card_pow_prime p (n := 2) (by rw [hm]; exact pow_dvd_pow p h2)

end Cube

theorem six_dvd_sub_one {p q : ℕ} (hp : p.Prime) (h : orderOf ((q : ℕ) : ZMod p) = 6) :
    6 ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at h
    omega
  rw [← h]
  exact ZMod.orderOf_dvd_card_sub_one hq0

theorem three_lt_of_orderOf_eq_six {p q : ℕ} (hp : p.Prime) (h : orderOf ((q : ℕ) : ZMod p) = 6) :
    3 < p := by
  have h6 := six_dvd_sub_one hp h
  have h2 := hp.two_le
  obtain ⟨k, hk⟩ := h6
  omega

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
