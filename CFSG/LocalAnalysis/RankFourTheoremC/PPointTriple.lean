module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma33
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Polynomial Subgroup

theorem exists_three_squares {F : Type*} [Field F] [Finite F] [CharP F 3] (hF : 9 < Nat.card F) :
    ∃ a₀ a₁ a₂ : F, a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₀ ^ 2 ≠ a₁ ^ 2 ∧ a₀ ^ 2 ≠ a₂ ^ 2 ∧
      a₁ ^ 2 ≠ a₂ ^ 2 ∧ a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 0 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  set P : F[X] := (X ^ 3 - X) * (X ^ 2 + X - C 1) * (X ^ 2 - X - C 1) * (X ^ 2 + C 1) with hP
  have h1 : (X ^ 3 - X : F[X]).Monic := monic_X_pow_sub (by simp)
  have h2 : (X ^ 2 + X - C 1 : F[X]).Monic := by monicity!
  have h4 : (X ^ 2 - X - C 1 : F[X]).Monic := by monicity!
  have h5 : (X ^ 2 + C 1 : F[X]).Monic := by monicity!
  have hP0 : P ≠ 0 := (((h1.mul h2).mul h4).mul h5).ne_zero
  have hd1 : (X ^ 3 - X : F[X]).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  have hd2 : (X ^ 2 + X - C 1 : F[X]).natDegree = 2 := by compute_degree!
  have hd4 : (X ^ 2 - X - C 1 : F[X]).natDegree = 2 := by compute_degree!
  have hd5 : (X ^ 2 + C 1 : F[X]).natDegree = 2 := by compute_degree!
  have hdeg : P.natDegree = 9 := by
    rw [hP, ((h1.mul h2).mul h4).natDegree_mul h5, (h1.mul h2).natDegree_mul h4,
      h1.natDegree_mul h2, hd1, hd2, hd4, hd5]
  obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_natDegree_lt_card P hP0 (by
    rw [hdeg, ← Nat.cast_card (α := F)]
    exact_mod_cast hF)
  simp only [hP, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C, ne_eq, mul_eq_zero,
    not_or] at ht
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := ht
  refine ⟨t ^ 2 + 1, t ^ 2 + t - 1, t ^ 2 - t - 1, hD, hB, hC, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hA
    linear_combination h + (t ^ 3 - t - t ^ 2) * h3
  · intro h
    apply hA
    linear_combination (-1 : F) * h + (t ^ 3 - t + t ^ 2) * h3
  · intro h
    apply hA
    linear_combination h - (t ^ 3 - t) * h3
  · linear_combination (t ^ 4 + 1) * h3

section Group

variable {G : Type} [Group G]

theorem mem_zpowers_of_pow_three {y z : G} (hy : y ^ 3 = 1) (hz : z ∈ zpowers y) :
    z = 1 ∨ z = y ∨ z = y⁻¹ := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hz
  have hy3 : y ^ (3 : ℤ) = 1 := by simpa using hy
  have hm : y ^ m = y ^ (m % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 3, zpow_add, zpow_mul, hy3, one_zpow, mul_one]
  rw [hm]
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · left
    rw [h0]
    simp
  · right
    left
    rw [h1]
    simp
  · right
    right
    rw [h2]
    refine eq_inv_of_mul_eq_one_right ?_
    calc y * y ^ (2 : ℤ) = y ^ 3 := by
          simp only [zpow_two, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hy

theorem map_conj_zpowers (y h : G) :
    (zpowers y).map (MulAut.conj h).toMonoidHom = zpowers (h * y * h⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

end Group

section Product

variable {G F : Type*} [Group G] [Field F]

theorem exists_subgroup_fx {x : G} (hx3 : x ^ 3 = 1) {f : F → G}
    (hfadd : ∀ s t, f (s + t) = f s * f t) (hfx : ∀ t, f t * x = x * f t) :
    ∃ W : Subgroup G, ∀ g, g ∈ W ↔ ∃ (t : F) (i : ℕ), i < 3 ∧ g = f t * x ^ i := by
  have hf0 : f 0 = 1 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one (f 0)).symm)
  have hfneg : ∀ t, f (-t) = (f t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_right (by rw [← hfadd, add_neg_cancel, hf0])
  have hxe : ∀ (t : F) (e : ℕ), f t * x ^ e = x ^ e * f t := fun t e =>
    (Commute.pow_right (show Commute (f t) x from hfx t) e).eq
  have hxx : x ^ 2 = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    calc x * x ^ 2 = x ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hx3
  refine ⟨{ carrier := {g | ∃ (t : F) (i : ℕ), i < 3 ∧ g = f t * x ^ i}
            mul_mem' := ?_
            one_mem' := ⟨0, 0, by norm_num, by simp [hf0]⟩
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro _ _ ⟨t, i, hi, rfl⟩ ⟨s, j, hj, rfl⟩
    have h1 : f t * x ^ i * (f s * x ^ j) = f (t + s) * x ^ (i + j) := by
      rw [hfadd, pow_add]
      calc f t * x ^ i * (f s * x ^ j) = f t * (x ^ i * f s) * x ^ j := by group
        _ = f t * (f s * x ^ i) * x ^ j := by rw [← hxe s i]
        _ = f t * f s * (x ^ i * x ^ j) := by group
    by_cases hij : i + j < 3
    · exact ⟨t + s, i + j, hij, h1⟩
    · refine ⟨t + s, i + j - 3, by omega, ?_⟩
      rw [h1]
      congr 1
      have : x ^ (i + j) = x ^ (i + j - 3) * x ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, hx3, mul_one]
  · rintro _ ⟨t, i, hi, rfl⟩
    interval_cases i
    · exact ⟨-t, 0, by norm_num, by simp [hfneg]⟩
    · refine ⟨-t, 2, by norm_num, ?_⟩
      rw [mul_inv_rev, pow_one, ← hxx, ← hfneg]
      exact (hxe (-t) 2).symm
    · refine ⟨-t, 1, by norm_num, ?_⟩
      rw [mul_inv_rev, hxx, inv_inv, ← hfneg, pow_one]
      exact (hfx (-t)).symm

end Product

section Main

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 3]

theorem eq_zpowers_of_isConj_of_le (hF : 9 < Nat.card F) {x : G} (hx3 : x ^ 3 = 1)
    {f : F → G} (hfadd : ∀ s t, f (s + t) = f s * f t) (hfinj : Function.Injective f)
    (hfx : ∀ t, f t * x = x * f t) (hxf : ∀ t, f t ≠ x)
    {W : Subgroup G} (hWf : ∀ t, f t ∈ W) (hWx : x ∈ W)
    (hWy : ∀ y ∈ W, ∃ (t : F) (i : ℕ), i < 3 ∧ y = f t * x ^ i)
    (htor : ∀ a : Fˣ, ∃ g : G, g * x * g⁻¹ = x ∧ ∀ t, g * f t * g⁻¹ = f ((a : F) ^ 2 * t))
    (hno : ∀ D : Subgroup G, D ≤ W → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = 3 ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom)
    {L : Subgroup G} (hLW : L ≤ W) (hL : Nat.card L = 3)
    (hLc : ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom) : L = zpowers x := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hf0 : f 0 = 1 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one (f 0)).symm)
  have hfcomm : ∀ s t, f s * f t = f t * f s := fun s t => by
    rw [← hfadd, ← hfadd, add_comm]
  have hfneg : ∀ t, f (-t) = (f t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_right (by rw [← hfadd, add_neg_cancel, hf0])
  have hf3 : ∀ t, f t ^ 3 = 1 := fun t => by
    have h : t + t + t = 0 := by linear_combination t * h3F
    calc f t ^ 3 = f t * f t * f t := by simp only [pow_succ, pow_zero, one_mul]
      _ = f (t + t + t) := by rw [hfadd, hfadd]
      _ = 1 := by rw [h, hf0]
  have hxe : ∀ (t : F) (e : ℕ), f t * x ^ e = x ^ e * f t := fun t e =>
    (Commute.pow_right (show Commute (f t) x from hfx t) e).eq
  have hxx : x ^ 2 = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    calc x * x ^ 2 = x ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hx3
  have hx0 : ∀ t : F, f t * x ≠ 1 := fun t h => hxf (-t) (by
    rw [hfneg]
    exact (eq_inv_of_mul_eq_one_right h).symm)
  have hL1 : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hL
    omega
  obtain ⟨⟨y, hyL⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := by
      have := orderOf_dvd_natCard (⟨y, hyL⟩ : L)
      rwa [Subgroup.orderOf_mk, hL] at this
    exact ((Nat.dvd_prime hp3).mp hdvd).resolve_left fun h => hy1' (orderOf_eq_one_iff.mp h)
  have hLy : L = zpowers y := (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyL)
    (by rw [Nat.card_zpowers, hyord, hL])).symm
  obtain ⟨t, i, hi, hyt⟩ := hWy y (hLW hyL)
  by_cases ht0 : t = 0
  ·
    subst ht0
    rw [hf0, one_mul] at hyt
    interval_cases i
    · exact absurd (by simpa using hyt) hy1'
    · rw [hLy, hyt, pow_one]
    · rw [hLy, hyt, hxx, zpowers_inv]
  exfalso
  obtain ⟨k, e, hk0, he, hLke⟩ : ∃ (k : F) (e : ℕ), k ≠ 0 ∧ e ≤ 1 ∧ L = zpowers (f k * x ^ e) := by
    interval_cases i
    · exact ⟨t, 0, ht0, by omega, by rw [hLy, hyt]⟩
    · exact ⟨t, 1, ht0, le_rfl, by rw [hLy, hyt]⟩
    · refine ⟨-t, 1, neg_ne_zero.mpr ht0, le_rfl, ?_⟩
      have hinv : (f t * x ^ 2)⁻¹ = f (-t) * x ^ 1 := by
        rw [mul_inv_rev, hxx, inv_inv, ← hfneg, pow_one]
        exact (hfx (-t)).symm
      rw [hLy, ← zpowers_inv, hyt, hinv]
  have hpow3 : ∀ u : F, (f u * x ^ e) ^ 3 = 1 := fun u => by
    rw [(show Commute (f u) (x ^ e) from hxe u e).mul_pow, hf3, ← pow_mul, mul_comm, pow_mul,
      hx3, one_pow, one_mul]
  have hne1 : ∀ u : F, u ≠ 0 → f u * x ^ e ≠ 1 := fun u hu h1 => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
    · rw [pow_zero, mul_one, ← hf0] at h1
      exact hu (hfinj h1)
    · rw [pow_one] at h1
      exact hx0 u h1
  have hcard3 : ∀ u : F, u ≠ 0 → Nat.card (zpowers (f u * x ^ e)) = 3 := fun u hu => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow3 u) (hne1 u hu)]
  have hcommy : ∀ u v : F, Commute (f u * x ^ e) (f v * x ^ e) := fun u v =>
    Commute.mul_right (Commute.mul_left (hfcomm u v) (show Commute (x ^ e) (f v) from
      (hxe v e).symm)) (Commute.mul_left (show Commute (f u) (x ^ e) from hxe u e)
        (Commute.refl _))
  have hdist : ∀ u v : F, v ≠ 0 → zpowers (f u * x ^ e) = zpowers (f v * x ^ e) →
      v = u ∨ (e = 0 ∧ v = -u) := by
    intro u v hv h
    have hmem : f v * x ^ e ∈ zpowers (f u * x ^ e) := h ▸ mem_zpowers _
    rcases mem_zpowers_of_pow_three (hpow3 u) hmem with h1 | h2 | h3'
    · exact absurd h1 (hne1 v hv)
    · left
      exact hfinj (mul_right_cancel h2)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
      · right
        refine ⟨rfl, ?_⟩
        rw [pow_zero, mul_one, mul_one, ← hfneg] at h3'
        exact hfinj h3'
      · exfalso
        have h4 : (f v * x ^ 1) * (f u * x ^ 1) = 1 := by rw [h3']; exact inv_mul_cancel _
        have h5 : f (v + u) * x ^ 2 = 1 := by
          calc f (v + u) * x ^ 2 = f v * (f u * x) * x := by
                rw [hfadd]; simp only [pow_two, mul_assoc]
            _ = f v * (x * f u) * x := by rw [hfx u]
            _ = (f v * x ^ 1) * (f u * x ^ 1) := by simp only [pow_one, mul_assoc]
            _ = 1 := h4
        rw [hxx] at h5
        exact hxf (v + u) (mul_inv_eq_one.mp h5)
  obtain ⟨a₀, a₁, a₂, ha₀, ha₁, ha₂, h01, h02, h12, hsum⟩ := exists_three_squares hF
  have hne : ∀ b₁ b₂ b₃ : F, b₁ ≠ 0 → b₂ ≠ 0 → b₃ ≠ 0 → b₁ ^ 2 ≠ b₂ ^ 2 →
      b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 = 0 →
      zpowers (f (b₁ ^ 2 * k) * x ^ e) ≠ zpowers (f (b₂ ^ 2 * k) * x ^ e) := by
    intro b₁ b₂ b₃ hb₁ hb₂ hb₃ hb12 hsum' h
    have hv : b₂ ^ 2 * k ≠ 0 := mul_ne_zero (pow_ne_zero 2 hb₂) hk0
    rcases hdist _ _ hv h with h1 | ⟨-, h2⟩
    · exact hb12 (mul_right_cancel₀ hk0 h1).symm
    · have h2' : b₂ ^ 2 = -b₁ ^ 2 := mul_right_cancel₀ hk0 (h2.trans (neg_mul _ _).symm)
      apply hb₃
      have : b₃ ^ 2 = 0 := by linear_combination hsum' - h2'
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have key : ∀ a : F, a ≠ 0 →
      ∃ g : G, g * x * g⁻¹ = x ∧ ∀ t, g * f t * g⁻¹ = f (a ^ 2 * t) := fun a ha => by
    obtain ⟨g, hgx, hgf⟩ := htor (Units.mk0 a ha)
    exact ⟨g, hgx, fun t => by simpa using hgf t⟩
  obtain ⟨g₀, hg₀⟩ := hLc
  have hconj : ∀ a : F, a ≠ 0 → ∃ g : G, zpowers (f (a ^ 2 * k) * x ^ e) =
      (zpowers x).map (MulAut.conj g).toMonoidHom := by
    intro a ha
    obtain ⟨g, hgx, hgf⟩ := key a ha
    refine ⟨g * g₀, ?_⟩
    have h1 : zpowers (f (a ^ 2 * k) * x ^ e) = L.map (MulAut.conj g).toMonoidHom := by
      rw [hLke, map_conj_zpowers]
      congr 1
      calc f (a ^ 2 * k) * x ^ e = (g * f k * g⁻¹) * (g * x * g⁻¹) ^ e := by rw [hgf, hgx]
        _ = g * (f k * x ^ e) * g⁻¹ := by rw [conj_pow]; group
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom =
        (MulAut.conj (g * g₀)).toMonoidHom := MonoidHom.ext fun z => by simp [mul_assoc]
    rw [h1, hg₀, Subgroup.map_map, hcomp]
  have hunit : ∀ a : F, a ≠ 0 → a ^ 2 * k ≠ 0 := fun a ha => mul_ne_zero (pow_ne_zero 2 ha) hk0
  have hprod : (f (a₀ ^ 2 * k) * x ^ e) * (f (a₁ ^ 2 * k) * x ^ e) * (f (a₂ ^ 2 * k) * x ^ e) =
      1 := by
    have hcx : ∀ u : F, Commute (x ^ e) (f u) := fun u => (hxe u e).symm
    rw [Commute.mul_mul_mul_comm (hcx _), Commute.mul_mul_mul_comm
      (Commute.mul_left (hcx _) (hcx _)), ← hfadd, ← hfadd, ← add_mul, ← add_mul, hsum, zero_mul,
      hf0, one_mul, show x ^ e * x ^ e * x ^ e = (x ^ 3) ^ e by
        rw [← pow_add, ← pow_add, ← pow_mul]; congr 1; ring, hx3, one_pow]
  have hne01 := hne a₀ a₁ a₂ ha₀ ha₁ ha₂ h01 hsum
  have hne02 := hne a₀ a₂ a₁ ha₀ ha₂ ha₁ h02 (by linear_combination hsum)
  have hne12 := hne a₁ a₂ a₀ ha₁ ha₂ ha₀ h12 (by linear_combination hsum)
  have hy1D : f (a₁ ^ 2 * k) * x ^ e ∉ zpowers (f (a₀ ^ 2 * k) * x ^ e) := fun hmem =>
    hne01 (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem)
      (by rw [hcard3 _ (hunit a₀ ha₀), hcard3 _ (hunit a₁ ha₁)])).symm
  have hDel : IsElemAbelian 3 (zpowers (f (a₀ ^ 2 * k) * x ^ e) ⊔
      zpowers (f (a₁ ^ 2 * k) * x ^ e)) := by
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
      (isElemAbelian_zpowers (hpow3 _)) (isElemAbelian_zpowers (hpow3 _)) ?_
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun b hb => ?_
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (hcommy (a₁ ^ 2 * k) (a₀ ^ 2 * k)) m).eq
  have hDcard : Nat.card ↥(zpowers (f (a₀ ^ 2 * k) * x ^ e) ⊔
      zpowers (f (a₁ ^ 2 * k) * x ^ e)) = 3 ^ 2 := by
    have hcomm : ∀ a ∈ zpowers (f (a₀ ^ 2 * k) * x ^ e),
        a * (f (a₁ ^ 2 * k) * x ^ e) = (f (a₁ ^ 2 * k) * x ^ e) * a := fun a ha => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hcommy (a₀ ^ 2 * k) (a₁ ^ 2 * k)) m).eq
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp3 _ (hpow3 _) hy1D hcomm,
      hcard3 _ (hunit a₀ ha₀)]
    norm_num
  have hyW : ∀ u : F, f u * x ^ e ∈ W := fun u => W.mul_mem (hWf u) (pow_mem hWx e)
  have hDW : zpowers (f (a₀ ^ 2 * k) * x ^ e) ⊔ zpowers (f (a₁ ^ 2 * k) * x ^ e) ≤ W :=
    sup_le (zpowers_le.mpr (hyW _)) (zpowers_le.mpr (hyW _))
  have hy2D : f (a₂ ^ 2 * k) * x ^ e ∈ zpowers (f (a₀ ^ 2 * k) * x ^ e) ⊔
      zpowers (f (a₁ ^ 2 * k) * x ^ e) := by
    rw [eq_inv_of_mul_eq_one_right hprod]
    exact inv_mem (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
  refine hno _ hDW hDel hDcard ⟨{zpowers (f (a₀ ^ 2 * k) * x ^ e),
    zpowers (f (a₁ ^ 2 * k) * x ^ e), zpowers (f (a₂ ^ 2 * k) * x ^ e)},
    Finset.card_eq_three.mpr ⟨_, _, _, hne01, hne02, hne12, rfl⟩, ?_⟩
  intro L' hL'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL'
  rcases hL' with rfl | rfl | rfl
  · exact ⟨le_sup_left, hcard3 _ (hunit a₀ ha₀), hconj a₀ ha₀⟩
  · exact ⟨le_sup_right, hcard3 _ (hunit a₁ ha₁), hconj a₁ ha₁⟩
  · exact ⟨zpowers_le.mpr hy2D, hcard3 _ (hunit a₂ ha₂), hconj a₂ ha₂⟩

end Main

end CFSG.LocalAnalysis.RankFourTheoremC
