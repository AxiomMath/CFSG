module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Shape
import CFSG.LocalAnalysis.RankFourTheoremC.P5.Sylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTriple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC Subgroup

open Polynomial

private theorem l42_exists_pow_ne_one {F : Type*} [Field F] [Finite F] {m : ℕ} (hm0 : 0 < m)
    (hm : m + 1 < Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ m ≠ 1 := by
  set Q : F[X] := X * (X ^ m - C 1) with hQ
  have h1 : (X ^ m - C 1 : F[X]).Monic := monic_X_pow_sub_C 1 (by omega)
  have hQ0 : Q ≠ 0 := (monic_X.mul h1).ne_zero
  have hdeg : Q.natDegree = m + 1 := by
    rw [hQ, monic_X.natDegree_mul h1, natDegree_X, natDegree_X_pow_sub_C]
    omega
  obtain ⟨a, ha⟩ := exists_eval_ne_zero_of_natDegree_lt_card Q hQ0 (by
    rw [hdeg, ← Nat.cast_card (α := F)]
    exact_mod_cast hm)
  simp only [hQ, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ne_eq, mul_eq_zero, not_or] at ha
  exact ⟨a, ha.1, fun h => ha.2 (by rw [h, sub_self])⟩

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

private theorem l42_natCast_pow_p (n k : ℕ) : (k : GaloisField p n) ^ p = (k : GaloisField p n) := by
  rw [← frobenius_def, map_natCast]

private theorem l42_card_lt {n : ℕ} (hp5 : 5 ≤ p) (hn : 3 ≤ n) :
    2 * (p - 1) + 1 < Nat.card (GaloisField p n) := by
  rw [GaloisField.card p n (by omega)]
  have h3 : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos hn
  have h4 : 2 * p < p ^ 3 := by
    rw [pow_three]
    nlinarith [Nat.mul_le_mul hp5 hp5]
  omega

theorem centralizer_le_of_not_mem_zpowers_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) {a : G}
    (haP : a ∈ (P : Subgroup G)) (hap : a ^ p = 1) (hax : a ∉ zpowers x) :
    centralizer ({a} : Set G) ≤ M := by
  by_contra hCM
  obtain ⟨n, f, W, hB⟩ := exists_borelDataP hp5 hK hG hloc hType h
  have hS := shape_p hp5 hK hG hloc hType h
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ one_mem _)
  have hao : orderOf a = p := orderOf_eq_prime hap ha1
  have hpa : IsPPoint p P M a := isPPoint_of_mem_abelian hloc hS.abelian haP hao hCM
  have hSa := shape_p hp5 hK hG hloc hType hpa
  have hxP : x ∈ (P : Subgroup G) := h.mem
  have haC : a ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hS.abelian.is_comm.comm ⟨a, haP⟩ ⟨x, hxP⟩)
  have haW : a ∈ W := hB.of_pow_p a ⟨haP, haC⟩ hap
  obtain ⟨t, i, hi, hati⟩ := (hB.mem_iff a).mp haW
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hax
    rw [hati, hB.f_zero, one_mul]
    exact Subgroup.pow_mem _ (mem_zpowers x) i
  obtain ⟨b, hb0, hb⟩ := l42_exists_pow_ne_one (F := GaloisField p n) (m := 2 * (p - 1))
    (by have := hp.out.two_le; omega) (l42_card_lt hp5 hB.three_le)
  obtain ⟨g, hgx, hgf⟩ := hB.torus (Units.mk0 b hb0)
  have hga : g * a * g⁻¹ = f (b ^ 2 * t) * x ^ i := by
    rw [hati]
    calc g * (f t * x ^ i) * g⁻¹ = (g * f t * g⁻¹) * (g * x * g⁻¹) ^ i := by
          rw [conj_pow]; group
      _ = f (b ^ 2 * t) * x ^ i := by
          rw [hgx]
          have := hgf t
          simp only [Units.val_mk0] at this
          rw [this]
  have hgaP : g * a * g⁻¹ ∈ (P : Subgroup G) := by
    rw [hga]
    exact Subgroup.mul_mem _ (hB.f_mem _) (Subgroup.pow_mem _ hxP i)
  have hle : (zpowers a).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
    rw [map_conj_zpowers, zpowers_le]
    exact hgaP
  have hweak := hSa.weak g hle
  have hmem : g * a * g⁻¹ ∈ zpowers a := by
    have : g * a * g⁻¹ ∈ (zpowers a).map (MulAut.conj g).toMonoidHom :=
      ⟨a, mem_zpowers a, rfl⟩
    rw [hweak] at this
    exact this
  obtain ⟨m, hm, hmeq⟩ := PPointP.exists_pow_lt_of_mem_zpowers hao hmem
  have hcommx : ∀ s : GaloisField p n, Commute (f s) x := fun s => hB.f_comm s
  have hcf : Commute (f t) (x ^ i) := (hcommx t).pow_right i
  have hfeq : f (b ^ 2 * t) * x ^ i = f ((m : GaloisField p n) * t) * x ^ (i * m) := by
    rw [← hga, hmeq, hati, hcf.mul_pow, ← hB.f_nat_mul t m, pow_mul]
  have hfeq' : f (b ^ 2 * t) = f ((m : GaloisField p n) * t) * (x ^ (i * m) * (x ^ i)⁻¹) := by
    have h1 := congrArg (· * (x ^ i)⁻¹) hfeq
    simp only [mul_inv_cancel_right] at h1
    rw [h1]
    group
  have hcomm_f : ∀ s : GaloisField p n, Commute (f s) (x ^ (i * m) * (x ^ i)⁻¹) := fun s =>
    ((hcommx s).pow_right (i * m)).mul_right ((hcommx s).pow_right i).inv_right
  have hD : f ((b ^ 2 - (m : GaloisField p n)) * t) = x ^ (i * m) * (x ^ i)⁻¹ := by
    have e1 : (b ^ 2 - (m : GaloisField p n)) * t = b ^ 2 * t + -((m : GaloisField p n) * t) := by
      ring
    rw [e1, hB.f_add, hB.f_neg, hfeq']
    have hc := hcomm_f ((m : GaloisField p n) * t)
    calc f ((m : GaloisField p n) * t) * (x ^ (i * m) * (x ^ i)⁻¹) *
          (f ((m : GaloisField p n) * t))⁻¹
        = (x ^ (i * m) * (x ^ i)⁻¹) * f ((m : GaloisField p n) * t) *
          (f ((m : GaloisField p n) * t))⁻¹ := by rw [hc.eq]
      _ = x ^ (i * m) * (x ^ i)⁻¹ := by rw [mul_inv_cancel_right]
  have hDx : f ((b ^ 2 - (m : GaloisField p n)) * t) ∈ zpowers x := by
    rw [hD]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_zpowers x) _)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_zpowers x) _))
  have hzero : (b ^ 2 - (m : GaloisField p n)) * t = 0 := by
    by_contra hne
    exact hB.f_not_mem_zpowers hne hDx
  have hbm : b ^ 2 = (m : GaloisField p n) := by
    have := (mul_eq_zero.mp hzero).resolve_right ht0
    exact sub_eq_zero.mp this
  have hpow : (b ^ 2) ^ p = b ^ 2 := by
    rw [hbm]
    exact l42_natCast_pow_p n m
  apply hb
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have e2 : (b ^ 2) ^ p = b ^ 2 * b ^ (2 * (p - 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e2] at hpow
  have := mul_left_cancel₀ hb2 (hpow.trans (mul_one (b ^ 2)).symm)
  exact this


end CFSG.LocalAnalysis.RankFourTheoremC.P5
