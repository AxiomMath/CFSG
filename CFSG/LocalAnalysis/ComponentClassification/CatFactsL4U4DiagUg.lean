module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUf

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem conj_blk {P B : GL (Fin 4) K} {x y : K}
    (hblk : ((P⁻¹ * B * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk x 0 0 y) (n : ℕ) :
    ((P⁻¹ * B ^ n * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk (x ^ n) 0 0 (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, mul_one, inv_mul_cancel, Units.val_one, pow_zero, pow_zero, blk_one]
  | succ n ih =>
    have e : P⁻¹ * B ^ (n + 1) * P = (P⁻¹ * B ^ n * P) * (P⁻¹ * B * P) := by group
    rw [e, Units.val_mul, ih, hblk, blk_mul_blk, pow_succ, pow_succ]

theorem sq_eq_one_of_pow_four_AU (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {a : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (ha : a ∈ CAU J' ⊓ InnU p f K h)
    (h4 : a ^ 4 = 1) : a ^ 2 = 1 := by
  obtain ⟨haC, B, hB⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨x, y, hblk, hun⟩ := blk_of_mem_AU h hp2 P hP hJU hJL hB haC
  have hpow : ∀ n : ℕ, IsCU h (B ^ n) (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact isCU_one h
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h hB
  obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 (h4 ▸ hpow 4)
  have h4m := conj_blk hblk 4
  rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one] at h4m
  have e0 := congrFun (congrFun h4m 0) 0
  have e2 := congrFun (congrFun h4m 2) 2
  simp [blk] at e0 e2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hun
    exact zero_ne_one hun
  set t := x * h.bar x with ht
  have hbt : h.bar t = t := by rw [ht, map_mul, h.bar_bar, mul_comm]
  have ht0 : t ≠ 0 := mul_ne_zero hx0 (fun h0 => hx0 ((map_eq_zero h.bar).1 h0))
  have ht4 : t ^ 4 = 1 := by
    have e : t ^ 4 = (x ^ 4) * h.bar x ^ 4 := by rw [ht, mul_pow]
    rw [e, ← e0, e2, ← mul_pow, mul_comm, hun, one_pow]
  have htq : t ^ (p ^ f - 1) = 1 := by
    have e : t ^ (p ^ f) = t := by rw [← UnitaryFieldData.bar_apply h, hbt]
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have e' : t ^ (p ^ f - 1) * t = t := by rw [← pow_succ, Nat.sub_add_cancel hq1, e]
    exact (mul_eq_right₀ ht0).1 e'
  have ht2 : t ^ 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f - 1 = 4 * k + 2 := ⟨(p ^ f - 3) / 4, by omega⟩
    rw [hk, pow_add, pow_mul, ht4, one_pow, one_mul] at htq
    exact htq
  have hxy : x ^ 2 = y ^ 2 := by
    calc x ^ 2 = x ^ 2 * (h.bar x * y) ^ 2 := by rw [hun, one_pow, mul_one]
      _ = t ^ 2 * y ^ 2 := by rw [ht]; ring
      _ = y ^ 2 := by rw [ht2, one_mul]
  have h2m := conj_blk hblk 2
  rw [← hxy, blk_eq_smul_one] at h2m
  have hB2 : ((B ^ 2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = x ^ 2 • 1 := by
    rw [val_eq_of_conj P (B ^ 2), h2m, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact (hpow 2).unique h (isCU_one_of_eq_smul h (pow_mem hB.1 2) hB2)

theorem mul_comm_of_mem_AU (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {a b : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (ha : a ∈ CAU J' ⊓ InnU p f K h)
    (hb : b ∈ CAU J' ⊓ InnU p f K h) : a * b = b * a := by
  obtain ⟨haC, B, hB⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨hbC, B', hB'⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨x, y, hblk, -⟩ := blk_of_mem_AU h hp2 P hP hJU hJL hB haC
  obtain ⟨x', y', hblk', -⟩ := blk_of_mem_AU h hp2 P hP hJU hJL hB' hbC
  have e1 : ((P⁻¹ * (B * B') * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((P⁻¹ * (B' * B) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have f1 : P⁻¹ * (B * B') * P = (P⁻¹ * B * P) * (P⁻¹ * B' * P) := by group
    have f2 : P⁻¹ * (B' * B) * P = (P⁻¹ * B' * P) * (P⁻¹ * B * P) := by group
    rw [f1, f2, Units.val_mul (P⁻¹ * B * P), Units.val_mul (P⁻¹ * B' * P), hblk, hblk',
      blk_mul_blk, blk_mul_blk, mul_comm x, mul_comm y]
  have e2 : B * B' = B' * B := Units.ext (by rw [val_eq_of_conj P (B * B'), e1,
    ← val_eq_of_conj P])
  have h1 := hB.mul h hB'
  rw [e2] at h1
  exact h1.unique h (hB'.mul h hB)

theorem inv_mul_mem_AU (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {g k : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hg : g ∈ CAU J') (hk : k ∈ CAU J')
    (hgA : g ∉ CAU J' ⊓ InnU p f K h) (hkA : k ∉ CAU J' ⊓ InnU p f K h) :
    g⁻¹ * k ∈ CAU J' ⊓ InnU p f K h := by
  classical
  have : Finite K := h.finite
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hker : (thU p f K).ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  have hbar : ∀ u ∈ CAU J', u ∉ CAU J' ⊓ InnU p f K h →
      ∃ (Au : GL (Fin 4) K) (φ : K ≃+* K) (hAu : ∀ x : unitarySU p f K 4,
        Au * glAut φ (x : GL (Fin 4) K) * Au⁻¹ ∈ unitarySU p f K 4),
        Au ∈ uMat h 4 ∧ (∀ x : unitarySU p f K 4, thU p f K
          (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom Au φ hAu x) =
            u (thU p f K x)) ∧ ∀ c, φ c = h.bar c := by
    intro u hu huA
    obtain ⟨Au, φ, hAu, hAuu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2
      (d := 4) (by norm_num) (thU p f K) thU_surjective hker u
    refine ⟨Au, φ, hAu, (mem_uMat h).2 hAuu, hlift, ?_⟩
    obtain ⟨_, _, _, _, _, _, hcase⟩ := blk_of_fix h hp2 P hP hμ hAuu hlift (hu _ (hJU 1))
      (hu _ (hJL 1)) (hu _ (hJU μ))
    rcases hcase with ⟨rfl, -, -⟩ | ⟨hb, -, -⟩
    · exfalso
      apply huA
      refine Subgroup.mem_inf.2 ⟨hu, Au, (mem_uMat h).2 hAuu, fun x x' hx => ?_⟩
      rw [← hlift x]
      congr 1
      apply Subtype.ext
      rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, glAut_refl, hx]
    · exact hb
  obtain ⟨Ag, φ, hAg, hAgU, hliftg, hφ⟩ := hbar g hg hgA
  obtain ⟨Ak, ψ, hAk, hAkU, hliftk, hψ⟩ := hbar k hk hkA
  have hφψ : ψ = φ := RingEquiv.ext fun c => by rw [hφ, hψ]
  subst hφψ
  have hφφ : ∀ X : GL (Fin 4) K, glAut ψ (glAut ψ X) = X := by
    intro X
    have e : ψ * ψ = 1 := RingEquiv.ext fun c => by
      change ψ (ψ c) = c
      rw [hψ, hψ, h.bar_bar]
    have := congrArg (fun χ : MulAut (GL (Fin 4) K) => χ X) (show glAut ψ * glAut ψ = 1 by
      rw [← map_mul, e, map_one])
    simpa using this
  set C := glAut ψ (Ag⁻¹ * Ak) with hC
  have hCU : C ∈ uMat h 4 := glAut_mem_uMat h ψ (mul_mem (inv_mem hAgU) hAkU)
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hg) hk, C, hCU, fun x x' hx => ?_⟩
  have e1 : k (thU p f K x) = g (thU p f K x') := by
    rw [← hliftk x, ← hliftg x']
    congr 1
    apply Subtype.ext
    rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
      ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hx, map_mul, map_mul,
      map_inv, hC, hφφ]
    group
  rw [MulAut.mul_apply, e1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
