module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292UReal
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open Matrix

namespace P614K292U

section Arith

theorem pow_mod_three_of_even {p k : ℕ} (hp : p % 3 = 2) (hk : Even k) : p ^ k % 3 = 1 := by
  obtain ⟨i, rfl⟩ := hk
  rw [← two_mul, pow_mul, Nat.pow_mod, Nat.pow_mod p 2 3, hp]
  norm_num

theorem pow_mod_three_of_odd {p k : ℕ} (hp : p % 3 = 2) (hk : Odd k) : p ^ k % 3 = 2 := by
  obtain ⟨i, rfl⟩ := hk
  rw [pow_succ, Nat.mul_mod, pow_mod_three_of_even hp (even_two_mul i), hp]

theorem mod_three_eq_two {p f : ℕ} (hf : 1 ≤ f) (hq : p ^ f % 3 = 2) : p % 3 = 2 := by
  rw [Nat.pow_mod] at hq
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · rw [h, zero_pow (by omega)] at hq
    norm_num at hq
  · rw [h, one_pow] at hq
    norm_num at hq
  · exact h

theorem odd_of_pow_mod_three {p f : ℕ} (hf : 1 ≤ f) (hq : p ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with he | ho
  · have := pow_mod_three_of_even (mod_three_eq_two hf hq) he
    omega
  · exact ho

end Arith

variable {p f : ℕ} {K : Type} [Field K]

theorem glAut_eq_frobGL (σ : K ≃+* K) (g : GL (Fin 3) K) : glAut σ g = frobGL σ g :=
  Units.ext (by rw [coe_glAut, coe_frobGL])

theorem glAut_mem_glPi (hK : PiField false p f K) (σ : K ≃+* K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi false 3 (p ^ f) K) : glAut σ g ∈ glPi false 3 (p ^ f) K := by
  rw [glAut_eq_frobGL]
  exact frobGL_mem_glPi hK σ hg

theorem glAut_mem_slPi (hK : PiField false p f K) (σ : K ≃+* K) {g : GL (Fin 3) K}
    (hg : g ∈ slPi false 3 (p ^ f) K) : glAut σ g ∈ slPi false 3 (p ^ f) K := by
  rw [glAut_eq_frobGL]
  exact frobGL_mem_slPi hK σ hg

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  rw [glAut_eq_frobGL, frobGL_scalar]

theorem exists_pow_eq (hK : PiField false p f K) {α : MulAut ↥(slPi false 3 (p ^ f) K)}
    {A : GL (Fin 3) K} (hA : A ∈ glPi false 3 (p ^ f) K) {σ : K ≃+* K}
    (hα : ∀ s : ↥(slPi false 3 (p ^ f) K), ((α s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) =
      A * glAut σ (s : GL (Fin 3) K) * A⁻¹) (m : ℕ) :
    ∃ B ∈ glPi false 3 (p ^ f) K, ∀ s : ↥(slPi false 3 (p ^ f) K),
      (((α ^ m) s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) =
        B * glAut (σ ^ m) (s : GL (Fin 3) K) * B⁻¹ := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun s => by simp⟩
  | succ m ih =>
    obtain ⟨B, hB, hBs⟩ := ih
    refine ⟨B * glAut (σ ^ m) A, mul_mem hB (glAut_mem_glPi hK _ hA), fun s => ?_⟩
    rw [pow_succ, MulAut.mul_apply, hBs, hα, map_mul, map_mul, map_inv, pow_succ, map_mul,
      MulAut.mul_apply]
    group

theorem exists_scalar_conj (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {y : GL (Fin 3) K} (hy : y ∈ glPi false 3 (p ^ f) K)
    {α : MulAut ↥(slPi false 3 (p ^ f) K)} {A : GL (Fin 3) K} {σ : K ≃+* K}
    (hα : ∀ s : ↥(slPi false 3 (p ^ f) K), ((α s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) =
      A * glAut σ (s : GL (Fin 3) K) * A⁻¹)
    (hcomm : ∀ s t : ↥(slPi false 3 (p ^ f) K), (t : GL (Fin 3) K) = y * s * y⁻¹ →
      ((α t : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) = y * α s * y⁻¹) :
    ∃ μ : Kˣ, A * glAut σ y * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * y := by
  have h := hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hc : (y * A)⁻¹ * (A * glAut σ y) ∈
      Subgroup.centralizer (slPi false 3 (p ^ f) K : Set (GL (Fin 3) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hs : glAut σ⁻¹ x ∈ slPi false 3 (p ^ f) K := glAut_mem_slPi hK σ⁻¹ hx
    have hsx : glAut σ (glAut σ⁻¹ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hyU : y ∈ unitaryIsom3 h := (mem_glPi_false h).1 hy
    have ht : y * glAut σ⁻¹ x * y⁻¹ ∈ slPi false 3 (p ^ f) K := conj_mem_unitarySU hyU hs
    have e0 := hcomm ⟨_, hs⟩ ⟨_, ht⟩ rfl
    rw [hα, hα] at e0
    have e1 : glAut σ (y * glAut σ⁻¹ x * y⁻¹) = glAut σ y * x * (glAut σ y)⁻¹ := by
      rw [map_mul, map_mul, hsx, map_inv]
    have e : A * (glAut σ y * x * (glAut σ y)⁻¹) * A⁻¹ = y * (A * x * A⁻¹) * y⁻¹ := by
      calc A * (glAut σ y * x * (glAut σ y)⁻¹) * A⁻¹
          = A * glAut σ (y * glAut σ⁻¹ x * y⁻¹) * A⁻¹ := by rw [e1]
        _ = y * (A * glAut σ (glAut σ⁻¹ x) * A⁻¹) * y⁻¹ := e0
        _ = y * (A * x * A⁻¹) * y⁻¹ := by rw [hsx]
    calc x * ((y * A)⁻¹ * (A * glAut σ y))
        = (y * A)⁻¹ * (y * (A * x * A⁻¹) * y⁻¹) * (A * glAut σ y) := by group
      _ = (y * A)⁻¹ * (A * (glAut σ y * x * (glAut σ y)⁻¹) * A⁻¹) * (A * glAut σ y) := by
          rw [e]
      _ = (y * A)⁻¹ * (A * glAut σ y) * x := by group
  rw [centralizer_slPi (fun _ => h) (fun _ => hq) hτ hτ1] at hc
  obtain ⟨μ, hμ⟩ := hc
  refine ⟨μ, ?_⟩
  have e2 : A * glAut σ y = y * A * GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [hμ]
    group
  have hcA : A * GeneralLinearGroup.scalar (Fin 3) μ = GeneralLinearGroup.scalar (Fin 3) μ * A :=
    (commute_scalar μ A).eq
  have hcy : y * GeneralLinearGroup.scalar (Fin 3) μ = GeneralLinearGroup.scalar (Fin 3) μ * y :=
    (commute_scalar μ y).eq
  calc A * glAut σ y * A⁻¹ = y * (A * GeneralLinearGroup.scalar (Fin 3) μ) * A⁻¹ := by
        rw [e2]
        group
    _ = GeneralLinearGroup.scalar (Fin 3) μ * y := by
        rw [hcA, ← mul_assoc, hcy]
        group

theorem map_eq_cube_mul {y A : GL (Fin 3) K} {σ : K ≃+* K} {μ ℓ : Kˣ}
    (hμ : A * glAut σ y * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * y)
    (hℓ : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ : K) • 1) :
    σ (ℓ : K) = (μ : K) ^ 3 * ℓ := by
  have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) ℓ :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hℓ, coe_scalar_eq_smul])
  have h3 : (A * glAut σ y * A⁻¹) ^ 3 = (GeneralLinearGroup.scalar (Fin 3) μ * y) ^ 3 := by
    rw [hμ]
  rw [conj_pow, ← map_pow, hy3, glAut_scalar,
    (commute_scalar (Units.map (σ : K →* K) ℓ) A).eq, mul_assoc, mul_inv_cancel, mul_one,
    (commute_scalar μ y).symm.mul_pow, hy3, ← map_pow, ← map_mul] at h3
  have h4 := congrArg Units.val (scalar_injective_three h3)
  rw [Units.coe_map, Units.val_mul, Units.val_pow_eq_pow_val] at h4
  exact h4

theorem pow_eq_one (hK : PiField false p f K) (hq : ModThree false (p ^ f)) {σ : K ≃+* K}
    {ℓ μ : K} (hℓ0 : ℓ ≠ 0) (hnc : ∀ ν : K, ν ^ 3 ≠ ℓ) (hσ : σ ℓ = μ ^ 3 * ℓ) : σ ^ f = 1 := by
  have h := hK.unitary
  have hf := hK.one_le
  have hq' : p ^ f % 3 = 2 := hq
  obtain ⟨k, -, hk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hK.prime
    (by omega : 1 ≤ 2 * f) h.card σ
  have hp3 := mod_three_eq_two hf hq'
  have hke : Even k := by
    rcases Nat.even_or_odd k with he | ho
    · exact he
    · exfalso
      have hpk : p ^ k = 3 * (p ^ k / 3) + 2 := by
        have := Nat.div_add_mod (p ^ k) 3
        rw [pow_mod_three_of_odd hp3 ho] at this
        omega
      set m := p ^ k / 3
      have e : ℓ ^ (3 * m) * ℓ * ℓ = μ ^ 3 * ℓ := by
        rw [← hσ, hk, hpk]
        ring
      have e' : ℓ ^ (3 * m) * ℓ = μ ^ 3 := mul_right_cancel₀ hℓ0 e
      apply hnc (μ * (ℓ ^ m)⁻¹)
      have hℓm : ℓ ^ (3 * m) ≠ 0 := pow_ne_zero _ hℓ0
      calc (μ * (ℓ ^ m)⁻¹) ^ 3 = μ ^ 3 * (ℓ ^ (3 * m))⁻¹ := by
            rw [mul_pow, inv_pow, ← pow_mul, mul_comm m 3]
        _ = ℓ := by
            rw [← e', mul_comm (ℓ ^ (3 * m)) ℓ, mul_assoc, mul_inv_cancel₀ hℓm, mul_one]
  obtain ⟨j, rfl⟩ := hke
  have hpow : ∀ (n : ℕ) (a : K), (σ ^ n) a = a ^ ((p ^ (j + j)) ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', RingAut.mul_apply, ih, hk, ← pow_mul, pow_succ]
  have := h.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
  refine RingEquiv.ext fun a => ?_
  rw [hpow, RingAut.one_apply,
    show (p ^ (j + j)) ^ f = (Fintype.card K) ^ j by rw [hcard, ← pow_mul, ← pow_mul]; ring_nf]
  exact FiniteField.pow_card_pow j a

end P614K292U

open P614K292U

theorem kD292UniOuter3_holds : KD292UniOuter3 := by
  intro p f K _ y hK hq h2 hT α ⟨n, hn⟩ hcomm
  obtain ⟨A, hA, σ, hα⟩ := exists_semilinear hK h2 α
  obtain ⟨μ, hμ⟩ := exists_scalar_conj hK hq hT.mem hα hcomm
  obtain ⟨ℓ, hℓ, hnc⟩ := hT.not_cube hK hq
  have hσf : σ ^ f = 1 := pow_eq_one hK hq ℓ.ne_zero hnc (map_eq_cube_mul hμ hℓ)
  have hfodd : Odd f := odd_of_pow_mod_three hK.one_le hq
  have hcop : f.Coprime (orderOf α) :=
    (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hfodd)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  obtain ⟨B, hB, hBs⟩ := exists_pow_eq hK hA hα (f * u)
  refine ⟨B, hB, fun s => ?_⟩
  rw [← hu, ← pow_mul, hBs, pow_mul, hσf, one_pow, map_one, MulAut.one_apply]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
