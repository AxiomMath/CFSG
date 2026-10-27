module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpLevi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open SymplecticHigher (flagStabilizer fieldSp)

section Aut

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (a : MulAut G) (g : G) :
    a * MulAut.conj g * a⁻¹ = MulAut.conj (a g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [MulAut.apply_inv_self]

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_of_forall_conj_eq {g h : StatedSp r K} (hgh : ∀ x, g * x * g⁻¹ = h * x * h⁻¹) :
    g = h := by
  have hc : h⁻¹ * g ∈ Subgroup.center (StatedSp r K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [hgh x]
      _ = (h⁻¹ * g) * x := by group
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end Aut

section Res

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_forall_commute_spResBlock (m : ℕ) {γ : StatedSp m K}
    (h : ∀ c ∈ spResBlock K m, γ * c = c * γ) : γ = 1 := by
  have hnorm := spResBlock_normal (K := K) m
  have hcomm : ∀ x : StatedSp m K, x * γ * x⁻¹ * γ⁻¹ = 1 := by
    intro x
    refine eq_one_of_commute_spResBlock m
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top γ)) ?_
    intro c hc
    have h1 := h c hc
    have h2 : γ * (x⁻¹ * c * x) = (x⁻¹ * c * x) * γ := by
      have := h _ (hnorm.conj_mem c hc x⁻¹)
      simpa using this
    have h3 : x * γ * x⁻¹ * c = c * (x * γ * x⁻¹) := by
      calc x * γ * x⁻¹ * c = x * (γ * (x⁻¹ * c * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * c * x) * γ) * x⁻¹ := by rw [h2]
        _ = c * (x * γ * x⁻¹) := by group
    have h4 : γ⁻¹ * c = c * γ⁻¹ := by
      calc γ⁻¹ * c = γ⁻¹ * (c * γ) * γ⁻¹ := by group
        _ = γ⁻¹ * (γ * c) * γ⁻¹ := by rw [h1]
        _ = c * γ⁻¹ := by group
    calc x * γ * x⁻¹ * γ⁻¹ * c = x * γ * x⁻¹ * (γ⁻¹ * c) := by group
      _ = x * γ * x⁻¹ * (c * γ⁻¹) := by rw [h4]
      _ = (x * γ * x⁻¹ * c) * γ⁻¹ := by group
      _ = (c * (x * γ * x⁻¹)) * γ⁻¹ := by rw [h3]
      _ = c * (x * γ * x⁻¹ * γ⁻¹) := by group
  have hγ : γ ∈ Subgroup.center (StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := hcomm x
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hγ
  exact hγ

end Res

section Levi

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r)

theorem cutHom_fieldSp_eq_pow {a b : ℕ} (ha : a = 0 ∨ a ∈ I) (hb : b ∈ I) {σ : K ≃+* K} {k : ℕ}
    (hσ : ∀ x, σ x = x ^ 2 ^ k) (g : flagStabilizer r K I)
    (hg : fieldSp r K σ g ∈ flagStabilizer r K I)
    (hz : spFlagCutHom hI ha hb g ∈ Subgroup.center (GL (Fin (b - a)) K)) :
    spFlagCutHom hI ha hb ⟨fieldSp r K σ g, hg⟩ = spFlagCutHom hI ha hb g ^ 2 ^ k := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
  have h1 : (Matrix.scalar (Fin (b - a)) c).map σ = Matrix.scalar (Fin (b - a)) (σ c) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  apply Units.ext
  rw [cutHom_fieldSp hI ha hb σ g hg, Units.val_pow_eq_pow_val, ← hc, h1, hσ, ← map_pow]

theorem leviHom_eq_one_of_conj_field {t : ℕ} (htI : t ∈ I) {σ : K ≃+* K} {k : ℕ}
    (hσ : ∀ x, σ x = x ^ 2 ^ k) (g' g : flagStabilizer r K I)
    (hg : fieldSp r K σ g ∈ flagStabilizer r K I)
    (hcut : ∀ (b : ℕ) (hb : b ∈ I), spFlagCutHom hI (spFlagPrev_mem I b) hb g ∈
      Subgroup.center (GL (Fin (b - spFlagPrev I b)) K))
    (hres : spFlagResHom hI htI g = 1) :
    spFlagLeviHom hI htI (g' * ⟨fieldSp r K σ g, hg⟩ * g'⁻¹ * (g ^ 2 ^ k)⁻¹) = 1 := by
  refine leviHom_eq_one_of_blocks hI htI (fun b hb => ?_) ?_
  · simp only [map_mul, map_inv, map_pow]
    rw [cutHom_fieldSp_eq_pow hI _ hb hσ g hg (hcut b hb)]
    have hzc := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (hcut b hb) (2 ^ k))
      (spFlagCutHom hI (spFlagPrev_mem I b) hb g')
    calc spFlagCutHom hI (spFlagPrev_mem I b) hb g' *
          spFlagCutHom hI (spFlagPrev_mem I b) hb g ^ 2 ^ k *
          (spFlagCutHom hI (spFlagPrev_mem I b) hb g')⁻¹ *
          (spFlagCutHom hI (spFlagPrev_mem I b) hb g ^ 2 ^ k)⁻¹
        = spFlagCutHom hI (spFlagPrev_mem I b) hb g ^ 2 ^ k *
          spFlagCutHom hI (spFlagPrev_mem I b) hb g' *
          (spFlagCutHom hI (spFlagPrev_mem I b) hb g')⁻¹ *
          (spFlagCutHom hI (spFlagPrev_mem I b) hb g ^ 2 ^ k)⁻¹ := by rw [hzc]
      _ = 1 := by group
  · simp only [map_mul, map_inv, map_pow]
    rw [resHom_fieldSp' hI htI σ g hg, hres, map_one]
    simp

end Levi

section Model

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}

theorem exists_pow_two_eq_one_conj_fieldSp (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I)
    {σ : K ≃+* K} {k : ℕ} (hσ : ∀ x, σ x = x ^ 2 ^ k) (g' g : flagStabilizer r K I)
    (hcut : ∀ (b : ℕ) (hb : b ∈ I), spFlagCutHom (fun i hi => (hI i hi).2)
      (spFlagPrev_mem I b) hb g ∈ Subgroup.center (GL (Fin (b - spFlagPrev I b)) K))
    (hres : spFlagResHom (fun i hi => (hI i hi).2) htI g = 1) :
    ∃ j : ℕ, ((MulAut.conj (g' : StatedSp r K) * fieldSp r K σ) *
      MulAut.conj (g : StatedSp r K) * (MulAut.conj (g' : StatedSp r K) * fieldSp r K σ)⁻¹ *
        (MulAut.conj (g : StatedSp r K) ^ (((2 ^ k : ℕ)) : ℤ))⁻¹) ^ 2 ^ j = 1 := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hg : fieldSp r K σ g ∈ flagStabilizer r K I := fieldSp_mem_flagStabilizer hI₀ σ g.2
  set D : flagStabilizer r K I := g' * ⟨fieldSp r K σ g, hg⟩ * g'⁻¹ * (g ^ 2 ^ k)⁻¹ with hD
  have hDker : D ∈ (spFlagLeviHom hI₀ htI).ker :=
    MonoidHom.mem_ker.mpr (leviHom_eq_one_of_conj_field hI₀ htI hσ g' g hg hcut hres)
  obtain ⟨j, hj⟩ := isPGroup_ker_spFlagLeviHom hI₀ htI (fun i hi => (hI i hi).1) ⟨D, hDker⟩
  refine ⟨j, ?_⟩
  have hpow : D ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hpow' : (D : StatedSp r K) ^ 2 ^ j = 1 := by
    have := congrArg (flagStabilizer r K I).subtype hpow
    simpa using this
  have hX : (MulAut.conj (g' : StatedSp r K) * fieldSp r K σ) * MulAut.conj (g : StatedSp r K) *
      (MulAut.conj (g' : StatedSp r K) * fieldSp r K σ)⁻¹ *
        (MulAut.conj (g : StatedSp r K) ^ (((2 ^ k : ℕ)) : ℤ))⁻¹ =
      MulAut.conj (D : StatedSp r K) := by
    rw [mulAut_mul_conj_mul_inv, zpow_natCast, ← map_pow, ← map_inv, ← map_mul]
    congr 1
  rw [hX, ← map_pow, hpow', map_one]

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp
