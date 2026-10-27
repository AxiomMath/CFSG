module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Rank

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem isUnit_det_of_linearIndependent {b : Fin 3 → (Fin 3 → GF64)}
    (hb : LinearIndependent GF64 b) : IsUnit (Matrix.of fun r i => b i r : Matrix (Fin 3) (Fin 3)
      GF64).det := by
  have hcols : (Matrix.of fun r i => b i r : Matrix (Fin 3) (Fin 3) GF64).col = b := by
    funext i r
    rfl
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit, hcols]
  exact hb

theorem mul_eigenmatrix {M : Matrix (Fin 3) (Fin 3) GF64} {b : Fin 3 → (Fin 3 → GF64)}
    {c : Fin 3 → GF64} (hM : ∀ i, M *ᵥ b i = c i • b i) :
    M * (Matrix.of fun r i => b i r : Matrix (Fin 3) (Fin 3) GF64) =
      (Matrix.of fun r i => b i r : Matrix (Fin 3) (Fin 3) GF64) * Matrix.diagonal c := by
  refine Matrix.ext fun r i => ?_
  have := congrFun (hM i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

theorem det_eq_prod_of_eigenbasis {M : Matrix (Fin 3) (Fin 3) GF64} {b : Fin 3 → (Fin 3 → GF64)}
    (hb : LinearIndependent GF64 b) {c : Fin 3 → GF64} (hM : ∀ i, M *ᵥ b i = c i • b i) :
    M.det = c 0 * c 1 * c 2 := by
  have hdet := congrArg Matrix.det (mul_eigenmatrix hM)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have hu := isUnit_det_of_linearIndependent hb
  rw [mul_comm] at hdet
  exact mul_left_cancel₀ hu.ne_zero hdet

theorem det_pow_nine_of_mem_GU {h : GL (Fin 3) GF64} (hh : h ∈ GU) :
    ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ^ 9 = 1 := by
  have h1 : (((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).map hU.bar)ᵀ *
      (h : Matrix (Fin 3) (Fin 3) GF64) = 1 := hh
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  have h3 := RingHom.map_det hU.bar (h : Matrix (Fin 3) (Fin 3) GF64)
  rw [RingHom.mapMatrix_apply] at h3
  rw [← h3, bar_apply_eq, barC_eq_pow] at h2
  calc ((h : Matrix (Fin 3) (Fin 3) GF64)).det ^ 9
      = (h : Matrix (Fin 3) (Fin 3) GF64).det ^ 8 * (h : Matrix (Fin 3) (Fin 3) GF64).det := by ring
    _ = 1 := h2

theorem det_pow_three_of_eigenbasis {h : GL (Fin 3) GF64} (hh : h ∈ GU) {ν : GF64} (hν0 : ν ≠ 0)
    (hν : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) ^ 3 = ν • 1)
    {b : Fin 3 → (Fin 3 → GF64)} (hb : LinearIndependent GF64 b)
    (hbh : ∀ i, ∃ c : GF64,
      ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) *ᵥ b i = c • b i) :
    ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ^ 3 = 1 := by
  choose c hc using hbh
  have hdet := det_eq_prod_of_eigenbasis hb hc
  have hcν : ∀ i, c i ^ 3 = ν := by
    intro i
    have h1 := pow_mulVec_of_eigen (hc i) 3
    rw [hν, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    have hbi : b i ≠ 0 := hb.ne_zero i
    have := smul_left_injective GF64 hbi h1
    exact this.symm
  have hc0 : c 0 ≠ 0 := by
    intro h0
    apply hν0
    rw [← hcν 0, h0]
    norm_num
  have h63 : ν ^ 21 = 1 := by
    rw [← hcν 0, ← pow_mul]
    have := FiniteField.pow_card_sub_one_eq_one (c 0) hc0
    rwa [show Fintype.card GF64 = 64 from by rw [← Nat.card_eq_fintype_card]; exact card_eq] at this
  have h9 : ν ^ 9 = 1 := by
    have := det_pow_nine_of_mem_GU hh
    rw [hdet] at this
    calc ν ^ 9 = (c 0 ^ 3 * c 1 ^ 3 * c 2 ^ 3) ^ 3 := by rw [hcν, hcν, hcν]; ring
      _ = (c 0 * c 1 * c 2) ^ 9 := by ring
      _ = 1 := this
  rw [hdet]
  calc (c 0 * c 1 * c 2) ^ 3 = c 0 ^ 3 * c 1 ^ 3 * c 2 ^ 3 := by ring
    _ = ν ^ 3 := by rw [hcν, hcν, hcν]; ring
    _ = ν ^ 3 * (ν ^ 9) ^ 2 := by rw [h9]; ring
    _ = ν ^ 21 := by ring
    _ = 1 := h63

theorem scalar_injective' :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) : GF64ˣ →* GL (Fin 3) GF64) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 3) GF64 => (g : Matrix (Fin 3) (Fin 3) GF64) 0 0) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem pow_nine_of_scalar_mem_GU {c : GF64ˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ GU) : (c : GF64) ^ 9 = 1 := by
  have h1 : (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) GF64) :
      Matrix (Fin 3) (Fin 3) GF64).map hU.bar)ᵀ *
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) GF64) :
        Matrix (Fin 3) (Fin 3) GF64) = 1 := hc
  have h2 := congrFun (congrFun h1 0) 0
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at h2
  simp [bar_apply_eq, barC_eq_pow] at h2
  calc (c : GF64) ^ 9 = c ^ 8 * c := by ring
    _ = 1 := by simpa using h2

@[expose] def omegaC : GF64 := GF64.ofNat' 8

theorem omegaC_cube : omegaC ^ 3 = 1 := by decide +kernel

theorem omegaC_ne_one : omegaC ≠ 1 := by decide +kernel

theorem scalarCommute (c : GF64ˣ) (g : GL (Fin 3) GF64) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) c) g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem exists_scalar_of_mk_eq {y s : GL (Fin 3) GF64}
    (h : (s : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) = y) :
    ∃ c : GF64ˣ, y = s * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨c, hc⟩ := QuotientGroup.eq.1 h
  exact ⟨c, by rw [hc]; group⟩

theorem zeta_eq_one_of_commute {s₁ s₂ y₁ y₂ : GL (Fin 3) GF64} {ζ : GF64ˣ}
    (hs : Commute s₁ s₂)
    (h₁ : (s₁ : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) = y₁)
    (h₂ : (s₂ : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) = y₂)
    (hζ : y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂) : ζ = 1 := by
  obtain ⟨c₁, rfl⟩ := exists_scalar_of_mk_eq h₁
  obtain ⟨c₂, rfl⟩ := exists_scalar_of_mk_eq h₂
  have hc : Commute (s₁ * Matrix.GeneralLinearGroup.scalar (Fin 3) c₁)
      (s₂ * Matrix.GeneralLinearGroup.scalar (Fin 3) c₂) :=
    (hs.mul_right (scalarCommute c₂ _).symm).mul_left
      ((scalarCommute c₁ _).mul_right (scalarCommute c₁ _))
  rw [hc.mul_inv_cancel] at hζ
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 3) ζ = 1 := mul_eq_right.mp hζ.symm
  exact scalar_injective' (h1.trans (map_one _).symm)

theorem false_of_commuting_outer {h a : GL (Fin 3) GF64} (hh : h ∈ GU) (ha : a ∈ SU)
    (haS : a ∉ StatedScalars (Fin 3) GF64) (ha3 : a ^ 3 = 1)
    (hh3 : h ^ 3 ∈ StatedScalars (Fin 3) GF64)
    (hhd : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ^ 3 ≠ 1)
    (hcomm : a * h = h * a) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haGU : a ∈ GU := unitarySU_le_unitaryIsom3 ha
  have hab3 : (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ha3, QuotientGroup.mk_one]
  have hhb3 : (h : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hh3
  have hcomm' : Commute (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64)
      (h : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) := by
    show (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) * _ = _ * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Subgroup (GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64),
      E₂ = (pair3Hom _ _ hab3 hhb3 hcomm').range := ⟨_, rfl⟩
  have hmemE : ∀ x : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64, x ∈ E₂ ↔
      ∃ t, pair3Hom _ _ hab3 hhb3 hcomm' t = x := by
    intro x
    rw [hE₂]
    exact MonoidHom.mem_range
  have haE : (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ∈ E₂ :=
    (hmemE _).2 ⟨(Multiplicative.ofAdd 1, 1), by
      rw [pair3Hom_apply]
      simp [val_one3]⟩
  have hhE : (h : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ∈ E₂ :=
    (hmemE _).2 ⟨(1, Multiplicative.ofAdd 1), by
      rw [pair3Hom_apply]
      simp [val_one3]⟩
  have hcommE : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨t, rfl⟩ := (hmemE x).1 hx
    obtain ⟨t', rfl⟩ := (hmemE y).1 hy
    rw [← map_mul, ← map_mul, mul_comm t t']
  have hexpE : ∀ x ∈ E₂, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨t, rfl⟩ := (hmemE x).1 hx
    rw [← map_pow]
    have : t ^ 3 = 1 := Prod.ext (m3_pow_three _) (m3_pow_three _)
    rw [this, map_one]
  have hrep : ∀ y : GL (Fin 3) GF64,
      (y : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ∈ E₂ → ∃ u v : ℕ,
        ((a ^ u * h ^ v : GL (Fin 3) GF64) : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) =
          y := by
    intro y hy
    obtain ⟨t, ht⟩ := (hmemE _).1 hy
    rw [pair3Hom_apply] at ht
    exact ⟨_, _, by rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]; exact ht⟩
  have hhnot : ∀ k : ℤ, (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ^ k ≠ (h : _) := by
    intro k hk
    have hk' : ((a ^ k)⁻¹ * h : GL (Fin 3) GF64) ∈ StatedScalars (Fin 3) GF64 := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
      exact hk
    obtain ⟨c, hc⟩ := hk'
    have hGU : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ GU := by
      rw [hc]
      exact GU.mul_mem (GU.inv_mem (GU.zpow_mem haGU k)) hh
    have hc9 := pow_nine_of_scalar_mem_GU hGU
    apply hhd
    have hdet : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det = (c : GF64) ^ 3 := by
      have h1 : h = a ^ k * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
        rw [hc]; group
      rw [h1, Units.val_mul, Matrix.det_mul, det_scalar_three]
      have hak : ((a ^ k : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det = 1 := by
        have : (a ^ k : GL (Fin 3) GF64) ∈ SU := SU.zpow_mem ha k
        exact (mem_SU_iff'.1 this).1
      rw [hak, one_mul]
    rw [hdet, ← pow_mul]
    exact hc9
  have hcard : 3 < Nat.card E₂ := by
    by_contra hle
    push Not at hle
    have ha1 : (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ≠ 1 := by
      intro h1
      exact haS ((QuotientGroup.eq_one_iff _).1 h1)
    have hord := orderOf_eq_prime hab3 ha1
    have hS : Subgroup.zpowers (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ≤ E₂ := by
      rw [Subgroup.zpowers_le]
      exact haE
    have hcS : Nat.card (Subgroup.zpowers
        (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64)) = 3 := by
      rw [Nat.card_zpowers, hord]
    have heq := Subgroup.eq_of_le_of_card_ge hS (by rw [hcS]; exact hle)
    have : (h : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) ∈
        Subgroup.zpowers (a : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) := by
      rw [heq]; exact hhE
    obtain ⟨k, hk⟩ := this
    exact hhnot k hk
  rcases frame_or_heis three_ne_zero_GF64 omegaC_cube omegaC_ne_one E₂ hcommE hexpE hcard with
    ⟨b, hb, hbE, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · obtain ⟨ν, hν⟩ := hh3
    have hνmat : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) ^ 3 = (ν : GF64) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hν, coe_scalar_eq_smul]
    exact hhd (det_pow_three_of_eigenbasis hh ν.ne_zero hνmat hb (hbE h hhE))
  ·
    have hah : Commute a h := hcomm
    have hm : ∀ u v u' v' : ℕ, Commute (a ^ u * h ^ v) (a ^ u' * h ^ v') := by
      intro u v u' v'
      exact ((Commute.pow_pow_self a u u').mul_right (hah.pow_pow u v')).mul_left
        ((hah.symm.pow_pow v u').mul_right (Commute.pow_pow_self h v v'))
    obtain ⟨u₁, v₁, h₁⟩ := hrep y₁ hy₁
    obtain ⟨u₂, v₂, h₂⟩ := hrep y₂ hy₂
    exact hζ1 (zeta_eq_one_of_commute (hm u₁ v₁ u₂ v₂) h₁ h₂ hζ)

end CFSG.AGLEmbedding.ChevOuter.U38
