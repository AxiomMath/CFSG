module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvL4Arith
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane Matrix
open scoped commutatorElement

@[expose] def OutOddCentral (Y : Type) [Group Y] : Prop :=
  ∀ (β α : MulAut Y) (m : ℕ), Odd m → β ^ m = 1 →
    β * α * β⁻¹ * α⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range

theorem outOddCentral_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : OutOddCentral Y) : OutOddCentral Y' := by
  intro β α m hm hβm
  have h1 := h (MulAut.congr e.symm β) (MulAut.congr e.symm α) m hm
    (by rw [← map_pow, hβm, map_one])
  obtain ⟨g, hg⟩ := h1
  refine ⟨e g, ?_⟩
  ext y
  have := congrArg (fun σ : MulAut Y => e (σ (e.symm y))) hg
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply] at this ⊢
  simpa [map_mul, map_inv] using this

theorem comm_mem_sup_centralizer_of_odd {A : Type} [Group A] (K : Subgroup A) [K.Normal]
    (hOut : OutOddCentral ↥K) (a b : A) (m : ℕ) (hm : Odd m) (ha : a ^ m = 1) :
    ⁅a, b⁆ ∈ K ⊔ centralizer (K : Set A) := by
  let ρ : A →* MulAut ↥K := MulAut.conjNormal
  obtain ⟨k, hk⟩ := hOut (ρ a) (ρ b) m hm (by rw [← map_pow, ha, map_one])
  have hρ : ρ ⁅a, b⁆ = ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹ := by
    simp only [commutatorElement_def, map_mul, map_inv]
  have hc : (k : A)⁻¹ * ⁅a, b⁆ ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨y, hy⟩ : ↥K) : A)) (hk.trans hρ.symm)
    simp only [MulAut.conj_apply] at h1
    have h2 : (k : A) * y * (k : A)⁻¹ = ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ := h1
    calc y * ((k : A)⁻¹ * ⁅a, b⁆) = (k : A)⁻¹ * ((k : A) * y * (k : A)⁻¹) * ⁅a, b⁆ := by group
      _ = (k : A)⁻¹ * (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h2]
      _ = (k : A)⁻¹ * ⁅a, b⁆ * y := by group
  have : ⁅a, b⁆ = (k : A) * ((k : A)⁻¹ * ⁅a, b⁆) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hc)

theorem outOddCentral_projectiveSL4 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hfodd : Odd f) (hcard : Nat.card F = p ^ f) :
    OutOddCentral (projectiveSL 4 F) := by
  intro β α m hm hβm
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set I := (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range
  have hInorm : ∀ φ : MulAut (projectiveSL 4 F), ∀ i ∈ I, φ * i * φ⁻¹ ∈ I := by
    rintro φ _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  obtain ⟨C, τ, η, hη, hβ⟩ := (automorphism_generation (K := F) (n := 4) (by norm_num)).2 β
  obtain ⟨A, σ, ε, -, hα⟩ := (automorphism_generation (K := F) (n := 4) (by norm_num)).2 α
  have hη0 : η = 0 := by
    by_contra hne
    have hη1 : η = 1 := by omega
    subst hη1
    rw [pow_one] at hβ
    have hβ2 : β ^ 2 ∈ semilinearAutGroup 4 F := by
      rw [hβ, sq_conjAut_fieldAut_dualAut]
      exact mem_semilinearAutGroup_iff.mpr ⟨_, _, rfl⟩
    obtain ⟨r, hr⟩ := hm
    have hβE : β ∈ semilinearAutGroup 4 F := by
      have h1 : β = ((β ^ 2) ^ r)⁻¹ := by
        rw [hr, pow_succ, pow_mul] at hβm
        exact (eq_inv_of_mul_eq_one_right hβm)
      rw [h1]
      exact inv_mem (pow_mem hβ2 r)
    have hCf : conjAut 4 F C * fieldAut 4 F τ ∈ semilinearAutGroup 4 F :=
      mem_semilinearAutGroup_iff.mpr ⟨_, _, rfl⟩
    apply dualAut_not_mem_semilinearAutGroup (K := F) (n := 4) (by norm_num)
    have : dualAut 4 F = (conjAut 4 F C * fieldAut 4 F τ)⁻¹ * β := by
      rw [hβ]; group
    rw [this]
    exact mul_mem (inv_mem hCf) hβE
  subst hη0
  rw [pow_zero, mul_one] at hβ
  obtain ⟨kτ, hτk⟩ := exists_pow_frob hp hf hcard τ
  obtain ⟨kσ, hσk⟩ := exists_pow_frob hp hf hcard σ
  have hodd_pow : ∀ j : ℕ, p ^ j % 2 = 1 := fun j => Nat.odd_iff.mp hpodd.pow
  have hCI : conjAut 4 F C ∈ I := by
    obtain ⟨N, S, hNpow, hdet, hS⟩ := exists_pow_conjAut_fieldAut C τ hτk (hodd_pow kτ) m
    rw [← hβ, hβm] at hNpow
    obtain ⟨-, z, hz⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) N (τ ^ m) hNpow.symm
    have hdz : GeneralLinearGroup.det N = z ^ 4 := by
      rw [← hz, GeneralLinearGroup.det_scalar, Fintype.card_fin]
    rw [hdet] at hdz
    obtain ⟨y, hy⟩ := exists_pow_four_of_odd_pow (by rw [hS]; exact Nat.odd_iff.mp hm) hdz
    exact conjAut_mem_range_conj_of_det_four hy
  have hfτσ : fieldAut 4 F τ * fieldAut 4 F σ = fieldAut 4 F σ * fieldAut 4 F τ := by
    rw [← map_mul, ← map_mul]
    congr 1
    ext x
    simp only [RingAut.mul_apply, hτk, hσk, ← pow_mul, ← pow_add, add_comm]
  have hfτδ : ∀ e : ℕ, fieldAut 4 F τ * dualAut 4 F ^ e = dualAut 4 F ^ e * fieldAut 4 F τ := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, ← dualAut_mul_fieldAut]
  have hXI : fieldAut 4 F τ * α * (fieldAut 4 F τ)⁻¹ * α⁻¹ ∈ I := by
    have h1 : fieldAut 4 F τ * α = conjAut 4 F (GeneralLinearGroup.map (τ : F →+* F) A) *
        (fieldAut 4 F σ * dualAut 4 F ^ ε) * fieldAut 4 F τ := by
      rw [hα]
      calc fieldAut 4 F τ * (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F ^ ε)
          = (fieldAut 4 F τ * conjAut 4 F A) * fieldAut 4 F σ * dualAut 4 F ^ ε := by group
        _ = conjAut 4 F (GeneralLinearGroup.map (τ : F →+* F) A) *
              (fieldAut 4 F τ * fieldAut 4 F σ) * dualAut 4 F ^ ε := by
            rw [fieldAut_mul_conjAut]; group
        _ = conjAut 4 F (GeneralLinearGroup.map (τ : F →+* F) A) * fieldAut 4 F σ *
              (fieldAut 4 F τ * dualAut 4 F ^ ε) := by rw [hfτσ]; group
        _ = conjAut 4 F (GeneralLinearGroup.map (τ : F →+* F) A) * fieldAut 4 F σ *
              (dualAut 4 F ^ ε * fieldAut 4 F τ) := by rw [hfτδ ε]
        _ = _ := by group
    have h2 : fieldAut 4 F τ * α * (fieldAut 4 F τ)⁻¹ * α⁻¹ =
        conjAut 4 F (GeneralLinearGroup.map (τ : F →+* F) A * A⁻¹) := by
      rw [h1, map_mul, map_inv]
      conv_lhs => rw [hα]
      generalize dualAut 4 F ^ ε = D
      generalize fieldAut 4 F σ = Fσ
      generalize fieldAut 4 F τ = Fτ
      group
    rw [h2]
    obtain ⟨y, hy⟩ := exists_pow_four_of_frob hp hp2 hfodd hcard kτ (GeneralLinearGroup.det A)
    refine conjAut_mem_range_conj_of_det_four (y := y) ?_
    rw [map_mul, map_inv, GeneralLinearGroup.map_det]
    have hu : Units.map ((τ : F →+* F) : F →* F) (GeneralLinearGroup.det A) =
        (GeneralLinearGroup.det A) ^ (p ^ kτ) := Units.ext (by simp [hτk])
    rw [hu, hy, mul_comm (GeneralLinearGroup.det A), mul_assoc, mul_inv_cancel, mul_one]
  have e1 : β * α * β⁻¹ * α⁻¹ = conjAut 4 F C * (fieldAut 4 F τ * α * (fieldAut 4 F τ)⁻¹ * α⁻¹) *
      (α * conjAut 4 F C * α⁻¹)⁻¹ := by
    rw [hβ]; group
  rw [e1]
  exact mul_mem (mul_mem hCI hXI) (inv_mem (hInorm α _ hCI))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
