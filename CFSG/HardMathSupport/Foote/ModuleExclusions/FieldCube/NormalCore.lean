module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

set_option linter.unusedSectionVars false

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

@[expose] def innAut (F : Type) [Field F] : Subgroup (MulAut (projectiveSL 3 F)) :=
  (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range

theorem innAut_le_linear : innAut F ≤ linearAutGroup 3 F := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

theorem ringAut_commute (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcyc : IsCyclic (RingAut F) :=
    (card_ringAut_and_isCyclic hp F (by rw [Nat.card_eq_fintype_card]; exact hn)).2
  exact (IsCyclic.commGroup (α := RingAut F)).mul_comm σ τ

theorem conjAut_pow_three_mem_inn (A : GL (Fin 3) F) : conjAut 3 F A ^ 3 ∈ innAut F := by
  set l : Fˣ := Matrix.GeneralLinearGroup.det A with hl
  set B : GL (Fin 3) F := (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ * A ^ 3 with hB
  have hdet : (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : ((GeneralLinearGroup.scalar (Fin 3) l)⁻¹ : GL (Fin 3) F) =
        GeneralLinearGroup.scalar (Fin 3) l⁻¹ := (map_inv _ _).symm
    rw [hB, Units.val_mul, Matrix.det_mul, h1, GeneralLinearGroup.coe_scalar]
    have e1 : (Matrix.scalar (Fin 3) ((l⁻¹ : Fˣ) : F)).det = (((l⁻¹ : Fˣ) : F)) ^ 3 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]; simp
    have e2 : ((A ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = (l : F) ^ 3 := by
      rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
      simp [hl, Matrix.GeneralLinearGroup.val_det_apply]
    rw [e1, e2, Units.val_inv_eq_inv_val]
    have : (l : F) ≠ 0 := l.ne_zero
    field_simp
  set S : SL(3, F) := ⟨(B : Matrix (Fin 3) (Fin 3) F), hdet⟩ with hS
  have hSB : SpecialLinearGroup.toGL S = B := Units.ext rfl
  have hA3 : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) l * B := by
    rw [hB]; group
  rw [← map_pow, hA3, map_mul, conjAut_scalar, one_mul, ← hSB, conjAut_toGL]
  exact ⟨proj 3 F S, rfl⟩

theorem sq_mem_semilinear (x : MulAut (projectiveSL 3 F)) : x ^ 2 ∈ semilinearAutGroup 3 F := by
  have hR : x ∈ standardAutGroup 3 F := by
    rw [(automorphism_generation (n := 3) (K := F) le_rfl).1]; trivial
  rcases mem_or_mul_dualAut_mem hR with h | h
  · rw [pow_two]; exact mul_mem h h
  · have hδδ := (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
    have hx : x = (x * dualAut 3 F) * dualAut 3 F := by rw [mul_assoc, hδδ, mul_one]
    have : x ^ 2 = (x * dualAut 3 F) * (dualAut 3 F * (x * dualAut 3 F) * dualAut 3 F) := by
      generalize x * dualAut 3 F = e at hx ⊢
      rw [hx, pow_two]
      group
    rw [this]
    exact mul_mem h (dualAut_mul_mul_dualAut_mem h)

theorem mem_semilinear_of_pow_mem {x : MulAut (projectiveSL 3 F)} {m : ℕ}
    (hx : x ^ (2 * m + 1) ∈ semilinearAutGroup 3 F) : x ∈ semilinearAutGroup 3 F := by
  have h2 : (x ^ 2) ^ m ∈ semilinearAutGroup 3 F := pow_mem (sq_mem_semilinear x) m
  have : x = x ^ (2 * m + 1) * ((x ^ 2) ^ m)⁻¹ := by
    rw [← pow_mul, pow_succ, mul_comm 2 m]
    group
  rw [this]
  exact mul_mem hx (inv_mem h2)

theorem fieldAut_mem_linear_iff {σ : F ≃+* F} (h : fieldAut 3 F σ ∈ linearAutGroup 3 F) :
    σ = 1 := by
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 h
  have h1 : conjAut 3 F B⁻¹ * fieldAut 3 F σ = 1 := by
    rw [← hB, map_inv, inv_mul_cancel]
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _ h1).1

theorem sigma_pow_eq_one_of_pow_mem_inn {A : GL (Fin 3) F} {σ : F ≃+* F} {n : ℕ}
    (h : (conjAut 3 F A * fieldAut 3 F σ) ^ n ∈ innAut F) : σ ^ n = 1 := by
  rw [conj_fieldAut_pow] at h
  have hD := innAut_le_linear h
  have : fieldAut 3 F (σ ^ n) ∈ linearAutGroup 3 F := by
    have h2 : (conjAut 3 F (AiG σ A n))⁻¹ * (conjAut 3 F (AiG σ A n) * fieldAut 3 F σ ^ n) ∈
        linearAutGroup 3 F :=
      mul_mem (inv_mem (conjAut_mem_linearAutGroup _)) hD
    rw [map_pow]
    simpa using h2
  exact fieldAut_mem_linear_iff this

theorem exists_mul_pow_mem_inn {x y : MulAut (projectiveSL 3 F)} {a b : ℕ}
    (hx : x ^ 3 ^ a ∈ innAut F) (hy : y ^ 3 ^ b ∈ innAut F) :
    (x * y) ^ 3 ^ (a + b + 1) ∈ innAut F := by
  have hodd : ∀ c : ℕ, ∃ m, 3 ^ c = 2 * m + 1 := fun c =>
    Odd.exists_bit1 ((by decide : Odd 3).pow)
  have hxE : x ∈ semilinearAutGroup 3 F := by
    obtain ⟨m, hm⟩ := hodd a
    rw [hm] at hx
    exact mem_semilinear_of_pow_mem
      (linearAutGroup_le_semilinearAutGroup (innAut_le_linear hx))
  have hyE : y ∈ semilinearAutGroup 3 F := by
    obtain ⟨m, hm⟩ := hodd b
    rw [hm] at hy
    exact mem_semilinear_of_pow_mem
      (linearAutGroup_le_semilinearAutGroup (innAut_le_linear hy))
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hxE
  obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.1 hyE
  have hσ := sigma_pow_eq_one_of_pow_mem_inn hx
  have hτ := sigma_pow_eq_one_of_pow_mem_inn hy
  rw [conjAut_mul_fieldAut_mul]
  set N : ℕ := 3 ^ (a + b) with hN
  have hστ : (σ * τ) ^ N = 1 := by
    rw [Commute.mul_pow (ringAut_commute σ τ)]
    have h1 : σ ^ N = 1 := by
      rw [hN, pow_add, pow_mul, hσ, one_pow]
    have h2 : τ ^ N = 1 := by
      rw [hN, pow_add, mul_comm, pow_mul, hτ, one_pow]
    rw [h1, h2, one_mul]
  have hpow : (conjAut 3 F (A * GeneralLinearGroup.map (σ : F →+* F) B) * fieldAut 3 F (σ * τ)) ^ N =
      conjAut 3 F (AiG (σ * τ) (A * GeneralLinearGroup.map (σ : F →+* F) B) N) := by
    rw [conj_fieldAut_pow, ← map_pow, hστ, map_one, mul_one]
  have hexp : 3 ^ (a + b + 1) = N * 3 := by rw [hN, pow_succ]
  rw [hexp, pow_mul, hpow]
  exact conjAut_pow_three_mem_inn _

instance innAut_normal : (innAut F).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ g
    refine ⟨g x, ?_⟩
    ext y
    simp [MulAut.conj_apply]

theorem exists_sylow_mul_of_closed {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (hmul : ∀ (x y : G) (a b : ℕ), x ^ 3 ^ a ∈ N → y ^ 3 ^ b ∈ N → (x * y) ^ 3 ^ (a + b + 1) ∈ N)
    {Y : Type} [Group Y] [Finite Y] (Rb : Sylow 3 Y)
    (ρ : Y →* G) {z : Y} (hz : ∃ a, ρ z ^ 3 ^ a ∈ N) :
    ∃ r ∈ (Rb : Subgroup Y), ρ (r⁻¹ * z) ∈ N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : Y →* G ⧸ N := (QuotientGroup.mk' N).comp ρ
  let π' : Y →* π.range := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  let Rb' : Sylow 3 π.range := Sylow.mapSurjective hπ' Rb
  have hπy : ∀ y : Y, ∀ a : ℕ, (π' y) ^ 3 ^ a = 1 ↔ ρ y ^ 3 ^ a ∈ N := by
    intro y a
    rw [← QuotientGroup.eq_one_iff, ← Subtype.coe_inj]
    simp [π', π, ← map_pow]
  let T : Subgroup π.range :=
    { carrier := {h | ∃ a : ℕ, h ^ 3 ^ a = 1}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro h₁ h₂ ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨y₁, rfl⟩ := hπ' h₁
        obtain ⟨y₂, rfl⟩ := hπ' h₂
        refine ⟨a + b + 1, ?_⟩
        rw [← map_mul, hπy, map_mul]
        exact hmul _ _ a b ((hπy y₁ a).1 ha) ((hπy y₂ b).1 hb)
      inv_mem' := by
        rintro _ ⟨a, ha⟩
        exact ⟨a, by rw [inv_pow, ha, inv_one]⟩ }
  have hTnormal : T.Normal :=
    ⟨fun n ⟨a, hn⟩ g => ⟨a, by rw [conj_pow, hn]; simp⟩⟩
  have hTp : IsPGroup 3 T := fun t => by
    obtain ⟨a, ha⟩ := t.2
    exact ⟨a, Subtype.ext ha⟩
  have hle : T ≤ (Rb' : Subgroup π.range) := hTp.le_sylow_of_normal Rb'
  obtain ⟨a, ha⟩ := hz
  have hzT : π' z ∈ T := ⟨a, (hπy z a).2 ha⟩
  have hmem : π' z ∈ (Rb' : Subgroup π.range) := hle hzT
  have hmem' : π' z ∈ (Rb : Subgroup Y).map π' := by
    simpa [Rb', Sylow.coe_mapSurjective] using hmem
  obtain ⟨r, hr, hrz⟩ := hmem'
  refine ⟨r, hr, ?_⟩
  have h1 : π r = π z := congrArg Subtype.val hrz
  have h2 := QuotientGroup.eq.1 h1
  simpa [π, map_mul, map_inv] using h2

theorem exists_sylow_mul_inn {Y : Type} [Group Y] [Finite Y] (Rb : Sylow 3 Y)
    (ρ : Y →* MulAut (projectiveSL 3 F)) {z : Y} (hz : ∃ a, ρ z ^ 3 ^ a ∈ innAut F) :
    ∃ r ∈ (Rb : Subgroup Y), ρ (r⁻¹ * z) ∈ innAut F :=
  exists_sylow_mul_of_closed (innAut F) (fun _ _ _ _ hx hy => exists_mul_pow_mem_inn hx hy) Rb ρ hz

end CFSG.HardMathSupport.Foote.ModuleExclusions
