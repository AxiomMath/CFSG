module

public import CFSG.LargeExtraspecial.Asc611Out
public import CFSG.LargeExtraspecial.Asc611Uni
public import CFSG.LargeExtraspecial.AS35KFix

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem semi_smul_conj {A : GL (Fin m) K} {φ : K ≃+* K} {g g' : SUid frob m}
    (h : (g' : GL (Fin m) K) = A * glAut φ (g : GL (Fin m) K) * A⁻¹) (x : Fin m → K) :
    AS35K.semi A φ (g • x) = g' • AS35K.semi A φ x := by
  have h1 : A * glAut φ (g : GL (Fin m) K) = g' * A := by
    rw [h]
    group
  have h2 := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ x)) h1
  simp only [Units.val_mul, ← mulVec_mulVec, AS35K.glAut_mulVec] at h2
  rw [AS35K.semi, AS35K.semi, CFSG.ClassicalGroups.Unitary.smul_def,
    CFSG.ClassicalGroups.Unitary.smul_def]
  exact h2

theorem realize_tq {β : MulAut (PG m)}
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') {v : Fin m → K}
    (hv : herm frob v v = 0) : β (tq v) = tq (AS35K.semi A φ v) := by
  obtain ⟨g', hg', hβg⟩ := hβ (tvU v)
  have hφv : herm frob (φ ∘ v) (φ ∘ v) = 0 := by rw [AS35K.herm_comp, hv, map_zero]
  have hg'w : g' = tvU (AS35K.semi A φ v) := Subtype.ext (by
    rw [hg', AS35K.glAut_tvU φ hv, AS35K.conj_tvU_of_unitary A.2 hφv]
    rfl)
  change β (QuotientGroup.mk (tvU v)) = _
  rw [hβg, hg'w]

theorem eq_frob_of_fieldFactor_ne_one (hm : 4 ≤ m) {β : MulAut (PG m)}
    (hβ1 : fieldFactor hm β ≠ 1)
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') (c : K) : φ c = frob c := by
  have hφ : φ ≠ 1 := by
    rw [← fieldFactor_of_realize hm hβ]
    exact hβ1
  rcases AS35N.ringEquiv_cases φ with h | h
  · exact absurd (RingEquiv.ext h) hφ
  · rcases AS35N.K_cases' c with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [map_add, map_add, map_one, map_one, h]

theorem semi_semi {A : GL (Fin m) K} {φ : K ≃+* K} (hφφ : ∀ c, φ (φ c) = c)
    (x : Fin m → K) :
    AS35K.semi A φ (AS35K.semi A φ x) =
      ((A * glAut φ A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x := by
  have h1 : φ ∘ (φ ∘ x) = x := funext fun i => hφφ (x i)
  rw [AS35K.semi, AS35K.semi, ← AS35K.glAut_mulVec, h1, Units.val_mul, ← mulVec_mulVec]

theorem semi_semi_eq (hm : 4 ≤ m) {β : MulAut (PG m)} (hββ : β * β = 1)
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') (hφ : ∀ c, φ c = frob c)
    (x : Fin m → K) : AS35K.semi A φ (AS35K.semi A φ x) = x := by
  have hφφ : ∀ c, φ (φ c) = c := fun c => by rw [hφ, hφ, frob_frob]
  set M := (((A : GL (Fin m) K) * glAut φ (A : GL (Fin m) K) : GL (Fin m) K) :
    Matrix (Fin m) (Fin m) K) with hM
  have hSS : ∀ y, AS35K.semi A φ (AS35K.semi A φ y) = M *ᵥ y := fun y => semi_semi hφφ y
  have heig : ∀ v : Fin m → K, v ≠ 0 → herm frob v v = 0 → ∃ c : K, M *ᵥ v = c • v := by
    intro v hv0 hv
    have hSv : herm frob (AS35K.semi A φ v) (AS35K.semi A φ v) = 0 := by
      rw [AS35K.herm_semi A.2, hv, map_zero]
    have h1 : β (β (tq v)) = tq v := by
      rw [← MulAut.mul_apply, hββ, MulAut.one_apply]
    rw [realize_tq hβ hv, realize_tq hβ hSv, hSS] at h1
    have hMv : herm frob (M *ᵥ v) (M *ᵥ v) = 0 := by
      rw [← hSS, AS35K.herm_semi A.2, hSv, map_zero]
    have hMv0 : M *ᵥ v ≠ 0 := by
      rw [← hSS]
      exact AS35K.semi_ne_zero _ _ (AS35K.semi_ne_zero _ _ hv0)
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff (by omega) hv0 hv hMv0 hMv).mp h1.symm
    exact ⟨c, hc.symm ▸ rfl⟩
  obtain ⟨μ, hμ⟩ := exists_scalar_of_forall_eigen M heig
  have hS3 : ∀ y, AS35K.semi (A : GL (Fin m) K) φ (μ • y) =
      μ • AS35K.semi (A : GL (Fin m) K) φ y := by
    intro y
    have h1 := hSS (AS35K.semi A φ y)
    rw [hμ] at h1
    have h2 : AS35K.semi (A : GL (Fin m) K) φ (AS35K.semi (A : GL (Fin m) K) φ y) = μ • y :=
      (hSS y).trans (hμ y)
    rw [← h1, h2]
  set e₀ : Fin m → K := Pi.single ⟨0, by omega⟩ 1 with he₀
  have he₀0 : e₀ ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, by omega⟩
    simp [he₀] at this
  have hSe : AS35K.semi A φ e₀ ≠ 0 := AS35K.semi_ne_zero _ _ he₀0
  have hμμ : frob μ = μ := by
    have h1 := hS3 e₀
    rw [AS35K.semi_smul, hφ] at h1
    have h2 : (frob μ - μ) • AS35K.semi A φ e₀ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hSe)
  have hμ1 : μ = 1 := by
    rcases (frob_eq_self_iff μ).mp hμμ with h | h
    · exfalso
      have h1 := hSS e₀
      rw [hμ, h, zero_smul] at h1
      exact AS35K.semi_ne_zero _ _ hSe h1
    · exact h
  rw [hSS, hμ, hμ1, one_smul]

theorem smul_smul_comm (g : SUid frob m) (c : K) (x : Fin m → K) : g • (c • x) = c • (g • x) := by
  rw [CFSG.ClassicalGroups.Unitary.smul_def, CFSG.ClassicalGroups.Unitary.smul_def, mulVec_smul]

theorem exists_lift_comm (hm : 4 ≤ m) {β : MulAut (PG m)}
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') (hφ : ∀ c, φ c = frob c)
    {u : PG m} (hu : β u = u) :
    ∃ û : SUid frob m, (QuotientGroup.mk û : PG m) = u ∧
      ∀ x, AS35K.semi (A : GL (Fin m) K) φ (û • x) = û • AS35K.semi (A : GL (Fin m) K) φ x := by
  obtain ⟨û₀, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨g', hg', hβg⟩ := hβ û₀
  rw [hβg, QuotientGroup.eq] at hu
  set ζ := g'⁻¹ * û₀ with hζ
  have hcen : ζ ∈ center (SUid frob m) := hu
  have hcen' := hcen
  rw [center_SUid (by omega)] at hcen'
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hcen'
  have hc0 : c ≠ 0 := by
    intro h0
    set e₀ : Fin m → K := Pi.single ⟨0, by omega⟩ 1 with he₀
    have h1 := hc e₀
    rw [h0, zero_smul] at h1
    have h2 : e₀ = 0 := by
      have := congrArg (fun y => ζ⁻¹ • y) h1
      simpa [smul_smul] using this
    have := congrFun h2 ⟨0, by omega⟩
    simp [he₀] at this
  have hg'x : ∀ x : Fin m → K, g' • x = û₀ • (c⁻¹ • x) := by
    intro x
    have h1 : g' = û₀ * ζ⁻¹ := by rw [hζ]; group
    have h2 : ζ⁻¹ • x = c⁻¹ • x := by
      have h3 := hc (c⁻¹ • x)
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul] at h3
      calc ζ⁻¹ • x = ζ⁻¹ • (ζ • (c⁻¹ • x)) := by rw [h3]
        _ = c⁻¹ • x := by rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [h1, mul_smul, h2]
  refine ⟨û₀ * ζ, ?_, fun x => ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ζ).mpr hcen, mul_one]
  · have hfc : frob c * c⁻¹ = c := by
      rw [frob_apply, sq, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    calc AS35K.semi (A : GL (Fin m) K) φ ((û₀ * ζ) • x)
        = AS35K.semi (A : GL (Fin m) K) φ (û₀ • (c • x)) := by rw [mul_smul, hc]
      _ = g' • (frob c • AS35K.semi (A : GL (Fin m) K) φ x) := by
          rw [semi_smul_conj hg', AS35K.semi_smul, hφ]
      _ = c • (û₀ • AS35K.semi (A : GL (Fin m) K) φ x) := by
          rw [smul_smul_comm, hg'x, smul_smul_comm, smul_smul, hfc]
      _ = (û₀ * ζ) • AS35K.semi (A : GL (Fin m) K) φ x := by
          rw [mul_smul, hc, smul_smul_comm]

end CFSG.LargeExtraspecial.Asc611
