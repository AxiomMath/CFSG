module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GA2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma ga4_mem_conjugate_iff {Y : Type*} [Group Y] {A : Subgroup Y} {g x : Y} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem closed_of_setup [Finite H] (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j)
    (hcent : ∀ s ∈ normalizer (Sec5B517Q8 hS.quad : Set H), s * s ∈ Sec5B517Q8 hS.quad →
      (∀ q ∈ Sec5B517Q8 hS.quad, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hS.quad)
    (hpar : ∀ w ∈ normalizer (Sec5B517Q8 hS.quad : Set H),
      (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hS.quad, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    (h518 : ∀ (U : Subgroup H) (n : ℕ), U ≤ normalizer (Sec5B517Q8 hS.quad : Set H) →
      (∀ a ∈ U, ∀ b ∈ U,
        (∀ q ∈ Sec5B517Q8 hS.quad,
          a * b * a⁻¹ * b⁻¹ * q * (a * b * a⁻¹ * b⁻¹)⁻¹ * q⁻¹ ∈ zpowers z) ∧
        (∀ q ∈ Sec5B517Q8 hS.quad, a * a * q * (a * a)⁻¹ * q⁻¹ ∈ zpowers z)) →
      ((centralizer (planeV hS.quad α : Set X)).comap α).relIndex U = 2 ^ n → n ≤ 3)
    (hCd : ∀ d : H, d ∈ Sec5B517Q8 hS.quad → d * d = 1 → d ≠ 1 → d ≠ z →
      (∃ i j : Fin 4, i ≠ j ∧ d ∈ K i ⊔ K j) →
        centralizer ({d} : Set H) ≤ normalizer (Sec5B517Q8 hS.quad : Set H)) :
    ∀ q ∈ Sec5B517Q8 hS.quad, ∀ x : H, x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) →
      x⁻¹ * q * x ∈ Sec5B517Q8 hS.quad := by
  classical
  haveI : Finite X := Finite.of_surjective α hS.surj
  have hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α) := planeSys_of_setup hS hperm
  have hparX : PlaneParity (planeV hS.quad α) (planeW hS.quad α) :=
    planeParity_of_setup hS hperm hpar
  have hCX : ∀ y ∈ normalizer (planeV hS.quad α : Set X), y * y = 1 →
      y ∈ centralizer (planeV hS.quad α : Set X) → y ∈ planeV hS.quad α :=
    fun y hy hy2 hyc => mem_planeV_of_inv_centralizes hS hcent hy hy2 hyc
  have h518X := h518X_of_setup hS h518
  have h73X := h73X_of_setup hS hSys hCd
  intro q hq x hx
  have hu : α (x⁻¹ * q * x) ∈ normalizer (planeV hS.quad α : Set X) :=
    (mem_normalizer_planeV_iff hS).mpr hx
  have hconj : ∃ k : X, α (x⁻¹ * q * x) ∈ CFSG.conjugate (planeV hS.quad α) k := by
    refine ⟨α x, ?_⟩
    rw [ga4_mem_conjugate_iff]
    have e : α x * α (x⁻¹ * q * x) * (α x)⁻¹ = α q := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      group
    rw [e]
    exact Subgroup.mem_map_of_mem α hq
  exact (mem_planeV_iff hS).mp
    (strongly_closed_in_normalizer hSys hparX hCX h518X h73X _ hu hconj)

end CFSG.OddStandard.SmallF3.Omega
