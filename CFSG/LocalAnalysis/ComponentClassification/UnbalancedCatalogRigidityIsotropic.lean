module

public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag

variable {p e : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem semilinear_eq_smul_of_isotropic (h : UnitaryFieldData p e K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hdim : 3 ≤ Module.finrank K V) {φ : K ≃+* K} (T : V →ₛₗ[(φ : K →+* K)] V)
    (hTinj : Function.Injective T)
    (hline : ∀ v, B v v = 0 → ∃ μ : K, T v = μ • v)
    (hperp : ∀ v, B v v = 0 → ∀ x, B v x = 0 → B v (T x) = 0) :
    φ = 1 ∧ ∃ μ : K, ∀ x, T x = μ • x := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨-, hiso, -, -⟩ := hermitian_witt_basis h hB hBl rfl
  obtain ⟨e₀, he₀0, he₀⟩ := hiso (by omega)
  obtain ⟨⟨f₀, hef, hf₀⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl he₀0 he₀
  obtain ⟨-, -, -, -, hWdim⟩ := hsplit f₀ hef hf₀
  have hfe : B f₀ e₀ = 1 := by rw [hsymm, hef, map_one]
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w ∈ (Submodule.span K {e₀, f₀}).orthogonalBilin B, w ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    rw [hbot, finrank_bot] at hWdim
    omega
  have hw₀e : B e₀ w₀ = 0 :=
    (Submodule.mem_orthogonalBilin.mp hw₀W) e₀ (Submodule.subset_span (by simp))
  have hw₀f : B f₀ w₀ = 0 :=
    (Submodule.mem_orthogonalBilin.mp hw₀W) f₀ (Submodule.subset_span (by simp))
  obtain ⟨a₀, ha₀⟩ := hline e₀ he₀
  obtain ⟨b₀, hb₀⟩ := hline f₀ hf₀
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← map_zero T] at ha₀
    exact he₀0 (hTinj ha₀)
  have key : ∀ w c, B e₀ w = 0 → B f₀ w = 0 → c + h.bar c = -B w w →
      T w = a₀ • w ∧ φ c * b₀ = a₀ * c := by
    intro w c hwe hwf hc
    have hwe' : B w e₀ = 0 := by rw [hsymm, hwe, map_zero]
    have hwf' : B w f₀ = 0 := by rw [hsymm, hwf, map_zero]
    have hvv : B (e₀ + w + c • f₀) (e₀ + w + c • f₀) = 0 := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        he₀, hwe, hef, hwe', hwf', hfe, hwf, hf₀]
      linear_combination hc
    obtain ⟨μ, hμ⟩ := hline _ hvv
    have hTv : T (e₀ + w + c • f₀) = a₀ • e₀ + T w + (φ c * b₀) • f₀ := by
      rw [map_add, map_add, map_smulₛₗ, ha₀, hb₀, smul_smul]
      rfl
    have hTwe := hperp e₀ he₀ w hwe
    have hTwf := hperp f₀ hf₀ w hwf
    have h1 := congrArg (B f₀) hμ
    rw [hTv] at h1
    simp only [map_add, map_smul, smul_eq_mul, hfe, hTwf, hf₀, hwf] at h1
    have hμa : μ = a₀ := by linear_combination -h1
    have h2 := congrArg (B e₀) hμ
    rw [hTv] at h2
    simp only [map_add, map_smul, smul_eq_mul, he₀, hTwe, hef, hwe] at h2
    have hcb : φ c * b₀ = a₀ * c := by
      rw [← hμa]
      linear_combination h2
    refine ⟨?_, hcb⟩
    have hTw : T w = μ • (e₀ + w + c • f₀) - a₀ • e₀ - (φ c * b₀) • f₀ := by
      rw [← hμ, hTv]
      abel
    rw [hTw, hμa, hcb]
    module
  have htrace : ∀ w, ∃ c, c + h.bar c = -B w w := by
    intro w
    have hF : h.bar (B w w) = B w w := (hsymm w w).symm
    obtain ⟨c, hc⟩ := h.traceLin_surjective (-⟨B w w, hF⟩)
    exact ⟨c, by simpa [UnitaryFieldData.trace] using congrArg Subtype.val hc⟩
  have hTW : ∀ w, B e₀ w = 0 → B f₀ w = 0 → T w = a₀ • w := by
    intro w hwe hwf
    obtain ⟨c, hc⟩ := htrace w
    exact (key w c hwe hwf hc).1
  have hφ : ∀ x, φ x = x := by
    intro x
    have h1 := hTW (x • w₀) (by rw [map_smul, hw₀e, smul_zero])
      (by rw [map_smul, hw₀f, smul_zero])
    rw [map_smulₛₗ, hTW w₀ hw₀e hw₀f, smul_smul, smul_smul] at h1
    have h2 : ((φ : K →+* K) x * a₀) = a₀ * x := smul_left_injective K hw₀ h1
    have h3 : (φ x - x) * a₀ = 0 := by
      rw [RingEquiv.coe_toRingHom] at h2
      linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha₀0)
  have hφ1 : φ = 1 := RingEquiv.ext hφ
  obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  have hτ' : τ + h.bar τ = -B 0 0 := by
    simp only [map_zero, neg_zero]
    exact (h.mem_traceZero).mp hτ
  obtain ⟨-, hτb⟩ := key 0 τ (map_zero _) (map_zero _) hτ'
  rw [hφ] at hτb
  have hba : b₀ = a₀ := mul_left_cancel₀ hτ0 (by rw [hτb, mul_comm])
  refine ⟨hφ1, a₀, fun x => ?_⟩
  have hwe : B e₀ (x - B f₀ x • e₀ - B e₀ x • f₀) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, he₀, hef]
    ring
  have hwf : B f₀ (x - B f₀ x • e₀ - B e₀ x • f₀) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hfe, hf₀]
    ring
  have hx : x = (x - B f₀ x • e₀ - B e₀ x • f₀) + B f₀ x • e₀ + B e₀ x • f₀ := by abel
  have hTx := congrArg T hx
  rw [map_add, map_add, map_smulₛₗ, map_smulₛₗ, hTW _ hwe hwf, ha₀, hb₀, hba,
    RingEquiv.coe_toRingHom, hφ, hφ] at hTx
  rw [hTx]
  module

end CFSG.ComponentClassification.UnbalancedCatalog
