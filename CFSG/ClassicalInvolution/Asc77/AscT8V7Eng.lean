module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerRes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {R T W : Subgroup G} {z t : G}

theorem y_dataE (hcl : ConjInvariant Ω) (hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hK : K ∈ Ω) (hJΩ : J ∈ Ω) (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hnoT : ∀ K' ∈ twinSet Ω K, K' = K) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    (hzW : z ∈ W) (htW : t ∈ W) (hRsyl : IsSylow2In R K) (hTsyl : IsSylow2In T J)
    (hcomm : ∀ {M R₀ : Subgroup G} {y : G} {m : ℕ}, M ∈ Ω → IsSylow2In R₀ M →
      y ∈ Subgroup.normalizer (M : Set G) → y ^ 2 ^ m = 1 → (∀ r ∈ R₀, y * r = r * y) →
        ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M)
    {y : G} (hyW : y ∈ W) (hy4 : y ^ 2 ^ 2 = 1)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) :
    y ∈ T8.cenZ (z * t) ∧ y ∈ Subgroup.normalizer (K : Set G) ∧
      y ∈ Subgroup.normalizer (J : Set G) ∧ (∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K) ∧
      (∀ k ∈ J, ⁅y, k⁆ ∈ oddCoreOf J) := by
  have hyz : y * z = z * y := hcommW y hyW z hzW
  have hyt : y * t = t * y := hcommW y hyW t htW
  have hyN1 : y ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hcl hK hnoT hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have hyN2 : y ∈ Subgroup.normalizer (J : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hcl hJΩ (hnt _ hJΩ) ht
      (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
  refine ⟨?_, hyN1, hyN2, ?_, ?_⟩
  · rw [T8.mem_cenZ_iff]
    calc y * (z * t) = (y * z) * t := by group
      _ = (z * y) * t := by rw [hyz]
      _ = z * (y * t) := by group
      _ = z * (t * y) := by rw [hyt]
      _ = (z * t) * y := by group
  · exact hcomm hK hRsyl hyN1 hy4 (fun r hr => (hyR r hr).symm)
  · exact hcomm hJΩ hTsyl hyN2 hy4 (fun r hr => (hyT r hr).symm)

end T8V

end CFSG.ClassicalInvolution.Asc77
