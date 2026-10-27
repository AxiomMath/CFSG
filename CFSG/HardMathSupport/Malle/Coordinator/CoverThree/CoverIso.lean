module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure
public import CFSG.LieType.SeitzGeneration.HyperCoverLinear
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration Matrix

theorem exists_mulEquiv_sl3_of_cover_compat {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {F : Type} [Field F] [Finite F] (hF9 : 9 ∣ Nat.card F - 1)
    (ρ : K →* ProjectiveSpecialLinearGroup (Fin 3) F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ ψ : SL(3, F) ≃* K, ∀ g, ρ (ψ g) =
      QuotientGroup.mk' (Subgroup.center SL(3, F)) g := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_nine (F := F) hF9
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating 2 F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_cube (Units.mk0 ζ hζ0)
      (by simpa using hζ.pow_ne_one_of_pos_of_lt (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : 3 < 9))
      (Or.inl rfl)
  obtain ⟨φ, hφs, hφρ⟩ := exists_sl_cover_hom (by norm_num) hsep ρ hρ hker.le
  have hcenter : Nat.card (Subgroup.center SL(3, F)) = 3 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num)]
    exact Nat.gcd_eq_left (dvd_trans (by norm_num : 3 ∣ 9) hF9)
  have hkerle : φ.ker ≤ Subgroup.center SL(3, F) := by
    intro g hg
    have h1 : ρ (φ g) = 1 := by rw [MonoidHom.mem_ker.mp hg, map_one]
    rw [hφρ] at h1
    exact (QuotientGroup.eq_one_iff g).mp h1
  have hbot : φ.ker = ⊥ := by
    by_contra hne
    have hdvd : Nat.card φ.ker ∣ 3 := hcenter ▸ Subgroup.card_dvd_of_le hkerle
    have hne1 : Nat.card φ.ker ≠ 1 := fun h =>
      hne ((Subgroup.card_eq_one).mp h)
    have h3 : Nat.card φ.ker = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
    have hker_eq : φ.ker = Subgroup.center SL(3, F) :=
      Subgroup.eq_of_le_of_card_ge hkerle (by rw [h3, hcenter])
    have hZ : Subgroup.center K = ⊥ := by
      rw [eq_bot_iff]
      intro z hzK
      obtain ⟨g, rfl⟩ := hφs z
      have h1 : ρ (φ g) = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hzK
      rw [hφρ] at h1
      have : g ∈ φ.ker := hker_eq ▸ (QuotientGroup.eq_one_iff g).mp h1
      rw [MonoidHom.mem_ker.mp this]
      exact Subgroup.one_mem _
    rw [hZ] at hz
    simp at hz
  exact ⟨MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hbot, hφs⟩, hφρ⟩


theorem exists_mulEquiv_sl3_of_cover {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {F : Type} [Field F] [Finite F] (hF9 : 9 ∣ Nat.card F - 1)
    (ρ : K →* ProjectiveSpecialLinearGroup (Fin 3) F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    Nonempty (SL(3, F) ≃* K) := by
  obtain ⟨ψ, -⟩ := exists_mulEquiv_sl3_of_cover_compat hF9 ρ hρ hker hz
  exact ⟨ψ⟩

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
