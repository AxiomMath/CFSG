module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type w} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

theorem perp_sub_mem_of_sub_mem (hρ : IsIsometric F ρ) {W W' : Submodule K V} {g : H}
    (hg : ∀ v ∈ W', ρ g⁻¹ v - v ∈ W) {v : V} (hv : v ∈ F.perp W) :
    ρ g v - v ∈ F.perp W' := by
  intro w hw
  have h1 := hρ g (ρ g⁻¹ w) v
  rw [rep_apply_inv_apply] at h1
  rw [F.β_sub_right, h1, ← F.β_sub_left]
  exact hv _ (hg w hw)

theorem le_flagKernel_isoFlag_of_triv [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) {X : Subgroup H} (hXN : X ≤ Subgroup.normalizer (R : Set H))
    (htriv : ∀ x ∈ X, ∀ k, ∀ v ∈ isoSeq F ρ R (k + 1), ρ x v - v ∈ isoSeq F ρ R k)
    (hmid : ∀ x ∈ X, ∀ v ∈ F.perp (isoSeq F ρ R (Module.finrank K V)),
      ρ x v - v ∈ isoSeq F ρ R (Module.finrank K V)) :
    X ≤ flagKernel ρ (isoFlag F ρ R) := by
  intro g hg
  refine ⟨normalizer_le_flagStab_isoFlag F ρ hρ R (hXN hg), fun k v hv => ?_⟩
  rcases Nat.lt_or_ge k (Module.finrank K V) with hk | hk
  · rw [isoFlag, ite_eq_left (by omega)] at hv
    rw [isoFlag, ite_eq_left hk.le]
    exact htriv g hg k v hv
  rcases hk.lt_or_eq with hk | rfl
  · rw [isoFlag, ite_eq_right (by omega)] at hv ⊢
    by_cases hk2 : k + 1 ≤ 2 * Module.finrank K V + 1
    · rw [ite_eq_left hk2] at hv
      rw [ite_eq_left (by omega), show 2 * Module.finrank K V + 1 - k =
        2 * Module.finrank K V + 1 - (k + 1) + 1 by omega]
      exact perp_sub_mem_of_sub_mem F ρ hρ (fun u hu => htriv _ (inv_mem hg) _ u hu) hv
    · by_cases hk3 : k ≤ 2 * Module.finrank K V + 1
      · rw [ite_eq_left hk3, show 2 * Module.finrank K V + 1 - k = 0 by omega, isoSeq_zero,
          F.perp_bot]
        trivial
      · rw [ite_eq_right hk3]
        trivial
  · rw [isoFlag, ite_eq_right (by omega), ite_eq_left (by omega),
      show 2 * Module.finrank K V + 1 - (Module.finrank K V + 1) = Module.finrank K V by omega]
      at hv
    rw [isoFlag, ite_eq_left le_rfl]
    exact hmid g hg v hv

theorem eq_bot_of_le_normalizer_of_triv [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) (R : Subgroup H) {X : Subgroup H}
    [Finite X] (hXp : Group.IsPerfect X) (hXN : X ≤ Subgroup.normalizer (R : Set H))
    (htriv : ∀ x ∈ X, ∀ k, ∀ v ∈ isoSeq F ρ R (k + 1), ρ x v - v ∈ isoSeq F ρ R k)
    (hmid : ∀ x ∈ X, ∀ v ∈ F.perp (isoSeq F ρ R (Module.finrank K V)),
      ρ x v - v ∈ isoSeq F ρ R (Module.finrank K V)) :
    X = ⊥ := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hle := le_flagKernel_isoFlag_of_triv F ρ hρ R hXN htriv hmid
  have hp : IsPGroup p (flagKernel ρ (isoFlag F ρ R)) :=
    isPGroup_flagKernel ρ p hinj (isoFlag_zero F ρ R) (isoFlag_top F ρ R)
  have hXp' : IsPGroup p X := hp.to_le hle
  by_contra hne
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  exact Group.IsPerfect.not_isNilpotent (G := X) hXp'.isNilpotent

theorem finrank_perp_add_finrank [FiniteDimensional K V] (W : Submodule K V) :
    Module.finrank K (F.perp W) + Module.finrank K W = Module.finrank K V := by
  have h := F.finrank_perp W
  have h2 := Submodule.finrank_le W
  omega

theorem two_mul_finrank_le_of_isTotallyIsotropic [FiniteDimensional K V] {W : Submodule K V}
    (hW : F.IsTotallyIsotropic W) : 2 * Module.finrank K W ≤ Module.finrank K V := by
  have h1 := finrank_perp_add_finrank F W
  have h2 := Submodule.finrank_mono hW
  omega

end CFSG.SeitzReduction.SymplecticPilot
