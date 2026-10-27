module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

theorem odd_eq_bot_of_hom_two_kernel {G Q : Type*} [Group G] [Finite G] [Group Q] {t x : G}
    (hxt : x ∈ Subgroup.centralizer ({t} : Set G)) (F : ↥(Subgroup.centralizer ({t} : Set G)) →* Q)
    (hker : IsPGroup 2 F.ker) {p : ℕ}
    (hQ : ∀ M : Subgroup Q, M ≤ Subgroup.centralizer ({F ⟨x, hxt⟩} : Set Q) →
      Odd (Nat.card M) → ¬ p ∣ Nat.card M → M = ⊥)
    {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
    (hodd : Odd (Nat.card K)) (hKp : ¬ p ∣ Nat.card K) : K = ⊥ := by
  have hKT : K ≤ Subgroup.centralizer ({t} : Set G) := fun k hk => (hK hk).2
  set K₀ : Subgroup ↥(Subgroup.centralizer ({t} : Set G)) :=
    K.subgroupOf (Subgroup.centralizer ({t} : Set G))
  have hcard : Nat.card K₀ = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  have hdvd : Nat.card (K₀.map F) ∣ Nat.card K :=
    hcard ▸ Subgroup.card_map_dvd K₀ F
  have hM : K₀.map F = ⊥ := by
    refine hQ _ ?_ (hodd.of_dvd_nat hdvd) fun hp => hKp (hp.trans hdvd)
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hkx : (k : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (hK (Subgroup.mem_subgroupOf.mp hk)).1
    exact Subgroup.mem_centralizer_singleton_iff.mp hkx
  have hK₂ : IsPGroup 2 K₀ := hker.to_le ((Subgroup.map_eq_bot_iff K₀).mp hM)
  rcases hK₂.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.mp (hcard ▸ h1)
  · obtain ⟨m, hm⟩ := hodd
    obtain ⟨k, hk⟩ := h2
    omega

theorem card_gLAPPrimeCoreOf_centralizer_conj {G : Type*} [Group G] (p : ℕ) (c x : G) :
    Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({c * x * c⁻¹} : Set G))) =
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) := by
  have hψ : Function.Injective (MulAut.conj c : G ≃* G).toMonoidHom :=
    (MulAut.conj c : G ≃* G).injective
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
    (MulAut.conj c : G ≃* G).toMonoidHom hψ (Subgroup.centralizer ({x} : Set G))
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    (MulAut.conj c : G ≃* G).toMonoidHom hψ ⊤ x
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj c : G ≃* G).surjective,
    top_inf_eq] at hc
  have hs : (MulAut.conj c : G ≃* G).toMonoidHom x = c * x * c⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hc
  rw [hc] at hmap
  rw [← hmap]
  exact Subgroup.card_map_of_injective hψ

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
