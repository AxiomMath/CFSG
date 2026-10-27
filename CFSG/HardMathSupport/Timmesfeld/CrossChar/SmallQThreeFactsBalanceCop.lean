module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsBalance

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance

section Balance

variable {K : Type*} [Group K] [Finite K]

theorem gLAPPrimeCoreOf_inf_centralizer_conj_eq_bot_of_coprime
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {t : K}
    (hin : GLAPPrimeCoreOf 3 (Subgroup.centralizer {t}) = ⊥)
    (hrig : ∀ α : MulAut K, Nat.Coprime 3 (orderOf α) →
      (∀ y ∈ Subgroup.centralizer {t}, α y = y) → α ∈ innerAut K)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer {MulAut.conj t}) = ⊥ := by
  have : Finite (MulAut K) :=
    Finite.of_injective (fun φ : MulAut K => (φ : K → K)) DFunLike.coe_injective
  set C := H ⊓ Subgroup.centralizer {MulAut.conj t} with hC
  set O := GLAPPrimeCoreOf 3 C with hO
  set CI := innerAut K ⊓ Subgroup.centralizer {MulAut.conj t} with hCI
  have hCI0 : GLAPPrimeCoreOf 3 CI = ⊥ := by
    rw [hCI, inner_inf_centralizer_conj hinj, gLAPPrimeCoreOf_map_of_injective 3 _ hinj, hin,
      Subgroup.map_bot]
  have hCIC : CI ≤ C := inf_le_inf_right _ hH
  have hOI : ∀ φ ∈ O, φ ∈ innerAut K → φ = 1 := by
    intro φ hφ hφI
    have hle : O ⊓ innerAut K ≤ GLAPPrimeCoreOf 3 CI := by
      refine le_gLAPPrimeCoreOf_of_normal' ?_ ?_ ?_
      · intro x hx
        exact ⟨hx.2, (Subgroup.mem_inf.1 (gLAPPrimeCoreOf_le_self' C hx.1)).2⟩
      · intro g hg x hx
        refine ⟨gLAPPrimeCoreOf_conj_mem' g (hCIC hg) x hx.1, ?_⟩
        exact (innerAut K).mul_mem ((innerAut K).mul_mem (Subgroup.mem_inf.1 hg).1 hx.2)
          ((innerAut K).inv_mem (Subgroup.mem_inf.1 hg).1)
      · exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three C).coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left)
    have := hle ⟨hφ, hφI⟩
    rw [hCI0, Subgroup.mem_bot] at this
    exact this
  refine eq_bot_iff.2 fun α hα => ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ y ∈ Subgroup.centralizer {t}, α y = y := by
    intro y hy
    have hyCI : MulAut.conj y ∈ CI := by
      rw [hCI, inner_inf_centralizer_conj hinj]
      exact ⟨y, hy, rfl⟩
    have h1 : α * MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ O := by
      have h2 : MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ O :=
        gLAPPrimeCoreOf_conj_mem' _ (hCIC hyCI) _ (O.inv_mem hα)
      have := O.mul_mem hα h2
      simpa [mul_assoc] using this
    have h3 : α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
      ext z
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    have h4 : α * MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ innerAut K := by
      rw [h3]
      exact (innerAut K).mul_mem ⟨α y, rfl⟩ ((innerAut K).inv_mem ⟨y, rfl⟩)
    have h5 := hOI _ h1 h4
    rw [mul_inv_eq_one, h3] at h5
    exact hinj h5
  have hcop : Nat.Coprime 3 (orderOf α) := by
    have h1 : orderOf (⟨α, hα⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three C).coprime_dvd_right h1
  exact hOI α hα (hrig α hcop hfix)

theorem innerOneBalanceThree_of_toral_coprime
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (T : Set K)
    (hfus : ∀ s : K, s ^ 3 = 1 → s ≠ 1 → ∃ c, c * s * c⁻¹ ∈ T)
    (hin : ∀ t ∈ T, GLAPPrimeCoreOf 3 (Subgroup.centralizer {t}) = ⊥)
    (hrig : ∀ t ∈ T, ∀ α : MulAut K, Nat.Coprime 3 (orderOf α) →
      (∀ y ∈ Subgroup.centralizer {t}, α y = y) → α ∈ innerAut K) :
    InnerOneBalanceThree K := by
  intro d hd hd3 hd1 H hH
  obtain ⟨s, rfl⟩ := hd
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hd3, map_one])
  have hs1 : s ≠ 1 := fun h => hd1 (by rw [h, map_one])
  obtain ⟨c, hc⟩ := hfus s hs3 hs1
  rw [← gLAPPrimeCoreOf_inf_centralizer_conj_iff hH c s]
  exact gLAPPrimeCoreOf_inf_centralizer_conj_eq_bot_of_coprime hinj (hin _ hc) (hrig _ hc) hH

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
