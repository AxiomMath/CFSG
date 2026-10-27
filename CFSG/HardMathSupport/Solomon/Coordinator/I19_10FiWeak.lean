module

public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem localDeltaIn_commutator_eq_bot {M : Type*} [Group M] (p : ℕ) (H D : Subgroup M) :
    ⁅localDeltaIn p H D, D⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx d hd
  by_cases hd1 : d = 1
  · rw [hd1, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · have hx' : x ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M)) := by
      unfold localDeltaIn at hx
      simp only [Subgroup.mem_iInf] at hx
      exact hx d hd hd1
    have hxc : x ∈ Subgroup.centralizer ({d} : Set M) := (Subgroup.map_subtype_le _ hx').2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    rw [commutatorElement_eq_one_iff_mul_comm.2 hxc]
    exact Subgroup.one_mem _

theorem fi22_weaklyLocallyBalanced_of_isPGroup
    {S : Type} [Group S] [Finite S] (hS : IsFiTwentyTwo S)
    {A : Subgroup (MulAut S)} (hA : IsPGroup 5 A) : IsWeaklyLocallyBalanced 5 2 A := by
  intro D hD H _ _
  obtain ⟨hcen, hfac, -, hinn⟩ := Proving.fi22Facts_holds S hS
  have hAinn : A ≤ innerAut S := by
    intro φ hφ
    obtain ⟨k, rfl⟩ := hinn φ (hA.to_le (Subgroup.zpowers_le.2 hφ))
    exact ⟨k, rfl⟩
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut S => φ g) hab
      simp only [MulAut.conj_apply] at h
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = a⁻¹ * b * g := by group
    rw [hcen, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.1 hc
  have hcardInn : Nat.card (innerAut S) = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have : Finite (MulAut S) :=
    Finite.of_injective (fun φ : MulAut S => (φ : S → S)) fun a b h => MulEquiv.ext (congrFun h)
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : 5 ^ n ∣ Nat.card S := by
    rw [← hn, ← hcardInn]
    exact Subgroup.card_dvd_of_le hAinn
  have hn2 : n ≤ 2 := by
    rw [← hfac]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 hdvd
  have hDA : D = A := Subgroup.eq_of_le_of_card_ge hD.1 (by
    rw [hn, hD.2.2]
    exact Nat.pow_le_pow_right (by norm_num) hn2)
  rw [← hDA]
  exact localDeltaIn_commutator_eq_bot 5 H D

theorem weakFi22FiveElem_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsFiTwentyTwo S → ∀ A : Subgroup (MulAut S), IsElemAbelian 5 A →
        IsWeaklyLocallyBalanced 5 2 A := by
  intro S _ _ _ _ hS A hA
  refine fi22_weaklyLocallyBalanced_of_isPGroup hS fun g => ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact hA.2 g g.2

end CFSG.HardMathSupport.Solomon.Coordinator
