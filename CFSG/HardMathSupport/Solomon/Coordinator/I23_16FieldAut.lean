module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.Quasithin.A318P CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.SBd19F

namespace FieldThree

theorem isInnDiagThree_or_isFieldAutThree_L {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]
    (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K) {α : MulAut Y} (h3 : α ^ 3 = 1) :
    Lemma54Ns.IsInnDiagThree α ∨ IsFieldAutThree α := by
  have hψ3 : MulAut.congr ε (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hD : MulAut.congr ε (centerDescend Y α) ∈ linearAutGroup 3 K
  · exact Or.inl (Or.inl (isInnDiagPSL3_of_model ε hD))
  · obtain ⟨σ, -, H, hH⟩ := linear_order_three_field_descent le_rfl _ hψ3 hD
    exact Or.inr (Or.inr (Or.inl (isFieldAutPSL3_of_model ε σ (conjAut 3 K H) hH)))

theorem isInnDiagThree_or_isFieldAutThree_U {Y : Type*} [Group Y] {p f : ℕ} {K : Type} [Field K]
    (hF : UnitaryFieldData p f K) (hq : 2 < p ^ f) (ε : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3)
    {α : MulAut Y} (h3 : α ^ 3 = 1) :
    Lemma54Ns.IsInnDiagThree α ∨ IsFieldAutThree α := by
  have hfin := hF.finite
  have hψ3 : MulAut.congr ε (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hD : MulAut.congr ε (centerDescend Y α) ∈ (psuConj hF).range
  · exact Or.inl (Or.inr (isInnDiagPSU3_of_model hF ε hD))
  · obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq _ hψ3 hD
    exact Or.inr (Or.inr (Or.inr (isFieldAutPSU3_of_model hF ε σ (by rw [hσ]; decide)
      (psuConj hF H) hH)))

theorem card_le_three_of_frame {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {M : Type} [Group M] [Finite M] {C : Type} [Group C] [Finite C] [IsCyclic C]
    (ε : (K ⧸ Subgroup.center K) ≃* M) (F : L3Frame M C)
    (hdiag : ∀ α : MulAut K, MulAut.congr ε (centerDescend K α) ∈ F.D →
      Lemma54Ns.IsInnDiagThree α)
    (E : Subgroup (MulAut K)) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hfield : ∀ α ∈ E, IsFieldAutThree α) : Nat.card E ≤ 3 := by
  set Φ : MulAut K →* MulAut M := (MulAut.congr ε).toMonoidHom.comp (centerDescend K) with hΦ
  have hinj : Function.Injective Φ := phi_injective hK ε
  have hmem : ∀ x : ↥E, Φ (x : MulAut K) ∈ F.E := by
    intro x
    have h3 : Φ (x : MulAut K) ^ 3 = 1 := by
      rw [← map_pow, hE.2 x x.2, map_one]
    have hd : orderOf (Φ (x : MulAut K)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · have : Φ (x : MulAut K) = 1 := orderOf_eq_one_iff.1 h1
      rw [this]; exact F.E.one_mem
    · exact F.mem_E.2 (F.three_mem _ 1 (by rw [h1]; norm_num))
  set ρ : ↥E →* C := F.rho.comp ((Φ.comp E.subtype).codRestrict F.E hmem) with hρ
  have hker : ∀ x : ↥E, ρ x = 1 → x = 1 := by
    intro x hx
    have hD : Φ (x : MulAut K) ∈ F.D :=
      (F.rho_eq_one_iff ⟨Φ (x : MulAut K), hmem x⟩).1 hx
    have h1 : (x : MulAut K) = 1 :=
      LocalBalance.AutL3.input7_fieldInnDiag_holds K hK _ (hfield x x.2) (hdiag _ hD)
    exact Subtype.ext h1
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    exact hker
  have hcube : ∀ c : ↥ρ.range, c ^ 3 = 1 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    show ρ x ^ 3 = 1
    rw [← map_pow]
    have : (x : ↥E) ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    rw [this, map_one]
  have hle := card_le_three_of_pow hcube
  have hcard : Nat.card ↥ρ.range = Nat.card E := Nat.card_congr (Equiv.ofInjective ρ hρinj).symm
  omega

theorem card_le_three_of_outThreeBound {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {S : Type} [Group S] [Finite S]
    (e : (K ⧸ Subgroup.center K) ≃* S) (hS : OutThreeBound S)
    (hfix : ∀ α : MulAut K, IsFieldAutThree α →
      IsInnerAut (MulAut.congr e (centerDescend K α)) → α = 1)
    (E : Subgroup (MulAut K)) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hfield : ∀ α ∈ E, IsFieldAutThree α) : Nat.card E ≤ 3 := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) fun f g h => MulEquiv.ext (congrFun h)
  set Φ : MulAut K →* MulAut S := (MulAut.congr e).toMonoidHom.comp (centerDescend K) with hΦ
  have hinj : Function.Injective Φ := phi_injective hK e
  have hcube : ∀ x ∈ E.map Φ, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE.2 y hy, map_one]
  obtain ⟨α, hαB, hα⟩ := hS (E.map Φ) hcube
  set C : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hC
  have h1 := card_le_three_mul_card_inf_of_pow_mul_mem (C := C) hαB
    (fun b hb => by
      obtain ⟨k, hk, h⟩ := hα b hb
      exact ⟨k, hk, h⟩)
  have hbot : (E.map Φ ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy, rfl⟩, hxC⟩
    rw [Subgroup.mem_bot]
    have : y = 1 := hfix y (hfield y hy) hxC
    rw [this, map_one]
  rw [hbot, Subgroup.card_bot, Subgroup.card_map_of_injective hinj] at h1
  omega

end FieldThree

end CFSG.HardMathSupport.Solomon.Coordinator
