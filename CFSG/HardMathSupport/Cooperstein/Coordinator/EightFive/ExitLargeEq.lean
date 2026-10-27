module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolLarge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section Perm

variable {m n : ℕ}

theorem conj_viaEmbedding_of_apply {ι : Fin m ↪ Fin n} {π : Perm (Fin n)} {τ : Perm (Fin m)}
    (hπ : ∀ i, π (ι i) = ι (τ i)) (σ : Perm (Fin m)) :
    π * viaEmbedding σ ι * π⁻¹ = viaEmbedding (τ * σ * τ⁻¹) ι := by
  have hinv : ∀ i, π⁻¹ (ι i) = ι (τ⁻¹ i) := fun i => by
    rw [Perm.inv_eq_iff_eq, hπ, perm_apply_inv_apply]
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    simp only [Perm.mul_apply, hinv, viaEmbedding_apply, hπ]
  · have hx' : π⁻¹ x ∉ Set.range ι := by
      rintro ⟨j, hj⟩
      apply hx
      refine ⟨τ j, ?_⟩
      rw [← hπ, hj, perm_apply_inv_apply]
    rw [Perm.mul_apply, Perm.mul_apply, viaEmbedding_apply_of_notMem _ _ _ hx',
      perm_apply_inv_apply, viaEmbedding_apply_of_notMem _ _ _ hx]

end Perm

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {m n : ℕ} {ψ : ↥H →* Perm (Fin n)}
  {ι : Fin m ↪ Fin n} {R' : Subgroup (Perm ↥(Set.range ι)ᶜ)}

section Conj

variable (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)

theorem conj_mem_alternatingGroup (τ : Perm (Fin m)) (σ : alternatingGroup (Fin m)) :
    τ * (σ : Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m) :=
  alternatingGroup.normal.conj_mem _ σ.2 τ

include hψ in
theorem conj_altRho_altLift_of_mem_largeK (k : ↥(largeK ψ ι R')) (σ : alternatingGroup (Fin m)) :
    (k : MulAut V) * altRho hψ hAlt (altLift ι σ) * (k : MulAut V)⁻¹ =
      altRho hψ hAlt (altLift ι ⟨_, conj_mem_alternatingGroup (largeKappa ψ ι R' k) σ⟩) := by
  set kH : ↥H := Subgroup.inclusion ((largeK_le ψ ι R').trans preSub_le) k with hkH
  set x : ↥H := ⟨_, altRho_mem hψ hAlt (altLift ι σ)⟩ with hx
  set y : ↥H := ⟨_, altRho_mem hψ hAlt (altLift ι ⟨_, conj_mem_alternatingGroup
    (largeKappa ψ ι R' k) σ⟩)⟩ with hy
  have h1 : ψ (kH * x * kH⁻¹) = ψ y := by
    rw [map_mul, map_mul, map_inv, hx, hy, apply_altRho, apply_altRho, coe_altLift, coe_altLift]
    exact conj_viaEmbedding_of_apply
      (fun i => (restrictHom_apply_apply (hK := largeK_le ψ ι R') k i).symm) _
  exact congrArg Subtype.val (hψ h1)

end Conj

theorem altRho_altLift_mem_centQuot (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hm : 5 ≤ m) {A : Subgroup (MulAut V)}
    (hAK : A ≤ largeK ψ ι R') (htop : fixV (largeQ ψ ι R') ⊔ fixV A = ⊤) {a : MulAut V}
    (ha : a ∈ A) (ha1 : largeKappa ψ ι R' ⟨a, hAK ha⟩ ≠ 1) (σ : alternatingGroup (Fin m)) :
    altRho hψ hAlt (altLift ι σ) ∈ centQuot (fixV (largeQ ψ ι R')) := by
  set W := fixV (largeQ ψ ι R') with hW
  have hKW := largeK_le_stabSub ψ ι R'
  have hAq : ∀ b ∈ A, b ∈ centQuot W := by
    intro b hb v
    have hv : v ∈ W ⊔ fixV A := htop ▸ Subgroup.mem_top v
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
    have hbc : b c = c := hc b hb
    rw [map_mul, hbc, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    exact W.mul_mem (((hKW (hAK hb)) w).2 hw) (W.inv_mem hw)
  set ρ : alternatingGroup (Fin m) →* MulAut V := (altRho hψ hAlt).comp (altLift ι) with hρ
  have hρK : ∀ τ, ρ τ ∈ largeK ψ ι R' := fun τ => altRho_altLift_mem_largeK hψ hAlt τ
  set N : Subgroup (alternatingGroup (Fin m)) := (centQuot W).comap ρ with hN_def
  have hN : N.Normal := ⟨fun τ hτ g => by
    change ρ (g * τ * g⁻¹) ∈ centQuot W
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_centQuot (hKW (hρK g)) hτ⟩
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rcases hN.eq_bot_or_eq_top with hNb | hNt
  · exfalso
    set κa := largeKappa ψ ι R' ⟨a, hAK ha⟩ with hκa
    have hcomm : ∀ τ : alternatingGroup (Fin m), κa * (τ : Perm (Fin m)) = τ * κa := by
      intro τ
      set τ' : alternatingGroup (Fin m) := ⟨_, conj_mem_alternatingGroup κa τ⟩ with hτ'
      have hconj : a * ρ τ * a⁻¹ = ρ τ' :=
        conj_altRho_altLift_of_mem_largeK hψ hAlt ⟨a, hAK ha⟩ τ
      have hmem : ρ (τ' * τ⁻¹) ∈ centQuot W := by
        rw [map_mul, map_inv, ← hconj]
        have h1 := conj_mem_centQuot (hKW (hρK τ)) ((centQuot W).inv_mem (hAq a ha))
        have h2 := (centQuot W).mul_mem (hAq a ha) h1
        simpa only [mul_assoc] using h2
      have h1 : τ' * τ⁻¹ ∈ N := hmem
      rw [hNb, Subgroup.mem_bot] at h1
      have h2 : κa * (τ : Perm (Fin m)) * κa⁻¹ = τ := congrArg Subtype.val (mul_inv_eq_one.1 h1)
      calc κa * (τ : Perm (Fin m)) = κa * τ * κa⁻¹ * κa := by group
        _ = τ * κa := by rw [h2]
    exact ha1 (eq_one_of_commute_alt (by omega) fun τ hτ => hcomm ⟨τ, hτ⟩)
  · have h1 : σ ∈ N := hNt ▸ Subgroup.mem_top σ
    exact h1

theorem natVia_or_altRho_altLift_mem_centQuot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hm : 5 ≤ m)
    (hn : 10 ≤ n) (hT₁ : TPerm (n - 1)) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender H A)
    (hAK : A ≤ largeK ψ ι R')
    (hC : ∀ k : ↥(largeK ψ ι R'), (∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w) →
      largeKappa ψ ι R' k = 1)
    {a : MulAut V} (ha : a ∈ A) (ha1 : largeKappa ψ ι R' ⟨a, hAK ha⟩ ≠ 1)
    (hcard : Nat.card (fixV (largeQ ψ ι R')) =
      Nat.card (autSub A (fixV (largeQ ψ ι R'))) *
        Nat.card (fixV (autSub A (fixV (largeQ ψ ι R'))))) :
    NatVia ψ (commV H) ∨
      ∀ σ : alternatingGroup (Fin m), altRho hψ hAlt (altLift ι σ) ∈ centQuot (fixV (largeQ ψ ι R')) := by
  set W := fixV (largeQ ψ ι R') with hW
  have hKW := largeK_le_stabSub ψ ι R'
  have hAW : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W := fun b hb w hw => ((hKW (hAK hb)) w).2 hw
  have hWA : commSub W A ≠ ⊥ := fun hbot =>
    ha1 (hC ⟨a, hAK ha⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw a ha)
  have hAut := B7_1_1 hA hAW hWA
  have hW2 := B1.sq_eq_one_sub hV W
  have hrk : rk (autSub A W) = rkIdx (fixV (autSub A W)) :=
    ((B1.card_eq_iff hW2 hAut.2.2.1).1 hcard).symm
  rcases B7_1_3 hV hA hAW hWA hrk with ⟨-, htop⟩ | ⟨hoff, -⟩
  · exact Or.inr (altRho_altLift_mem_centQuot hψ hAlt hm hAK htop ha ha1)
  ·
    left
    refine step_fix_of_ten_le hV hψ hAlt hoff hn hT₁ (ι ⟨0, by omega⟩) fun b hb => ?_
    have hk1 : largeKappa ψ ι R' ⟨b, hAK hb.1⟩ = 1 := hC ⟨b, hAK hb.1⟩ fun w hw => hb.2 w hw
    have h1 := (restrictHom_eq_one_iff (hK := largeK_le ψ ι R') ⟨(b : MulAut V), hAK hb.1⟩).1 hk1
      ⟨0, by omega⟩
    exact h1

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
