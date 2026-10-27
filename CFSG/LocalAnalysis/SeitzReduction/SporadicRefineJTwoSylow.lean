module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint Equiv
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def J2SylowSupportInput : Prop :=
  ∀ x ∈ j2S, x ∉ j2P → x * x = 1 →
    ∀ W : Subgroup (Perm (Fin 315)), W ≤ j2S → W ≤ j2P → Nat.card W = 16 →
      (∀ w ∈ W, w * w = 1) → (∀ w ∈ W, x * w * x⁻¹ ∈ W) →
      ∃ a ∈ W, ∃ b ∈ W, a * x = x * a ∧ b * x = x * b ∧ a ≠ 1 ∧ b ≠ 1 ∧
        a.support.card ≠ b.support.card

section Model


theorem j2_exists_conj_le_sylow {B : Subgroup (Perm (Fin 315))} (hBR : B ≤ j2R)
    (hB : IsPGroup 2 B) : ∃ g ∈ j2R, ∀ y ∈ B, g⁻¹ * y * g ∈ j2S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  set B' : Subgroup j2R := B.subgroupOf j2R with hB'
  have hB'p : IsPGroup 2 B' := hB.of_equiv (subgroupOfEquivOfLe hBR).symm
  obtain ⟨Q, hQ⟩ := hB'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq j2R Q T
  refine ⟨((g : j2R) : Perm (Fin 315))⁻¹, j2R.inv_mem g.2, fun y hy => ?_⟩
  have hyQ : (⟨y, hBR hy⟩ : j2R) ∈ (Q : Subgroup j2R) := hQ (mem_subgroupOf.2 hy)
  have hmem : g * ⟨y, hBR hy⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 j2R) : Set j2R) := by
    rw [Sylow.coe_smul]
    exact ⟨⟨y, hBR hy⟩, hyQ, rfl⟩
  rw [hg] at hmem
  have hmem' : g * ⟨y, hBR hy⟩ * g⁻¹ ∈ (T : Subgroup j2R) := hmem
  rw [hT] at hmem'
  have h1 := mem_subgroupOf.1 hmem'
  simpa [inv_inv] using h1

theorem j2OuterFixedClassesInput_of_sylow (h : J2SylowSupportInput) :
    J2OuterFixedClassesInput := by
  intro S _ _ hS τ hτ hout W hW16 hW2 hWτ
  obtain ⟨e⟩ := hS
  obtain ⟨E, hE, hEinner, -, -⟩ := ctuc_j2_full_automorphism_permutation_model
  set θ : S ≃* j2P := e.trans j2PermEquiv with hθ
  set τ' : MulAut j2P := ComponentClassification.RestrictedStd.Spor.transportAut θ τ with hτ'
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ'2 : τ' * τ' = 1 := ComponentClassification.RestrictedStd.Spor.transportAut_mul_self θ hτ2
  have hτ'out : τ' ∉ ComponentClassification.OuterAutomorphisms.inner j2P :=
    ComponentClassification.RestrictedStd.Spor.transportAut_not_mem_inner θ hout
  set x₀ : j2R := E.symm τ' with hx₀
  have hx₀act : ∀ p : j2P, ((τ' p : j2P) : Perm (Fin 315)) =
      (x₀ : Perm (Fin 315)) * p * (x₀ : Perm (Fin 315))⁻¹ := by
    intro p
    have h1 := hE x₀ p
    rw [hx₀, MulEquiv.apply_symm_apply] at h1
    exact h1
  have hx₀P : (x₀ : Perm (Fin 315)) ∉ j2P := by
    intro hx
    apply hτ'out
    rw [← hEinner]
    exact ⟨x₀, mem_subgroupOf.2 hx, by rw [hx₀]; exact MulEquiv.apply_symm_apply E τ'⟩
  have hx₀2 : (x₀ : Perm (Fin 315)) * x₀ = 1 := by
    have h1 : x₀ * x₀ = 1 := E.injective (by
      rw [map_mul, hx₀, MulEquiv.apply_symm_apply, hτ'2, map_one])
    exact congrArg Subtype.val h1
  have hx₀inv : (x₀ : Perm (Fin 315))⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx₀2
  set ι : S →* Perm (Fin 315) := j2P.subtype.comp θ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp θ.injective
  have hιP : ∀ s : S, ι s ∈ j2P := fun s => (θ s).2
  have hιτ : ∀ s : S, ι (τ s) = (x₀ : Perm (Fin 315)) * ι s * (x₀ : Perm (Fin 315))⁻¹ := by
    intro s
    have h2 : τ' (θ s) = θ (τ s) := by
      simp [hτ', ComponentClassification.RestrictedStd.Spor.transportAut]
    have h1 := hx₀act (θ s)
    rw [h2] at h1
    exact h1
  set W' : Subgroup (Perm (Fin 315)) := W.map ι with hW'
  have hW'P : W' ≤ j2P := by
    rintro _ ⟨w, -, rfl⟩
    exact hιP w
  have hW'card : Nat.card W' = 16 := by rw [hW', card_map_of_injective hιinj, hW16]
  have hW'2 : ∀ w ∈ W', w * w = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, hW2 w hw, map_one]
  have hτW : ∀ w ∈ W, τ w ∈ W := by
    intro w hw
    rw [← hWτ]
    exact ⟨w, hw, rfl⟩
  have hW'x : ∀ w ∈ W', (x₀ : Perm (Fin 315)) * w * (x₀ : Perm (Fin 315))⁻¹ ∈ W' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hιτ]
    exact ⟨τ w, hτW w hw, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW'p : IsPGroup 2 W' := fun w =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]; exact hW'2 _ w.2)⟩
  have hx₀1 : (x₀ : Perm (Fin 315)) ≠ 1 := fun h1 => hx₀P (h1 ▸ j2P.one_mem)
  have hx₀o : orderOf (x₀ : Perm (Fin 315)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hx₀2) hx₀1
  have hx₀p : IsPGroup 2 (zpowers (x₀ : Perm (Fin 315))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀o, pow_one])
  have hnorm : zpowers (x₀ : Perm (Fin 315)) ≤ normalizer (W' : Set (Perm (Fin 315))) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hW'x w hw
    · intro hw
      have hw' : w = (x₀ : Perm (Fin 315)) * ((x₀ : Perm (Fin 315)) * w *
          (x₀ : Perm (Fin 315))⁻¹) * (x₀ : Perm (Fin 315))⁻¹ := by
        rw [hx₀inv]
        calc w = ((x₀ : Perm (Fin 315)) * x₀) * w * ((x₀ : Perm (Fin 315)) * x₀) := by
              rw [hx₀2, one_mul, mul_one]
          _ = (x₀ : Perm (Fin 315)) * ((x₀ : Perm (Fin 315)) * w * x₀) * x₀ := by group
      rw [hw']
      exact hW'x _ hw
  have hBp : IsPGroup 2 (W' ⊔ zpowers (x₀ : Perm (Fin 315)) : Subgroup (Perm (Fin 315))) :=
    IsPGroup.to_sup_of_normal_left' hW'p hx₀p hnorm
  have hPR : j2P ≤ j2R := le_sup_left
  have hBR : W' ⊔ zpowers (x₀ : Perm (Fin 315)) ≤ j2R :=
    sup_le (hW'P.trans hPR) (zpowers_le.2 x₀.2)
  obtain ⟨g, hgR, hg⟩ := j2_exists_conj_le_sylow hBR hBp
  have hNsub := ctuc_j2_normalizing_involution_permutation_model.2.2.2.2.2.2.2.1
  have hN : ∀ y ∈ j2R, ∀ p ∈ j2P, y * p * y⁻¹ ∈ j2P := by
    intro y hy p hp
    have h1 := hNsub.conj_mem ⟨p, hPR hp⟩ (by simpa [Subgroup.mem_subgroupOf] using hp) ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  set x : Perm (Fin 315) := g⁻¹ * (x₀ : Perm (Fin 315)) * g with hxdef
  have hxS : x ∈ j2S := hg _ (mem_sup_right (mem_zpowers _))
  have hxP : x ∉ j2P := by
    intro hx
    apply hx₀P
    have h1 := hN g hgR x hx
    rwa [hxdef, show g * (g⁻¹ * (x₀ : Perm (Fin 315)) * g) * g⁻¹ = x₀ by group] at h1
  have hxx : x * x = 1 := by
    rw [hxdef, show g⁻¹ * (x₀ : Perm (Fin 315)) * g * (g⁻¹ * x₀ * g) =
      g⁻¹ * ((x₀ : Perm (Fin 315)) * x₀) * g by group, hx₀2]
    group
  set W'' : Subgroup (Perm (Fin 315)) := W'.map (MulAut.conj g⁻¹).toMonoidHom with hW''
  have hconj : ∀ y, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := by
    intro y
    simp
  have hW''S : W'' ≤ j2S := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hconj]
    exact hg w (mem_sup_left hw)
  have hW''P : W'' ≤ j2P := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hconj]
    have h1 := hN g⁻¹ (j2R.inv_mem hgR) w (hW'P hw)
    simpa using h1
  have hW''card : Nat.card W'' = 16 := by
    rw [hW'', card_map_of_injective (MulAut.conj g⁻¹).injective, hW'card]
  have hW''2 : ∀ w ∈ W'', w * w = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, hW'2 w hw, map_one]
  have hW''x : ∀ w ∈ W'', x * w * x⁻¹ ∈ W'' := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(x₀ : Perm (Fin 315)) * w * (x₀ : Perm (Fin 315))⁻¹, hW'x w hw, ?_⟩
    rw [hconj, hconj, hxdef]
    group
  obtain ⟨a'', ha'', b'', hb'', hax, hbx, ha1, hb1, hsupp⟩ :=
    h x hxS hxP hxx W'' hW''S hW''P hW''card hW''2 hW''x
  obtain ⟨_, ⟨a, haW, rfl⟩, rfl⟩ := ha''
  obtain ⟨_, ⟨b, hbW, rfl⟩, rfl⟩ := hb''
  have hfix : ∀ c : S, (MulAut.conj g⁻¹).toMonoidHom (ι c) * x =
      x * (MulAut.conj g⁻¹).toMonoidHom (ι c) → τ c = c := by
    intro c hc
    rw [hconj, hxdef] at hc
    have h1 : ι c * x₀ = x₀ * ι c := by
      calc ι c * x₀ = g * (g⁻¹ * ι c * g * (g⁻¹ * x₀ * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * x₀ * g * (g⁻¹ * ι c * g)) * g⁻¹ := by rw [hc]
        _ = x₀ * ι c := by group
    apply hιinj
    rw [hιτ, ← h1, mul_inv_cancel_right]
  refine ⟨a, mem_inf.2 ⟨haW, hfix a hax⟩, b, mem_inf.2 ⟨hbW, hfix b hbx⟩,
    fun h1 => ha1 (by rw [h1, map_one, map_one]), fun h1 => hb1 (by rw [h1, map_one, map_one]),
    fun k hk => hsupp ?_⟩
  have hb' : (MulAut.conj g⁻¹).toMonoidHom (ι b) =
      (MulAut.conj g⁻¹).toMonoidHom (ι k) * (MulAut.conj g⁻¹).toMonoidHom (ι a) *
        ((MulAut.conj g⁻¹).toMonoidHom (ι k))⁻¹ := by
    rw [← hk]
    simp only [map_mul, map_inv]
  rw [hb', Equiv.Perm.card_support_conj]

theorem lFiveJTwoInput_of_sylow (h : J2SylowSupportInput) :
    LinearPilot.LFiveJTwoInput :=
  lFiveJTwoInput_of (j2OuterFixedClassesInput_of_sylow h)

end Model

end CFSG.SeitzReduction.SporadicRefine
