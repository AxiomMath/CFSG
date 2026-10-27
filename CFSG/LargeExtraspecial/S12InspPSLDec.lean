module

public import CFSG.LargeExtraspecial.S12InspPSLRes
public import CFSG.LargeExtraspecial.S12Classify

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def actX12 (g : G) : S.Xbar12 g →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  S.O.subtype.comp (S.Xbar12 g).subtype

variable {S}

theorem actX12_apply {g : G} (x : S.Xbar12 g) :
    S.actX12 g x = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl

theorem psl_isInv_iff {g : G} {W : Submodule (ZMod 2) S.Qt} :
    IsInv (S.actX12 g) W ↔ ∀ x ∈ S.Xbar12 g, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

theorem psl_isInv_map_rho {g : G} {W : Submodule (ZMod 2) S.Qt} (hW : IsInv (S.actX12 g) W)
    (m : S.M) :
    IsInv (S.actX12 g) (W.map ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) := by
  rw [psl_isInv_iff] at hW ⊢
  rintro x hx _ ⟨w, hw, rfl⟩
  have hn : (S.ρ m)⁻¹ ∈ normalizer (S.Xbar12 g : Set S.O) :=
    Mbar_le_normalizer_Xbar12 (S.Mbar.inv_mem ⟨m, rfl⟩)
  have hx' : (S.ρ m)⁻¹ * x * (S.ρ m)⁻¹⁻¹ ∈ S.Xbar12 g := (mem_normalizer_iff.mp hn x).mp hx
  refine ⟨_, hW _ hx' w hw, ?_⟩
  change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((S.ρ m)⁻¹ * x * (S.ρ m)⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) _
  rw [inv_inv, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel, one_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rfl

theorem psl_exists_apply_ne {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hred : ¬ S.IsReducible12) {W : Submodule (ZMod 2) S.Qt} (hW : IsInv (S.actX12 g) W)
    (hW0 : W ≠ ⊥) : ∃ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
  by_contra hcon
  push Not at hcon
  rw [psl_isInv_iff] at hW
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hXne : S.Xbar12 g ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htX
    exact htA.2.1 (by rw [htX]; rfl)
  have hfixE : ∀ τ ∈ S.Ebar12 g, ∀ w ∈ W, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro τ hτ w hw
    obtain ⟨x, hx, rfl⟩ := hS.cls τ hτ
    have hxw : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := hW _ (inv_mem hx) w hw
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hcon _ hxw, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hfixX : ∀ y ∈ S.Xbar12 g, ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem τ hτ => exact hfixE τ hτ
    | one => exact fun w _ => rfl
    | mul y₁ y₂ _ _ h₁ h₂ =>
      intro w hw
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h₂ w hw, h₁ w hw]
    | inv y _ h =>
      intro w hw
      conv_lhs => rw [← h w hw]
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
  rcases S.s12_fixed_eq_zero_or Mbar_le_normalizer_Xbar12 hXne with h0 | hr
  · apply hW0
    rw [eq_bot_iff]
    intro w hw
    exact (mem_bot _).mpr (h0 w fun y hy => hfixX y hy w hw)
  · exact hred hr

theorem psl_exists_minInv (g : G) (htop : (⊤ : Submodule (ZMod 2) S.Qt) ≠ ⊥) :
    ∃ W : Submodule (ZMod 2) S.Qt, W ≠ ⊥ ∧ IsInv (S.actX12 g) W ∧
      ∀ U : Submodule (ZMod 2) S.Qt, U ≠ ⊥ → IsInv (S.actX12 g) U →
        finrank (ZMod 2) W ≤ finrank (ZMod 2) U := by
  set s : Set (Submodule (ZMod 2) S.Qt) := {U | U ≠ ⊥ ∧ IsInv (S.actX12 g) U}
  have hs : (⊤ : Submodule (ZMod 2) S.Qt) ∈ s := ⟨htop, fun _ _ _ => mem_top⟩
  refine ⟨Function.argminOn (fun U : Submodule (ZMod 2) S.Qt => finrank (ZMod 2) U) s ⟨_, hs⟩,
    (Function.argminOn_mem _ s ⟨_, hs⟩).1, (Function.argminOn_mem _ s ⟨_, hs⟩).2,
    fun U hU hUi => Function.argminOn_le
      (fun U : Submodule (ZMod 2) S.Qt => finrank (ZMod 2) U) s ⟨hU, hUi⟩⟩

theorem psl_eq_bot_or_eq_of_minInv {g : G} {W U : Submodule (ZMod 2) S.Qt}
    (hmin : ∀ U : Submodule (ZMod 2) S.Qt, U ≠ ⊥ → IsInv (S.actX12 g) U →
      finrank (ZMod 2) W ≤ finrank (ZMod 2) U)
    (hUW : U ≤ W) (hU : IsInv (S.actX12 g) U) : U = ⊥ ∨ U = W := by
  by_cases h0 : U = ⊥
  · exact Or.inl h0
  · exact Or.inr (eq_of_le_of_finrank_eq hUW (le_antisymm (finrank_mono hUW) (hmin U h0 hU)))

theorem psl_isInv_inf {g : G} {U W : Submodule (ZMod 2) S.Qt} (hU : IsInv (S.actX12 g) U)
    (hW : IsInv (S.actX12 g) W) : IsInv (S.actX12 g) (U ⊓ W) :=
  fun x w hw => ⟨hU x w hw.1, hW x w hw.2⟩

theorem psl_comm_lines {g : G} {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (htX : t ∈ S.Xbar12 g) {W W' : Submodule (ZMod 2) S.Qt} (hW : IsInv (S.actX12 g) W)
    (hW' : IsInv (S.actX12 g) W') (hinf : W ⊓ W' = ⊥)
    (hne : ∃ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w)
    (hne' : ∃ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) :
    (∃ c ∈ W, c ≠ 0 ∧ c ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {c}) ∧
    (∃ c ∈ W', c ≠ 0 ∧ c ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      ∀ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {c}) ∧
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ W ⊔ W' := by
  set T := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hTW : ∀ {U : Submodule (ZMod 2) S.Qt}, IsInv (S.actX12 g) U → ∀ w ∈ U,
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ T ⊓ U := fun {U} hU w hw =>
    ⟨sub_mem_commSpace _ w, U.sub_mem (hU ⟨t, htX⟩ w hw) hw⟩
  obtain ⟨w₀, hw₀, hw₀t⟩ := hne
  obtain ⟨w₁, hw₁, hw₁t⟩ := hne'
  have h0 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ - w₀ ≠ 0 := sub_ne_zero.mpr hw₀t
  have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁ ≠ 0 := sub_ne_zero.mpr hw₁t
  have hA : 1 ≤ finrank (ZMod 2) (T ⊓ W : Submodule (ZMod 2) S.Qt) := by
    rw [Nat.one_le_iff_ne_zero, Ne, finrank_eq_zero]
    intro h
    have := hTW hW w₀ hw₀
    rw [h, Submodule.mem_bot] at this
    exact h0 this
  have hA' : 1 ≤ finrank (ZMod 2) (T ⊓ W' : Submodule (ZMod 2) S.Qt) := by
    rw [Nat.one_le_iff_ne_zero, Ne, finrank_eq_zero]
    intro h
    have := hTW hW' w₁ hw₁
    rw [h, Submodule.mem_bot] at this
    exact h1 this
  have hinf' : (T ⊓ W) ⊓ (T ⊓ W') = ⊥ :=
    eq_bot_iff.mpr fun v hv => hinf ▸ (⟨hv.1.2, hv.2.2⟩ : v ∈ W ⊓ W')
  have hsum := finrank_sup_add_finrank_inf_eq (T ⊓ W) (T ⊓ W')
  rw [hinf', finrank_bot, add_zero] at hsum
  have hle : (T ⊓ W) ⊔ (T ⊓ W') ≤ T := sup_le inf_le_left inf_le_left
  have hT2 : finrank (ZMod 2) T = 2 := htA.2.2.2.1
  have hfin := finrank_mono hle
  rw [hT2] at hfin
  have hA1 : finrank (ZMod 2) (T ⊓ W : Submodule (ZMod 2) S.Qt) = 1 := by omega
  have hA1' : finrank (ZMod 2) (T ⊓ W' : Submodule (ZMod 2) S.Qt) = 1 := by omega
  have hTeq : (T ⊓ W) ⊔ (T ⊓ W') = T := eq_of_le_of_finrank_eq hle (by omega)
  have hline : ∀ {U : Submodule (ZMod 2) S.Qt} {c : S.Qt}, finrank (ZMod 2) ↥(T ⊓ U) = 1 →
      c ∈ T ⊓ U → c ≠ 0 → T ⊓ U = span (ZMod 2) {c} := fun hU hc hc0 =>
    (eq_of_le_of_finrank_eq (span_le.mpr (Set.singleton_subset_iff.mpr hc))
      (by rw [finrank_span_singleton hc0, hU])).symm
  refine ⟨⟨_, (hTW hW w₀ hw₀).2, h0, (hTW hW w₀ hw₀).1, fun w hw => ?_⟩,
    ⟨_, (hTW hW' w₁ hw₁).2, h1, (hTW hW' w₁ hw₁).1, fun w hw => ?_⟩, ?_⟩
  · rw [← hline hA1 (hTW hW w₀ hw₀) h0]
    exact hTW hW w hw
  · rw [← hline hA1' (hTW hW' w₁ hw₁) h1]
    exact hTW hW' w hw
  · rw [← hTeq]
    exact sup_le_sup inf_le_right inf_le_right

theorem psl_decomp {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hred : ¬ S.IsReducible12) :
    (∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) ∨
    ∃ W W' : Submodule (ZMod 2) S.Qt, W ⊓ W' = ⊥ ∧ W ⊔ W' = ⊤ ∧
      IsInv (S.actX12 g) W ∧ IsInv (S.actX12 g) W' ∧
      (∀ U, U ≤ W → IsInv (S.actX12 g) U → U = ⊥ ∨ U = W) ∧
      (∀ U, U ≤ W' → IsInv (S.actX12 g) U → U = ⊥ ∨ U = W') ∧
      finrank (ZMod 2) W = finrank (ZMod 2) W' ∧
      (∃ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) ∧
      (∃ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have htop : (⊤ : Submodule (ZMod 2) S.Qt) ≠ ⊥ := by
    intro h
    apply htA.2.1
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ (⊤ : Submodule (ZMod 2) S.Qt) := mem_top
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    rfl
  obtain ⟨W, hW0, hW, hmin⟩ := psl_exists_minInv g htop
  have hirr := fun U => psl_eq_bot_or_eq_of_minInv (U := U) hmin
  by_cases hWt : W = ⊤
  · left
    intro U hU
    rcases hirr U (hWt ▸ le_top) hU with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hWt)
  right
  have hnot : ¬ ∀ m : S.M, ∀ v ∈ W, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W :=
    fun h => hred ⟨W, hW0, hWt, h⟩
  push Not at hnot
  obtain ⟨m, v, hvW, hmv⟩ := hnot
  set W' := W.map ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap with hW'def
  have hW' : IsInv (S.actX12 g) W' := psl_isInv_map_rho hW m
  have hdim : ∀ m' : S.M, finrank (ZMod 2)
      (W.map ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) = finrank (ZMod 2) W :=
    fun m' => LinearEquiv.finrank_map_eq _ W
  have hmin' : ∀ m' : S.M, ∀ U : Submodule (ZMod 2) S.Qt, U ≠ ⊥ → IsInv (S.actX12 g) U →
      finrank (ZMod 2) (W.map ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) ≤
        finrank (ZMod 2) U := fun m' U hU hUi => (hdim m').symm ▸ hmin U hU hUi
  have hne0 : ∀ m' : S.M,
      W.map ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≠ ⊥ := by
    intro m' h
    rw [Submodule.map_eq_bot_iff] at h
    exact hW0 h
  have hinf : W ⊓ W' = ⊥ := by
    rcases psl_eq_bot_or_eq_of_minInv (hmin' m) inf_le_right (psl_isInv_inf hW hW') with h | h
    · exact h
    · exfalso
      exact hmv ((inf_eq_right.mp h) ⟨v, hvW, rfl⟩)
  have hne := psl_exists_apply_ne ht htA hS hred hW hW0
  have hne' := psl_exists_apply_ne ht htA hS hred hW' (hne0 m)
  obtain ⟨-, -, hTle⟩ := psl_comm_lines htA htX hW hW' hinf hne hne'
  refine ⟨W, W', hinf, ?_, hW, hW', hirr, fun U => psl_eq_bot_or_eq_of_minInv (hmin' m),
    (hdim m).symm, hne, hne'⟩
  by_contra hsup
  have hnot2 : ¬ ∀ m' : S.M,
      W.map ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≤ W ⊔ W' := by
    intro hall
    refine hred ⟨W ⊔ W', fun h => hW0 (eq_bot_iff.mpr (h ▸ le_sup_left)), hsup,
      fun m' u hu => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hu
    obtain ⟨y', hy', rfl⟩ := hz
    rw [map_add]
    refine add_mem (hall m' ⟨y, hy, rfl⟩) ?_
    have := hall (m' * m) ⟨y', hy', rfl⟩
    rw [map_mul] at this
    exact this
  push Not at hnot2
  obtain ⟨m', hm'⟩ := hnot2
  set W'' := W.map ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
  have hW'' : IsInv (S.actX12 g) W'' := psl_isInv_map_rho hW m'
  have hsupinv : IsInv (S.actX12 g) (W ⊔ W') := by
    intro x w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hw
    rw [map_add]
    exact add_mem (mem_sup_left (hW x y hy)) (mem_sup_right (hW' x z hz))
  have hinf2 : W'' ⊓ (W ⊔ W') = ⊥ := by
    rcases psl_eq_bot_or_eq_of_minInv (hmin' m') inf_le_left (psl_isInv_inf hW'' hsupinv) with h | h
    · exact h
    · exact absurd (inf_eq_left.mp h) hm'
  obtain ⟨w, hw, hwt⟩ := psl_exists_apply_ne ht htA hS hred hW'' (hne0 m')
  have hmem : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ W'' ⊓ (W ⊔ W') :=
    ⟨W''.sub_mem (hW'' ⟨t, htX⟩ w hw) hw, hTle (sub_mem_commSpace _ w)⟩
  rw [hinf2, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hwt hmem

end Setting

end CFSG.LargeExtraspecial
