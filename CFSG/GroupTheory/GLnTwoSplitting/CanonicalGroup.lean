module

public import CFSG.GroupTheory.GLnTwoSplitting.CanonicalLift

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {X : NatExt G E} [FiniteDimensional (ZMod 2) E]

variable (X) in
theorem exists_isCanonical (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} (he₀ : e₀ ≠ 0)
    {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0) (hψ0 : ψ ≠ 0) : ∃ a, X.IsCanonical hψ a := by
  obtain ⟨F, rfl, rfl⟩ := exists_frame he₀ hψ0 hψ
  exact X.exists_isCanonical_of_frame F hE

omit [FiniteDimensional (ZMod 2) E] in
theorem IsCanonical.apply_e₀ {e₀ : E} {ψ : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {a : G}
    (ha : X.IsCanonical hψ a) : X.π a e₀ = e₀ := by
  rw [ha.1, transvection_apply, hψ, zero_smul, add_zero]

omit [FiniteDimensional (ZMod 2) E] in
theorem ι_mul_comm_of_apply {e₀ w : E} (hw : w ∈ (ZMod 2) ∙ e₀) {g : G} (hg : X.π g e₀ = e₀) :
    X.ι w * g = g * X.ι w := by
  rw [X.mul_ι, apply_eq_of_mem_span hg hw]

omit [FiniteDimensional (ZMod 2) E] in
theorem IsCanonical.mul_ι {e₀ : E} {ψ : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {a : G}
    (ha : X.IsCanonical hψ a) {w : E} (hw : w ∈ (ZMod 2) ∙ e₀) : X.IsCanonical hψ (a * X.ι w) := by
  refine ⟨by rw [map_mul, X.π_ι, mul_one, ha.1], fun g hge₀ hgψ => ?_⟩
  obtain ⟨y, hy, hgy⟩ := ha.2 g hge₀ hgψ
  refine ⟨y, hy, ?_⟩
  rw [show g * (a * X.ι w) * g⁻¹ = g * a * g⁻¹ * (g * X.ι w * g⁻¹) by group, hgy, X.conj,
    apply_eq_of_mem_span hge₀ hw, mul_assoc, ← X.ι_add, mul_assoc, ← X.ι_add, add_comm]

omit [FiniteDimensional (ZMod 2) E] in
theorem IsCanonical.of_eqMod {e₀ : E} {ψ : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {a b : G}
    (ha : X.IsCanonical hψ a) (hab : X.EqMod e₀ a b) : X.IsCanonical hψ b := by
  obtain ⟨w, hw, rfl⟩ := hab
  exact ha.mul_ι hw

theorem eqMod_of_forall {U : Submodule (ZMod 2) E} (hU : 3 ≤ finrank (ZMod 2) U) {e₀ : E}
    {b b' : G} (hbb' : X.π b = X.π b')
    (hb : ∀ (χ : Dual (ZMod 2) E) (k : E) (hχk : χ k = 0), χ e₀ = 0 → k ∈ U → ∀ g,
      X.π g = LinearEquiv.transvection hχk → X.EqMod e₀ b (g * b * g⁻¹))
    (hb' : ∀ (χ : Dual (ZMod 2) E) (k : E) (hχk : χ k = 0), χ e₀ = 0 → k ∈ U → ∀ g,
      X.π g = LinearEquiv.transvection hχk → X.EqMod e₀ b' (g * b' * g⁻¹)) :
    X.EqMod e₀ b b' := by
  obtain ⟨w, rfl⟩ := X.exists_eq_mul_ι hbb'
  refine ⟨w, mem_span_of_forall_smul_mem_span hU e₀ w fun χ k hχe₀ hχk hk => ?_, rfl⟩
  obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection hχk)
  obtain ⟨y, hy, hgy⟩ := hb χ k hχk hχe₀ hk g hg
  obtain ⟨y', hy', hgy'⟩ := hb' χ k hχk hχe₀ hk g hg
  have h1 : g * (b * X.ι w) * g⁻¹ = b * X.ι (y + LinearEquiv.transvection hχk w) := by
    rw [show g * (b * X.ι w) * g⁻¹ = g * b * g⁻¹ * (g * X.ι w * g⁻¹) by group, hgy, X.conj, hg,
      mul_assoc, ← X.ι_add]
  rw [h1, mul_assoc, ← X.ι_add] at hgy'
  have h2 := X.injective (mul_left_cancel hgy')
  rw [transvection_apply] at h2
  have : χ w • k = y + y' := by
    calc χ w • k = (y + (w + χ w • k)) + (y + w) := by
          calc χ w • k = χ w • k + (y + y) + (w + w) := by
                rw [two_add_self, two_add_self, add_zero, add_zero]
            _ = _ := by abel
      _ = (w + y') + (y + w) := by rw [h2]
      _ = y + y' + (w + w) := by abel
      _ = _ := by rw [two_add_self, add_zero]
  rw [this]
  exact add_mem hy hy'

omit [FiniteDimensional (ZMod 2) E] in
theorem transvection_centralises {e₀ : E} {ψ χ : Dual (ZMod 2) E} {k : E} (hχk : χ k = 0)
    (hχe₀ : χ e₀ = 0) (hψk : ψ k = 0) {g : G} (hg : X.π g = LinearEquiv.transvection hχk) :
    X.π g e₀ = e₀ ∧ ∀ w, ψ (X.π g w) = ψ w := by
  refine ⟨by rw [hg, transvection_apply, hχe₀, zero_smul, add_zero], fun w => ?_⟩
  rw [hg, transvection_apply, map_add, map_smul, hψk, smul_zero, add_zero]

theorem IsCanonical.eqMod (hE : 4 ≤ finrank (ZMod 2) E) {e₀ : E} {ψ : Dual (ZMod 2) E}
    {hψ : ψ e₀ = 0} {a b : G} (ha : X.IsCanonical hψ a) (hb : X.IsCanonical hψ b) :
    X.EqMod e₀ a b := by
  refine eqMod_of_forall (U := LinearMap.ker ψ) (by have := finrank_ker_add_one_ge ψ; omega)
    (by rw [ha.1, hb.1]) (fun χ k hχk hχe₀ hk g hg => ?_) fun χ k hχk hχe₀ hk g hg => ?_
  · obtain ⟨h1, h2⟩ := transvection_centralises hχk hχe₀ hk hg
    exact ha.2 g h1 h2
  · obtain ⟨h1, h2⟩ := transvection_centralises hχk hχe₀ hk hg
    exact hb.2 g h1 h2

omit [FiniteDimensional (ZMod 2) E] in
theorem IsCanonical.conj {e₀ : E} {ψ : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {a : G}
    (ha : X.IsCanonical hψ a) {h : G} (hh : X.π h e₀ = e₀)
    (hψ' : (ψ ∘ₗ ((X.π h).symm : E →ₗ[ZMod 2] E)) e₀ = 0) :
    X.IsCanonical hψ' (h * a * h⁻¹) := by
  refine ⟨?_, fun g hge₀ hgψ => ?_⟩
  · rw [map_mul, map_mul, map_inv, ha.1, mul_transvection_mul_inv _ hψ
      (transvection_comp_apply_eq_zero _ hψ)]
    ext w
    rw [transvection_apply, transvection_apply, hh]
  · have hh' : (X.π h).symm e₀ = e₀ := by rw [LinearEquiv.symm_apply_eq, hh]
    obtain ⟨y, hy, hgy⟩ := ha.2 (h⁻¹ * g * h)
      (by rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh, hge₀];
          exact hh')
      (fun w => by
        have := hgψ (X.π h w)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
          at this
        rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact this)
    refine ⟨y, hy, ?_⟩
    calc g * (h * a * h⁻¹) * g⁻¹ = h * ((h⁻¹ * g * h) * a * (h⁻¹ * g * h)⁻¹) * h⁻¹ := by group
      _ = h * a * h⁻¹ * X.ι y := by
          rw [hgy, show h * (a * X.ι y) * h⁻¹ = h * a * h⁻¹ * (h * X.ι y * h⁻¹) by group, X.conj,
            apply_eq_of_mem_span hh hy]

theorem IsCanonical.mul (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} (he₀ : e₀ ≠ 0)
    {ψ ψ' : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {hψ' : ψ' e₀ = 0} {a b : G}
    (ha : X.IsCanonical hψ a) (hb : X.IsCanonical hψ' b) (hne : ψ ≠ ψ')
    (hψψ' : (ψ + ψ') e₀ = 0) : X.IsCanonical hψψ' (a * b) := by
  have hsum : ψ + ψ' ≠ 0 := fun h => hne ((two_add_eq_iff.1 h).trans (zero_add ψ'))
  obtain ⟨c, hc⟩ := X.exists_isCanonical hE he₀ hψψ' hsum
  refine hc.of_eqMod (eqMod_of_forall (U := LinearMap.ker ψ ⊓ LinearMap.ker ψ')
    (by have := finrank_ker_inf_ker_add_two_ge ψ ψ'; omega)
    (by rw [hc.1, map_mul, ha.1, hb.1, transvection_mul_transvection_right])
    (fun χ k hχk hχe₀ hk g hg => ?_) fun χ k hχk hχe₀ hk g hg => ?_)
  · obtain ⟨h1, h2⟩ := transvection_centralises (ψ := ψ + ψ') hχk hχe₀
      (by rw [LinearMap.add_apply, hk.1, hk.2, add_zero]) hg
    exact hc.2 g h1 h2
  · obtain ⟨h1, h2⟩ := transvection_centralises hχk hχe₀ hk.1 hg
    obtain ⟨-, h2'⟩ := transvection_centralises hχk hχe₀ hk.2 hg
    obtain ⟨y, hy, hgy⟩ := ha.2 g h1 h2
    obtain ⟨y', hy', hgy'⟩ := hb.2 g h1 h2'
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group, hgy, hgy', mul_assoc,
      ← mul_assoc (X.ι y), ι_mul_comm_of_apply hy hb.apply_e₀, mul_assoc, ← X.ι_add, ← mul_assoc]

omit [FiniteDimensional (ZMod 2) E] in
theorem IsCanonical.congr {e₀ : E} {ψ ψ' : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} (hψψ' : ψ = ψ')
    (hψ' : ψ' e₀ = 0) {a : G} (ha : X.IsCanonical hψ a) : X.IsCanonical hψ' a := by
  subst hψψ'
  exact ha

theorem IsCanonical.mul_self_eq (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} {ψ ψ' : Dual (ZMod 2) E}
    {hψ : ψ e₀ = 0} {hψ' : ψ' e₀ = 0} (hψ0 : ψ ≠ 0) (hψ'0 : ψ' ≠ 0) {a b : G}
    (ha : X.IsCanonical hψ a) (hb : X.IsCanonical hψ' b) : a * a = b * b := by
  obtain ⟨σ, hσe₀, hσψ⟩ := exists_comp_eq_of_apply_eq_zero hψ0 hψ'0 hψ hψ'
  obtain ⟨h, hh⟩ := X.surjective σ⁻¹
  have hhe₀ : X.π h e₀ = e₀ := by
    rw [hh]
    exact (LinearEquiv.symm_apply_eq σ).2 hσe₀.symm
  have hform : ψ ∘ₗ ((X.π h).symm : E →ₗ[ZMod 2] E) = ψ' := by
    rw [hh, ← hσψ]
    rfl
  have hc := (ha.conj hhe₀ (by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 hhe₀.symm,
      hψ])).congr hform hψ'
  obtain ⟨w, hw, hbw⟩ := hb.eqMod (by omega) hc
  obtain ⟨w₁, hw₁, ha₁⟩ := X.sq_mem_of_π_eq_transvection (by omega) hψ ha.1
  calc a * a = h * (a * a) * h⁻¹ := by rw [ha₁, X.conj, apply_eq_of_mem_span hhe₀ hw₁]
    _ = (h * a * h⁻¹) * (h * a * h⁻¹) := by group
    _ = b * b := by
        rw [hbw, mul_assoc, ← mul_assoc (X.ι w), ι_mul_comm_of_apply hw hb.apply_e₀, mul_assoc,
          X.ι_mul_self, mul_one]

theorem exists_three_forms (hE : 4 ≤ finrank (ZMod 2) E) (e₀ : E) :
    ∃ ψ₁ ψ₂ ψ₃ : Dual (ZMod 2) E, ψ₁ e₀ = 0 ∧ ψ₂ e₀ = 0 ∧ ψ₃ e₀ = 0 ∧ ψ₁ ≠ 0 ∧ ψ₂ ≠ 0 ∧
      ψ₃ ≠ 0 ∧ ψ₁ ≠ ψ₂ ∧ ψ₁ ≠ ψ₃ ∧ ψ₂ ≠ ψ₃ ∧ ψ₂ + ψ₃ ≠ 0 ∧ ψ₁ ≠ ψ₂ + ψ₃ := by
  have hP : 3 ≤ finrank (ZMod 2) (LinearMap.ker (Module.Dual.eval (ZMod 2) E e₀)) := by
    have h1 := finrank_ker_add_one_ge (E := Dual (ZMod 2) E) (Module.Dual.eval (ZMod 2) E e₀)
    rw [Subspace.dual_finrank_eq] at h1
    omega
  obtain ⟨ψ₁, hψ₁P, hψ₁⟩ := exists_mem_notMem_of_finrank_lt
    (U := LinearMap.ker (Module.Dual.eval (ZMod 2) E e₀))
    (S := span (ZMod 2) {(0 : Dual (ZMod 2) E), 0})
    ((finrank_span_pair_le _ _).trans_lt (by omega))
  obtain ⟨ψ₂, hψ₂P, hψ₂⟩ := exists_mem_notMem_of_finrank_lt
    (U := LinearMap.ker (Module.Dual.eval (ZMod 2) E e₀))
    (S := span (ZMod 2) {ψ₁, 0}) ((finrank_span_pair_le _ _).trans_lt (by omega))
  obtain ⟨ψ₃, hψ₃P, hψ₃⟩ := exists_mem_notMem_of_finrank_lt
    (U := LinearMap.ker (Module.Dual.eval (ZMod 2) E e₀))
    (S := span (ZMod 2) {ψ₁, ψ₂}) ((finrank_span_pair_le _ _).trans_lt (by omega))
  refine ⟨ψ₁, ψ₂, ψ₃, hψ₁P, hψ₂P, hψ₃P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hψ₁ (zero_mem _)
  · rintro rfl
    exact hψ₂ (zero_mem _)
  · rintro rfl
    exact hψ₃ (zero_mem _)
  · rintro rfl
    exact hψ₂ (subset_span (by simp))
  · rintro rfl
    exact hψ₃ (subset_span (by simp))
  · rintro rfl
    exact hψ₃ (subset_span (by simp))
  · intro h
    refine hψ₃ ?_
    rw [show ψ₃ = ψ₂ from ((two_add_eq_iff.1 h).trans (zero_add _)).symm]
    exact subset_span (by simp)
  · intro h
    refine hψ₃ ?_
    have : ψ₃ = ψ₁ + ψ₂ := by
      calc ψ₃ = ψ₃ + (ψ₂ + ψ₂) := by rw [two_add_self, add_zero]
        _ = ψ₁ + ψ₂ := by rw [h]; abel
    rw [this]
    exact add_mem (subset_span (by simp)) (subset_span (by simp))

theorem IsCanonical.mul_self (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} (he₀ : e₀ ≠ 0)
    {ψ : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} (hψ0 : ψ ≠ 0) {a : G} (ha : X.IsCanonical hψ a) :
    a * a = 1 := by
  obtain ⟨w, hw, haw⟩ := X.sq_mem_of_π_eq_transvection (by omega) hψ ha.1
  obtain hw0 | hwe := mem_span_singleton_iff_two.1 hw
  · rw [haw, hw0, X.ι_zero]
  exfalso
  rw [hwe] at haw
  have hsq : ∀ {φ : Dual (ZMod 2) E} {hφ : φ e₀ = 0}, φ ≠ 0 → ∀ {b : G},
      X.IsCanonical hφ b → b * b = X.ι e₀ := fun hφ0 b hb => by
    rw [← haw]
    exact (ha.mul_self_eq hE hψ0 hφ0 hb).symm
  have hinv : ∀ {φ : Dual (ZMod 2) E} {hφ : φ e₀ = 0}, φ ≠ 0 → ∀ {b : G},
      X.IsCanonical hφ b → b⁻¹ = b * X.ι e₀ := fun hφ0 b hb => by
    rw [← X.ι_inv, ← hsq hφ0 hb]
    group
  have hcomm : ∀ {φ φ' : Dual (ZMod 2) E} {hφ : φ e₀ = 0} {hφ' : φ' e₀ = 0}, φ ≠ 0 → φ' ≠ 0 →
      φ ≠ φ' → ∀ {b b' : G}, X.IsCanonical hφ b → X.IsCanonical hφ' b' →
        b * b' * b⁻¹ * b'⁻¹ = X.ι e₀ := by
    intro φ φ' hφ hφ' hφ0 hφ'0 hne b b' hb hb'
    have hφφ' : (φ + φ') e₀ = 0 := by rw [LinearMap.add_apply, hφ, hφ', add_zero]
    have hsum : φ + φ' ≠ 0 := fun h => hne ((two_add_eq_iff.1 h).trans (zero_add φ'))
    have h1 := hsq hsum (hb.mul hE he₀ hb' hne hφφ')
    have hc := ι_mul_comm_of_apply (X := X) (mem_span_singleton_self e₀) hb'.apply_e₀
    rw [hinv hφ0 hb, hinv hφ'0 hb']
    calc b * b' * (b * X.ι e₀) * (b' * X.ι e₀) = b * b' * b * (X.ι e₀ * b') * X.ι e₀ := by group
      _ = b * b' * (b * b') * (X.ι e₀ * X.ι e₀) := by rw [hc]; group
      _ = X.ι e₀ := by rw [h1, X.ι_mul_self, mul_one]
  obtain ⟨ψ₁, ψ₂, ψ₃, h₁, h₂, h₃, h₁0, h₂0, h₃0, h₁₂, h₁₃, h₂₃, h₂₃0, h₁₂₃⟩ :=
    exists_three_forms (by omega) e₀
  obtain ⟨a₁, ha₁⟩ := X.exists_isCanonical hE he₀ h₁ h₁0
  obtain ⟨a₂, ha₂⟩ := X.exists_isCanonical hE he₀ h₂ h₂0
  obtain ⟨a₃, ha₃⟩ := X.exists_isCanonical hE he₀ h₃ h₃0
  have h₂₃e₀ : (ψ₂ + ψ₃) e₀ = 0 := by rw [LinearMap.add_apply, h₂, h₃, add_zero]
  have ha₂₃ := ha₂.mul hE he₀ ha₃ h₂₃ h₂₃e₀
  have e1 := hcomm h₁0 h₂₃0 h₁₂₃ ha₁ ha₂₃
  have e2 := hcomm h₁0 h₂0 h₁₂ ha₁ ha₂
  have e3 := hcomm h₁0 h₃0 h₁₃ ha₁ ha₃
  have e4 : a₁ * (a₂ * a₃) * a₁⁻¹ * (a₂ * a₃)⁻¹ =
      (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (a₂ * (a₁ * a₃ * a₁⁻¹ * a₃⁻¹) * a₂⁻¹) := by group
  rw [e4, e2, e3, X.conj, ha₂.apply_e₀, X.ι_mul_self] at e1
  exact he₀ (X.ι_eq_one_iff.1 e1.symm)

theorem IsCanonical.commute (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} (he₀ : e₀ ≠ 0)
    {ψ ψ' : Dual (ZMod 2) E} {hψ : ψ e₀ = 0} {hψ' : ψ' e₀ = 0} (hψ0 : ψ ≠ 0) (hψ'0 : ψ' ≠ 0)
    (hne : ψ ≠ ψ') {a b : G} (ha : X.IsCanonical hψ a) (hb : X.IsCanonical hψ' b) :
    a * b = b * a := by
  have hψψ' : (ψ + ψ') e₀ = 0 := by rw [LinearMap.add_apply, hψ, hψ', add_zero]
  have hsum : ψ + ψ' ≠ 0 := fun h => hne ((two_add_eq_iff.1 h).trans (zero_add ψ'))
  have h1 := (ha.mul hE he₀ hb hne hψψ').mul_self hE he₀ hsum
  have h2 := ha.mul_self hE he₀ hψ0
  have h3 := hb.mul_self hE he₀ hψ'0
  calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
    _ = (a * a) * b * (a * (b * b)) := by group
    _ = b * a := by rw [h2, h3, one_mul, mul_one]

omit [FiniteDimensional (ZMod 2) E] in
theorem transvection_ne_one {e₀ : E} (he₀ : e₀ ≠ 0) {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0)
    (hψ0 : ψ ≠ 0) : LinearEquiv.transvection hψ ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, ψ u ≠ 0 := by
    by_contra! h'
    exact hψ0 (LinearMap.ext h')
  have := congrArg (fun σ : E ≃ₗ[ZMod 2] E => σ u) h
  simp only [transvection_apply, zmod_two_eq_one_of_ne_zero hu, one_smul] at this
  exact he₀ (by simpa using this)

variable (X) in
@[expose] def canonicalGroup (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E} (he₀ : e₀ ≠ 0) :
    Subgroup G where
  carrier := {g | X.EqMod e₀ 1 g ∨
    ∃ (ψ : Dual (ZMod 2) E) (hψ : ψ e₀ = 0), ψ ≠ 0 ∧ X.IsCanonical hψ g}
  mul_mem' := by
    rintro g g' (⟨w, hw, rfl⟩ | ⟨ψ, hψ, hψ0, hg⟩) (⟨w', hw', rfl⟩ | ⟨ψ', hψ', hψ'0, hg'⟩)
    · exact Or.inl ⟨w + w', add_mem hw hw', by rw [one_mul, one_mul, one_mul, X.ι_add]⟩
    · refine Or.inr ⟨ψ', hψ', hψ'0, ?_⟩
      rw [one_mul, ι_mul_comm_of_apply hw hg'.apply_e₀]
      exact hg'.mul_ι hw
    · refine Or.inr ⟨ψ, hψ, hψ0, ?_⟩
      rw [one_mul]
      exact hg.mul_ι hw'
    · by_cases hψψ' : ψ = ψ'
      · subst hψψ'
        obtain ⟨w, hw, rfl⟩ := hg.eqMod (by omega) hg'
        refine Or.inl ⟨w, hw, ?_⟩
        rw [← mul_assoc, hg.mul_self hE he₀ hψ0, one_mul]
      · have hψψ'0 : (ψ + ψ') e₀ = 0 := by rw [LinearMap.add_apply, hψ, hψ', add_zero]
        exact Or.inr ⟨ψ + ψ', hψψ'0, fun h => hψψ' ((two_add_eq_iff.1 h).trans (zero_add ψ')),
          hg.mul hE he₀ hg' hψψ' hψψ'0⟩
  one_mem' := Or.inl (EqMod.refl e₀ 1)
  inv_mem' := by
    rintro g (⟨w, hw, rfl⟩ | ⟨ψ, hψ, hψ0, hg⟩)
    · exact Or.inl ⟨w, hw, by rw [one_mul, X.ι_inv]⟩
    · refine Or.inr ⟨ψ, hψ, hψ0, ?_⟩
      rw [inv_eq_of_mul_eq_one_left (hg.mul_self hE he₀ hψ0)]
      exact hg

variable {hE : 6 ≤ finrank (ZMod 2) E} {e₀ : E} {he₀ : e₀ ≠ 0}

theorem mem_canonicalGroup {g : G} : g ∈ X.canonicalGroup hE he₀ ↔ (X.EqMod e₀ 1 g ∨
    ∃ (ψ : Dual (ZMod 2) E) (hψ : ψ e₀ = 0), ψ ≠ 0 ∧ X.IsCanonical hψ g) :=
  Iff.rfl

theorem canonicalGroup_mul_self {g : G} (hg : g ∈ X.canonicalGroup hE he₀) : g * g = 1 := by
  rcases hg with ⟨w, -, rfl⟩ | ⟨ψ, hψ, hψ0, hg⟩
  · rw [one_mul, X.ι_mul_self]
  · exact hg.mul_self hE he₀ hψ0

theorem canonicalGroup_commute {g g' : G} (hg : g ∈ X.canonicalGroup hE he₀)
    (hg' : g' ∈ X.canonicalGroup hE he₀) : g * g' = g' * g := by
  rcases hg with ⟨w, hw, rfl⟩ | ⟨ψ, hψ, hψ0, hg⟩
  · rcases hg' with ⟨w', -, rfl⟩ | ⟨ψ', hψ', -, hg'⟩
    · rw [one_mul, one_mul, X.ι_mul_comm]
    · rw [one_mul, ι_mul_comm_of_apply hw hg'.apply_e₀]
  · rcases hg' with ⟨w', hw', rfl⟩ | ⟨ψ', hψ', hψ'0, hg'⟩
    · rw [one_mul, ι_mul_comm_of_apply hw' hg.apply_e₀]
    · by_cases hψψ' : ψ = ψ'
      · subst hψψ'
        obtain ⟨w, hw, rfl⟩ := hg.eqMod (by omega) hg'
        rw [mul_assoc g (X.ι w) g, ι_mul_comm_of_apply hw hg.apply_e₀]
      · exact hg.commute hE he₀ hψ0 hψ'0 hψψ' hg'

theorem conj_mem_canonicalGroup {h g : G} (hh : X.π h e₀ = e₀)
    (hg : g ∈ X.canonicalGroup hE he₀) : h * g * h⁻¹ ∈ X.canonicalGroup hE he₀ := by
  rcases hg with ⟨w, hw, rfl⟩ | ⟨ψ, hψ, hψ0, hg⟩
  · exact Or.inl ⟨w, hw, by rw [one_mul, X.conj, apply_eq_of_mem_span hh hw]⟩
  · have hψ' : (ψ ∘ₗ ((X.π h).symm : E →ₗ[ZMod 2] E)) e₀ = 0 := by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 hh.symm, hψ]
    refine Or.inr ⟨_, hψ', fun h0 => hψ0 (LinearMap.ext fun w => ?_), hg.conj hh hψ'⟩
    have := congrArg (fun φ : Dual (ZMod 2) E => φ (X.π h w)) h0
    simpa using this

theorem ι_mem_canonicalGroup_iff {v : E} :
    X.ι v ∈ X.canonicalGroup hE he₀ ↔ v ∈ (ZMod 2) ∙ e₀ := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨v, h, (one_mul _).symm⟩⟩
  rcases h with ⟨w, hw, hvw⟩ | ⟨ψ, hψ, hψ0, hg⟩
  · rw [one_mul] at hvw
    rwa [X.injective hvw]
  · exact absurd (hg.1.symm.trans (X.π_ι v)) (transvection_ne_one he₀ hψ hψ0)

theorem exists_π_eq_of_mem_canonicalGroup {g : G} (hg : g ∈ X.canonicalGroup hE he₀) :
    ∃ (ψ : Dual (ZMod 2) E) (hψ : ψ e₀ = 0), X.π g = LinearEquiv.transvection hψ := by
  rcases hg with ⟨w, -, rfl⟩ | ⟨ψ, hψ, -, hg⟩
  · exact ⟨0, LinearMap.zero_apply e₀, by rw [one_mul, X.π_ι, transvection_zero_form]⟩
  · exact ⟨ψ, hψ, hg.1⟩

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
