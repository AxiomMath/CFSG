module

public import CFSG.GroupTheory.GLnTwoSplitting.Extension
public import CFSG.GroupTheory.GLnTwoSplitting.Frame
public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (X : NatExt G E)

@[expose] def EqMod (e₀ : E) (a b : G) : Prop :=
  ∃ w ∈ (ZMod 2) ∙ e₀, b = a * X.ι w

@[expose] def IsCanonical {e₀ : E} {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0) (a : G) : Prop :=
  X.π a = LinearEquiv.transvection hψ ∧
    ∀ g, X.π g e₀ = e₀ → (∀ w, ψ (X.π g w) = ψ w) → X.EqMod e₀ a (g * a * g⁻¹)

variable {X}

theorem EqMod.refl (e₀ : E) (a : G) : X.EqMod e₀ a a :=
  ⟨0, zero_mem _, by rw [X.ι_zero, mul_one]⟩

theorem apply_eq_of_mem_span {e₀ y : E} {σ : E ≃ₗ[ZMod 2] E} (hσ : σ e₀ = e₀)
    (hy : y ∈ (ZMod 2) ∙ e₀) : σ y = y := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hy
  rw [map_smul, hσ]

theorem EqMod.conj_mul {e₀ : E} {a g h : G} (hg : X.π g e₀ = e₀)
    (hga : X.EqMod e₀ a (g * a * g⁻¹)) (hha : X.EqMod e₀ a (h * a * h⁻¹)) :
    X.EqMod e₀ a (g * h * a * (g * h)⁻¹) := by
  obtain ⟨w, hw, hgw⟩ := hga
  obtain ⟨w', hw', hhw'⟩ := hha
  refine ⟨w + X.π g w', add_mem hw (by rw [apply_eq_of_mem_span hg hw']; exact hw'), ?_⟩
  calc g * h * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
    _ = g * a * g⁻¹ * (g * X.ι w' * g⁻¹) := by rw [hhw']; group
    _ = _ := by rw [hgw, X.conj, mul_assoc, ← X.ι_add]

theorem ι_conj_of_lift {e₀ : E} {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0) {a : G}
    (ha : X.π a = LinearEquiv.transvection hψ) (v : E) :
    X.ι v * a * (X.ι v)⁻¹ = a * X.ι (ψ v • e₀) := by
  have h1 : X.ι v * a * (X.ι v)⁻¹ = a * (a⁻¹ * X.ι v * a) * X.ι v := by
    rw [X.ι_inv]
    group
  rw [h1, X.conj_ι', ha,
    show (LinearEquiv.transvection hψ).symm = LinearEquiv.transvection hψ from
      transvection_inv hψ, mul_assoc, ← X.ι_add, transvection_apply, add_comm v, add_assoc,
    two_add_self, add_zero]

theorem eqMod_ι_conj {e₀ : E} {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0) {a : G}
    (ha : X.π a = LinearEquiv.transvection hψ) (v : E) :
    X.EqMod e₀ a (X.ι v * a * (X.ι v)⁻¹) :=
  ⟨ψ v • e₀, smul_mem _ _ (mem_span_singleton_self e₀), X.ι_conj_of_lift hψ ha v⟩

theorem conj_transvection_eq {e₀ : E} {ψ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0)
    {σ : E ≃ₗ[ZMod 2] E} (h₀ : σ e₀ = e₀) (h₁ : ∀ w, ψ (σ w) = ψ w) :
    σ * LinearEquiv.transvection hψ * σ⁻¹ = LinearEquiv.transvection hψ := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply, transvection_apply,
    map_add, map_smul, h₀]
  change σ (σ.symm w) + ψ (σ.symm w) • e₀ = _
  rw [LinearEquiv.apply_symm_apply, ← h₁ (σ.symm w), LinearEquiv.apply_symm_apply]

theorem conj_eqMod_of_centre [FiniteDimensional (ZMod 2) E] (hE : 4 ≤ finrank (ZMod 2) E)
    {e₀ : E} {ψ χ : Dual (ZMod 2) E} (hψ : ψ e₀ = 0) (hχ : χ e₀ = 0) {a b : G}
    (ha : X.π a = LinearEquiv.transvection hψ) (hb : X.π b = LinearEquiv.transvection hχ) :
    X.EqMod e₀ a (b * a * b⁻¹) := by
  obtain ⟨w₁, hw₁, ha₁⟩ := X.sq_mem_of_π_eq_transvection hE hψ ha
  obtain ⟨w₂, hw₂, hb₂⟩ := X.sq_mem_of_π_eq_transvection hE hχ hb
  have hχψ : (χ + ψ) e₀ = 0 := by rw [LinearMap.add_apply, hχ, hψ, add_zero]
  obtain ⟨w₃, hw₃, hba₃⟩ := X.sq_mem_of_π_eq_transvection hE hχψ (g := b * a)
    (by rw [map_mul, ha, hb, transvection_mul_transvection_right])
  have hae₀ : X.π a e₀ = e₀ := by rw [ha, transvection_apply, hψ, zero_smul, add_zero]
  have hcomm : X.ι w₃ * a = a * X.ι w₃ := by
    rw [X.ι_mul, show (X.π a).symm w₃ = w₃ from ?_]
    rw [LinearEquiv.symm_apply_eq, apply_eq_of_mem_span hae₀ hw₃]
  refine ⟨w₃ + w₁ + w₂, add_mem (add_mem hw₃ hw₁) hw₂, ?_⟩
  have hainv : a⁻¹ = a * X.ι w₁ := by
    rw [← X.ι_inv, ← ha₁]
    group
  calc b * a * b⁻¹ = (b * a * (b * a)) * a⁻¹ * (b * b)⁻¹ := by group
    _ = X.ι w₃ * (a * X.ι w₁) * X.ι w₂ := by rw [hba₃, hainv, hb₂, X.ι_inv]
    _ = a * X.ι (w₃ + w₁ + w₂) := by
        rw [← mul_assoc, hcomm, X.ι_add, X.ι_add]
        group

section Frame

variable [FiniteDimensional (ZMod 2) E] (F : Frame E)

theorem exists_levi_involution (hE : 6 ≤ finrank (ZMod 2) E) :
    ∃ a, X.π a = LinearEquiv.transvection F.ψ_e₀ ∧ a * a = 1 ∧
      ∀ g, X.π g ∈ F.levi → X.EqMod F.e₀ a (g * a * g⁻¹) := by
  obtain ⟨a₀, ha₀, ha₀a₀⟩ := X.exists_involution_lift (by omega) F.ψ_e₀ F.ψ_ne_zero
  let L := F.levi.comap X.π
  let ρ : L →* (F.E' ≃ₗ[ZMod 2] F.E') := F.restrict.comp (X.π.subgroupComap F.levi)
  have hconj : ∀ l : L, ∃ z, F.ψ z = 0 ∧ (l : G) * a₀ * (l : G)⁻¹ = a₀ * X.ι z := by
    intro l
    have hl : X.π l ∈ F.levi := l.2
    obtain ⟨z, hz⟩ := X.exists_eq_mul_ι (g := a₀) (g' := (l : G) * a₀ * (l : G)⁻¹)
      (by rw [map_mul, map_mul, map_inv, ha₀,
        conj_transvection_eq F.ψ_e₀ hl.1 (F.levi_comp_ψ hl)])
    refine ⟨z, ?_, hz⟩
    rw [← X.mul_ι_sq_eq_one_iff F.ψ_e₀ F.e₀_ne_zero ha₀ ha₀a₀ z, ← hz]
    calc (l : G) * a₀ * (l : G)⁻¹ * ((l : G) * a₀ * (l : G)⁻¹)
        = (l : G) * (a₀ * a₀) * (l : G)⁻¹ := by group
      _ = 1 := by rw [ha₀a₀, mul_one, mul_inv_cancel]
  choose z hzψ hz using hconj
  let δ : L → F.E' := fun l => F.projE' (z l)
  have hzmul : ∀ l l' : L, z (l * l') = z l + X.π l (z l') := by
    intro l l'
    have h2 : ((l * l' : L) : G) * a₀ * ((l * l' : L) : G)⁻¹ =
        a₀ * X.ι (z l + X.π l (z l')) := by
      calc ((l * l' : L) : G) * a₀ * ((l * l' : L) : G)⁻¹
          = (l : G) * ((l' : G) * a₀ * (l' : G)⁻¹) * (l : G)⁻¹ := by
            rw [Subgroup.coe_mul]
            group
        _ = ((l : G) * a₀ * (l : G)⁻¹) * ((l : G) * X.ι (z l') * (l : G)⁻¹) := by
            rw [hz l']
            group
        _ = _ := by rw [hz l, X.conj, mul_assoc, ← X.ι_add]
    rw [hz (l * l')] at h2
    exact X.injective (mul_left_cancel h2)
  have hδ : ∀ l l', δ (l * l') = δ l + ρ l (δ l') := by
    intro l l'
    apply Subtype.ext
    change F.proj (z (l * l')) = F.proj (z l) + X.π l (F.proj (z l'))
    rw [hzmul, map_add, F.proj_levi_apply l.2]
  have hker : ∀ l, ρ l = 1 → δ l = 0 := by
    intro l hl
    have h1 : X.π l = 1 := congrArg Subtype.val ((F.restrict_eq_one_iff _).1 hl)
    obtain ⟨v, hv⟩ := (X.ker_iff _).1 h1
    have h2 := hz l
    rw [← hv, X.ι_conj_of_lift F.ψ_e₀ ha₀] at h2
    have h3 : z l = F.ψ v • F.e₀ := (X.injective (mul_left_cancel h2)).symm
    apply Subtype.ext
    change F.proj (z l) = 0
    rw [h3, map_smul, F.proj_e₀, smul_zero]
  have hρ : ∀ (f : Dual (ZMod 2) F.E') (d : F.E') (h : f d = 0),
      ∃ l, ρ l = LinearEquiv.transvection h := by
    intro f d h
    obtain ⟨σ, hσ, -⟩ := F.restrict_extend h
    obtain ⟨g, hg⟩ := X.surjective σ
    refine ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact σ.2⟩, ?_⟩
    rw [← hσ]
    change F.restrict ⟨X.π g, _⟩ = F.restrict σ
    congr 1
    exact Subtype.ext hg
  obtain ⟨w', hw'⟩ := exists_eq_of_isCocycle (by have := F.finrank_E'; omega) ρ hρ δ hδ hker
  refine ⟨a₀ * X.ι w', by rw [map_mul, X.π_ι, mul_one, ha₀], ?_, ?_⟩
  · rw [X.mul_ι_sq_of_π_eq_transvection F.ψ_e₀ ha₀, ha₀a₀, one_mul, w'.2.1, zero_smul,
      X.ι_zero]
  · intro g hg
    let l : L := ⟨g, hg⟩
    have hδl : F.proj (z l) = X.π g w' + w' := congrArg Subtype.val (hw' l)
    refine ⟨z l + X.π g w' + w', F.mem_span_e₀ ?_ ?_, ?_⟩
    · rw [map_add, map_add, hzψ, F.levi_comp_ψ hg, w'.2.1, add_zero, add_zero]
    · rw [map_add, map_add, hδl, F.proj_levi_apply hg, F.proj_of_mem w'.2]
      calc X.π g w' + w' + X.π g w' + w' = (X.π g w' + X.π g w') + (w' + w') := by abel
        _ = 0 := by rw [two_add_self, two_add_self, add_zero]
    · calc g * (a₀ * X.ι w') * g⁻¹ = (g * a₀ * g⁻¹) * (g * X.ι w' * g⁻¹) := by group
        _ = a₀ * X.ι (z l + X.π g w') := by
          rw [show g * a₀ * g⁻¹ = (l : G) * a₀ * (l : G)⁻¹ from rfl, hz l, X.conj, mul_assoc,
            ← X.ι_add]
        _ = a₀ * X.ι w' * X.ι (z l + X.π g w' + w') := by
          rw [mul_assoc, ← X.ι_add]
          congr 2
          calc z l + X.π g w' = z l + X.π g w' + (w' + w') := by rw [two_add_self, add_zero]
            _ = _ := by abel

@[expose] def ColCoeff (a : G) {k : E} (hk : F.ψ k = 0) (c : ZMod 2) : Prop :=
  ∀ g, X.π g = LinearEquiv.transvection hk →
    ∃ y ∈ (ZMod 2) ∙ F.e₀, g * a * g⁻¹ = a * X.ι (c • k + y)

omit [FiniteDimensional (ZMod 2) E] in
theorem exists_colCoeff {a : G}
    (ha : X.π a = LinearEquiv.transvection F.ψ_e₀) (haa : a * a = 1)
    (hL : ∀ g, X.π g ∈ F.levi → X.EqMod F.e₀ a (g * a * g⁻¹)) {k : E} (hkE : k ∈ F.E')
    (hk0 : k ≠ 0) : ∃ c, X.ColCoeff F a hkE.1 c := by
  have hk : F.ψ k = 0 := hkE.1
  obtain ⟨g₀, hg₀⟩ := X.surjective (LinearEquiv.transvection hk)
  have hcol : LinearEquiv.transvection hk * LinearEquiv.transvection F.ψ_e₀ *
      (LinearEquiv.transvection hk)⁻¹ = LinearEquiv.transvection F.ψ_e₀ := by
    rw [transvection_commute hk F.ψ_e₀ F.ψ_e₀ hk, mul_inv_cancel_right]
  obtain ⟨z, hz⟩ := X.exists_eq_mul_ι (g := a) (g' := g₀ * a * g₀⁻¹)
    (by rw [map_mul, map_mul, map_inv, hg₀, ha, hcol])
  have hzψ : F.ψ z = 0 := by
    rw [← X.mul_ι_sq_eq_one_iff F.ψ_e₀ F.e₀_ne_zero ha haa z, ← hz]
    calc g₀ * a * g₀⁻¹ * (g₀ * a * g₀⁻¹) = g₀ * (a * a) * g₀⁻¹ := by group
      _ = 1 := by rw [haa, mul_one, mul_inv_cancel]
  have hg₀e₀ : X.π g₀ F.e₀ = F.e₀ := by rw [hg₀, transvection_apply, F.ψ_e₀, zero_smul, add_zero]
  obtain ⟨c, y, hy, hzc⟩ := F.exists_smul_add_of_forall hk hzψ fun χ hχe₀ hχu hχk => by
    obtain ⟨h, hh⟩ := X.surjective (LinearEquiv.transvection hχk)
    have hhL : X.π h ∈ F.levi := hh ▸ F.transvection_mem_levi hkE hχk hχe₀ hχu
    obtain ⟨y₁, hy₁, hy₁'⟩ := hL h hhL
    obtain ⟨v', hv'⟩ := X.exists_eq_mul_ι (g := g₀ * h) (g' := h * g₀)
      (by rw [map_mul, map_mul, hh, hg₀, transvection_commute hχk hk hχk hk])
    have he₀h : X.π h F.e₀ = F.e₀ := hhL.1
    have h1 : h * (g₀ * a * g₀⁻¹) * h⁻¹ = a * X.ι (y₁ + LinearEquiv.transvection hχk z) := by
      rw [hz, show h * (a * X.ι z) * h⁻¹ = h * a * h⁻¹ * (h * X.ι z * h⁻¹) by group, hy₁',
        X.conj, hh, mul_assoc, ← X.ι_add]
    have h2 : h * (g₀ * a * g₀⁻¹) * h⁻¹ = a * X.ι (z + (y₁ + F.ψ v' • F.e₀)) := by
      calc h * (g₀ * a * g₀⁻¹) * h⁻¹ = (h * g₀) * a * (h * g₀)⁻¹ := by group
        _ = g₀ * (h * (X.ι v' * a * (X.ι v')⁻¹) * h⁻¹) * g₀⁻¹ := by rw [hv']; group
        _ = g₀ * (h * a * h⁻¹ * (h * X.ι (F.ψ v' • F.e₀) * h⁻¹)) * g₀⁻¹ := by
            rw [X.ι_conj_of_lift F.ψ_e₀ ha]; group
        _ = g₀ * a * g₀⁻¹ * (g₀ * X.ι (y₁ + F.ψ v' • F.e₀) * g₀⁻¹) := by
            rw [hy₁', X.conj, map_smul, he₀h, X.ι_add]; group
        _ = _ := by
            rw [hz, X.conj, apply_eq_of_mem_span hg₀e₀
              (add_mem hy₁ (smul_mem _ _ (mem_span_singleton_self _))), mul_assoc, ← X.ι_add]
    have h3 := X.injective (mul_left_cancel (h1.symm.trans h2))
    rw [transvection_apply] at h3
    have h4 : χ z • k ∈ (ZMod 2) ∙ F.e₀ := by
      have : χ z • k = F.ψ v' • F.e₀ := by
        calc χ z • k = (y₁ + (z + χ z • k)) + (y₁ + z) := by
              calc χ z • k = χ z • k + (y₁ + y₁) + (z + z) := by
                    rw [two_add_self, two_add_self, add_zero, add_zero]
                _ = _ := by abel
          _ = (z + (y₁ + F.ψ v' • F.e₀)) + (y₁ + z) := by rw [h3]
          _ = F.ψ v' • F.e₀ + (y₁ + y₁) + (z + z) := by abel
          _ = _ := by rw [two_add_self, two_add_self, add_zero, add_zero]
      rw [this]
      exact smul_mem _ _ (mem_span_singleton_self _)
    by_contra hχz
    rw [zmod_two_eq_one_of_ne_zero hχz, one_smul] at h4
    exact F.notMem_span_e₀_of_mem_E' hkE hk0 h4
  refine ⟨c, fun g hg => ?_⟩
  obtain ⟨v, hv⟩ := X.exists_eq_mul_ι (g := g₀) (g' := g) (by rw [hg, hg₀])
  refine ⟨y + F.ψ v • F.e₀, add_mem hy (smul_mem _ _ (mem_span_singleton_self _)), ?_⟩
  calc g * a * g⁻¹ = g₀ * (X.ι v * a * (X.ι v)⁻¹) * g₀⁻¹ := by rw [hv]; group
    _ = g₀ * a * g₀⁻¹ * (g₀ * X.ι (F.ψ v • F.e₀) * g₀⁻¹) := by
        rw [X.ι_conj_of_lift F.ψ_e₀ ha]; group
    _ = _ := by
        rw [hz, X.conj, map_smul, hg₀e₀, mul_assoc, ← X.ι_add, hzc, add_assoc]

omit [FiniteDimensional (ZMod 2) E] in
theorem ColCoeff.unique {a : G} {k : E} (hkE : k ∈ F.E') (hk0 : k ≠ 0) {c c' : ZMod 2}
    (hc : X.ColCoeff F a hkE.1 c) (hc' : X.ColCoeff F a hkE.1 c') : c = c' := by
  obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection hkE.1)
  obtain ⟨y, hy, hgy⟩ := hc g hg
  obtain ⟨y', hy', hgy'⟩ := hc' g hg
  have h1 := X.injective (mul_left_cancel (hgy.symm.trans hgy'))
  by_contra hne
  have h2 : (c + c') • k = y + y' := by
    rw [add_smul, two_add_eq_iff.1 h1]
    calc c' • k + y' + y + c' • k = y + y' + (c' • k + c' • k) := by abel
      _ = _ := by rw [two_add_self, add_zero]
  have h3 : c + c' = 1 := zmod_two_eq_one_of_ne_zero fun h => hne
    ((two_add_eq_iff.1 h).trans (zero_add c'))
  rw [h3, one_smul] at h2
  exact F.notMem_span_e₀_of_mem_E' hkE hk0 (h2 ▸ add_mem hy hy')

omit [FiniteDimensional (ZMod 2) E] in
theorem ColCoeff.transport {a : G}
    (hL : ∀ g, X.π g ∈ F.levi → X.EqMod F.e₀ a (g * a * g⁻¹)) {σ : E ≃ₗ[ZMod 2] E}
    (hσ : σ ∈ F.levi) {k k' : E} (hk : F.ψ k = 0) (hk' : F.ψ k' = 0) (hσk : σ k = k')
    {c : ZMod 2} (hc : X.ColCoeff F a hk c) : X.ColCoeff F a hk' c := by
  intro g' hg'
  obtain ⟨h, hh⟩ := X.surjective σ
  have hhL : X.π h ∈ F.levi := hh ▸ hσ
  obtain ⟨y₁, hy₁, hy₁'⟩ := hL h hhL
  obtain ⟨y₀, hy₀, hy₀'⟩ := hL h⁻¹ (by rw [map_inv]; exact inv_mem hhL)
  rw [inv_inv] at hy₀'
  obtain ⟨y, hy, hgy⟩ := hc (h⁻¹ * g' * h)
    (by rw [map_mul, map_mul, map_inv, hh, hg', F.inv_mul_transvection_mul hσ hk hk' hσk])
  have hge₀ : X.π (h⁻¹ * g' * h) F.e₀ = F.e₀ := by
    rw [map_mul, map_mul, map_inv, hh, hg', F.inv_mul_transvection_mul hσ hk hk' hσk,
      transvection_apply, F.ψ_e₀, zero_smul, add_zero]
  have hσy : ∀ t ∈ (ZMod 2) ∙ F.e₀, σ t = t := fun t ht => apply_eq_of_mem_span hσ.1 ht
  refine ⟨y₁ + (y + y₀), add_mem hy₁ (add_mem hy hy₀), ?_⟩
  calc g' * a * g'⁻¹ = h * ((h⁻¹ * g' * h) * (h⁻¹ * a * h) * (h⁻¹ * g' * h)⁻¹) * h⁻¹ := by
        group
    _ = h * a * h⁻¹ * (h * X.ι (c • k + y + y₀) * h⁻¹) := by
        rw [hy₀', show (h⁻¹ * g' * h) * (a * X.ι y₀) * (h⁻¹ * g' * h)⁻¹ =
          (h⁻¹ * g' * h) * a * (h⁻¹ * g' * h)⁻¹ * ((h⁻¹ * g' * h) * X.ι y₀ * (h⁻¹ * g' * h)⁻¹)
          by group, hgy, X.conj, apply_eq_of_mem_span hge₀ hy₀, X.ι_add (c • k + y)]
        group
    _ = _ := by
        rw [hy₁', X.conj, hh, map_add, map_add, map_smul, hσk, hσy y hy, hσy y₀ hy₀, mul_assoc,
          ← X.ι_add]
        congr 2
        abel

theorem isCanonical_of_frame (hE : 4 ≤ finrank (ZMod 2) E) {a : G}
    (ha : X.π a = LinearEquiv.transvection F.ψ_e₀)
    (hcol : ∀ k (hk : F.ψ k = 0), k ∈ F.E' → ∀ g, X.π g = LinearEquiv.transvection hk →
      X.EqMod F.e₀ a (g * a * g⁻¹))
    (hlev : ∀ g, X.π g ∈ F.levi → X.EqMod F.e₀ a (g * a * g⁻¹)) :
    X.IsCanonical F.ψ_e₀ a := by
  refine ⟨ha, fun g hge₀ hgψ => ?_⟩
  obtain ⟨k, hk, χ, hχ, σ₂, hkE, hσ₂, hdec⟩ := F.exists_decomp hge₀ hgψ
  obtain ⟨gc, hgc⟩ := X.surjective (LinearEquiv.transvection hk)
  obtain ⟨gr, hgr⟩ := X.surjective (LinearEquiv.transvection hχ)
  obtain ⟨gL, hgL⟩ := X.surjective σ₂
  obtain ⟨v, hv⟩ := X.exists_eq_mul_ι (g := gc * gr * gL) (g' := g)
    (by rw [map_mul, map_mul, hgc, hgr, hgL, hdec])
  have hce₀ : X.π gc F.e₀ = F.e₀ := by
    rw [hgc, transvection_apply, F.ψ_e₀, zero_smul, add_zero]
  have hre₀ : X.π gr F.e₀ = F.e₀ := by
    rw [hgr, transvection_apply, hχ, zero_smul, add_zero]
  have hLe₀ : X.π gL F.e₀ = F.e₀ := hgL ▸ hσ₂.1
  have h1 := EqMod.conj_mul hce₀ (hcol k hk hkE gc hgc)
    (X.conj_eqMod_of_centre hE F.ψ_e₀ hχ ha hgr)
  have h2 := EqMod.conj_mul (by rw [map_mul, LinearEquiv.mul_apply, hre₀, hce₀]) h1
    (hlev gL (hgL ▸ hσ₂))
  have h3 := EqMod.conj_mul (by rw [map_mul, map_mul, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, hLe₀, hre₀, hce₀]) h2 (X.eqMod_ι_conj F.ψ_e₀ ha v)
  rwa [← hv] at h3

theorem exists_isCanonical_of_frame (hE : 6 ≤ finrank (ZMod 2) E) :
    ∃ a, X.IsCanonical F.ψ_e₀ a := by
  obtain ⟨a, ha, haa, hL⟩ := X.exists_levi_involution F hE
  obtain ⟨k₀, hk₀E, hk₀0⟩ := exists_ne_zero_mem_of_finrank_pos (U := F.E')
    (by have := F.finrank_E'; omega)
  obtain ⟨c, hc⟩ := X.exists_colCoeff F ha haa hL hk₀E hk₀0
  have hcall : ∀ k (hkE : k ∈ F.E'), k ≠ 0 → X.ColCoeff F a hkE.1 c := by
    intro k hkE hk0
    by_cases hkk : k = k₀
    · subst hkk
      exact hc
    have hnot : k₀ ∉ span (ZMod 2) {F.e₀, F.u, k₀ + k} := by
      intro hmem
      obtain ⟨α, z', hz', hz⟩ := mem_span_insert.1 hmem
      obtain ⟨β, γ, rfl⟩ := mem_span_pair.1 hz'
      have h1 := congrArg F.proj hz
      rw [map_add, map_add, map_smul, map_smul, map_smul, F.proj_e₀, F.proj_u,
        F.proj_of_mem hk₀E, F.proj_of_mem (add_mem hk₀E hkE), smul_zero, smul_zero, zero_add,
        zero_add] at h1
      rcases zmod_two_eq_zero_or_one γ with rfl | rfl
      · rw [zero_smul] at h1
        exact hk₀0 h1
      · rw [one_smul] at h1
        refine hk0 ?_
        calc k = (k₀ + k) + k₀ := by
              rw [add_comm k₀ k, add_assoc, two_add_self, add_zero]
          _ = 0 := by rw [← h1, two_add_self]
    obtain ⟨χ, hχ, hχk₀⟩ := exists_dual_eq_one_of_notMem hnot
    have hχe₀ : χ F.e₀ = 0 := hχ _ (subset_span (by simp))
    have hχu : χ F.u = 0 := hχ _ (subset_span (by simp))
    have hχs : χ (k₀ + k) = 0 := hχ _ (subset_span (by simp))
    have hσ := F.transvection_mem_levi (add_mem hk₀E hkE) hχs hχe₀ hχu
    refine ColCoeff.transport F hL hσ hk₀E.1 hkE.1 ?_ hc
    rw [transvection_apply, hχk₀, one_smul, ← add_assoc, two_add_self, zero_add]
  have hzero : ∀ {b : G}, X.π b = LinearEquiv.transvection F.ψ_e₀ →
      ∀ (hk : F.ψ 0 = 0) g, X.π g = LinearEquiv.transvection hk → X.EqMod F.e₀ b (g * b * g⁻¹) := by
    intro b hb hk g hg
    obtain ⟨v, rfl⟩ := (X.ker_iff g).1 (by rw [hg, transvection_eq_one])
    exact X.eqMod_ι_conj F.ψ_e₀ hb v
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · refine ⟨a, X.isCanonical_of_frame F (by omega) ha (fun k hk hkE g hg => ?_) hL⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact hzero ha hk g hg
    obtain ⟨y, hy, hgy⟩ := hcall k hkE hk0 g hg
    exact ⟨y, hy, by rw [hgy, zero_smul, zero_add]⟩
  · have ha' : X.π (a * X.ι F.u) = LinearEquiv.transvection F.ψ_e₀ := by
      rw [map_mul, X.π_ι, mul_one, ha]
    refine ⟨a * X.ι F.u, X.isCanonical_of_frame F (by omega) ha'
      (fun k hk hkE g hg => ?_) fun g hg => ?_⟩
    · by_cases hk0 : k = 0
      · subst hk0
        exact hzero ha' hk g hg
      obtain ⟨y, hy, hgy⟩ := hcall k hkE hk0 g hg
      refine ⟨y, hy, ?_⟩
      rw [show g * (a * X.ι F.u) * g⁻¹ = g * a * g⁻¹ * (g * X.ι F.u * g⁻¹) by group, hgy,
        X.conj, hg, transvection_apply, F.ψ_u, one_smul, mul_assoc, ← X.ι_add,
        mul_assoc, ← X.ι_add]
      congr 2
      calc k + y + (F.u + k) = F.u + y + (k + k) := by abel
        _ = _ := by rw [two_add_self, add_zero]
    · obtain ⟨y, hy, hgy⟩ := hL g hg
      refine ⟨y, hy, ?_⟩
      rw [show g * (a * X.ι F.u) * g⁻¹ = g * a * g⁻¹ * (g * X.ι F.u * g⁻¹) by group, hgy,
        X.conj, hg.2.1, mul_assoc, ← X.ι_add, mul_assoc, ← X.ι_add, add_comm]

end Frame

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
