module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

structure Frame (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] where
  e₀ : E
  u : E
  ψ : Dual (ZMod 2) E
  π₀ : Dual (ZMod 2) E
  ψ_e₀ : ψ e₀ = 0
  ψ_u : ψ u = 1
  π₀_e₀ : π₀ e₀ = 1
  π₀_u : π₀ u = 0

namespace Frame

variable (F : Frame E)

@[expose] def E' : Submodule (ZMod 2) E :=
  LinearMap.ker F.ψ ⊓ LinearMap.ker F.π₀

theorem mem_E' {w : E} : w ∈ F.E' ↔ F.ψ w = 0 ∧ F.π₀ w = 0 :=
  Iff.rfl

@[expose] def proj : E →ₗ[ZMod 2] E :=
  LinearMap.id + F.π₀.smulRight F.e₀ + F.ψ.smulRight F.u

theorem proj_apply (w : E) : F.proj w = w + F.π₀ w • F.e₀ + F.ψ w • F.u :=
  rfl

theorem proj_mem (w : E) : F.proj w ∈ F.E' := by
  refine ⟨?_, ?_⟩
  · change F.ψ (F.proj w) = 0
    rw [proj_apply, map_add, map_add, map_smul, map_smul, F.ψ_e₀, F.ψ_u, smul_zero, add_zero,
      smul_eq_mul, mul_one, two_add_self]
  · change F.π₀ (F.proj w) = 0
    rw [proj_apply, map_add, map_add, map_smul, map_smul, F.π₀_e₀, F.π₀_u, smul_zero, add_zero,
      smul_eq_mul, mul_one, two_add_self]

theorem proj_of_mem {w : E} (hw : w ∈ F.E') : F.proj w = w := by
  rw [proj_apply, hw.1, hw.2, zero_smul, zero_smul, add_zero, add_zero]

theorem proj_e₀ : F.proj F.e₀ = 0 := by
  rw [proj_apply, F.π₀_e₀, F.ψ_e₀, one_smul, zero_smul, add_zero, two_add_self]

theorem proj_u : F.proj F.u = 0 := by
  rw [proj_apply, F.π₀_u, F.ψ_u, one_smul, zero_smul, add_zero, two_add_self]

theorem decomp (w : E) : w = F.π₀ w • F.e₀ + F.ψ w • F.u + F.proj w := by
  rw [proj_apply]
  calc w = w + (F.π₀ w • F.e₀ + F.π₀ w • F.e₀) + (F.ψ w • F.u + F.ψ w • F.u) := by
        rw [two_add_self, two_add_self, add_zero, add_zero]
    _ = _ := by abel

theorem ext_of_coord {w w' : E} (h₀ : F.π₀ w = F.π₀ w') (h₁ : F.ψ w = F.ψ w')
    (h₂ : F.proj w = F.proj w') : w = w' := by
  rw [F.decomp w, F.decomp w', h₀, h₁, h₂]

theorem mem_span_e₀ {w : E} (h₁ : F.ψ w = 0) (h₂ : F.proj w = 0) : w ∈ (ZMod 2) ∙ F.e₀ := by
  rw [F.decomp w, h₁, h₂, zero_smul, add_zero, add_zero]
  exact smul_mem _ _ (mem_span_singleton_self _)

theorem ψ_ne_zero : F.ψ ≠ 0 := fun h => by
  have := F.ψ_u
  rw [h, LinearMap.zero_apply] at this
  exact zero_ne_one this

theorem e₀_ne_zero : F.e₀ ≠ 0 := fun h => by
  have := F.π₀_e₀
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem notMem_span_e₀_of_mem_E' {k : E} (hk : k ∈ F.E') (hk0 : k ≠ 0) :
    k ∉ (ZMod 2) ∙ F.e₀ := by
  rw [mem_span_singleton_iff_two]
  rintro (h | h)
  · exact hk0 h
  · have h' : F.π₀ k = 0 := hk.2
    rw [h, F.π₀_e₀] at h'
    exact one_ne_zero h'

theorem E'_le_ker_ψ : F.E' ≤ LinearMap.ker F.ψ :=
  inf_le_left

theorem finrank_E' [FiniteDimensional (ZMod 2) E] :
    finrank (ZMod 2) E ≤ finrank (ZMod 2) F.E' + 2 :=
  finrank_ker_inf_ker_add_two_ge F.ψ F.π₀

@[expose] def projE' : E →ₗ[ZMod 2] F.E' :=
  LinearMap.codRestrict F.E' F.proj F.proj_mem

theorem coe_projE' (w : E) : (F.projE' w : E) = F.proj w :=
  rfl

theorem map_eq_of_mul_self {σ : E ≃ₗ[ZMod 2] E} (hσ : σ * σ = 1) {S : Submodule (ZMod 2) E}
    (h : ∀ w ∈ S, σ w ∈ S) : S.map (σ : E →ₗ[ZMod 2] E) = S := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => h w hw) fun w hw => ?_
  refine ⟨σ w, h w hw, ?_⟩
  change σ (σ w) = w
  rw [← LinearEquiv.mul_apply, hσ]
  rfl

@[expose] def levi : Subgroup (E ≃ₗ[ZMod 2] E) where
  carrier := {σ | σ F.e₀ = F.e₀ ∧ σ F.u = F.u ∧ F.E'.map (σ : E →ₗ[ZMod 2] E) = F.E'}
  mul_mem' := by
    rintro σ τ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨by rw [LinearEquiv.mul_apply, h1', h1], by rw [LinearEquiv.mul_apply, h2', h2], ?_⟩
    rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, h3', h3]
  one_mem' := ⟨rfl, rfl, Submodule.map_id _⟩
  inv_mem' := by
    rintro σ ⟨h1, h2, h3⟩
    refine ⟨(LinearEquiv.symm_apply_eq σ).2 h1.symm, (LinearEquiv.symm_apply_eq σ).2 h2.symm, ?_⟩
    have h4 : ∀ w ∈ F.E', σ.symm w ∈ F.E' := fun w hw => by
      rw [← h3] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => h4 w hw) fun w hw => ?_
    refine ⟨σ w, ?_, σ.symm_apply_apply w⟩
    rw [← h3]
    exact ⟨w, hw, rfl⟩

theorem mem_levi {σ : E ≃ₗ[ZMod 2] E} :
    σ ∈ F.levi ↔ σ F.e₀ = F.e₀ ∧ σ F.u = F.u ∧ F.E'.map (σ : E →ₗ[ZMod 2] E) = F.E' :=
  Iff.rfl

theorem levi_apply_mem {σ : E ≃ₗ[ZMod 2] E} (hσ : σ ∈ F.levi) {w : E} (hw : w ∈ F.E') :
    σ w ∈ F.E' := by
  rw [← hσ.2.2]
  exact ⟨w, hw, rfl⟩

theorem levi_apply (σ : E ≃ₗ[ZMod 2] E) (hσ : σ ∈ F.levi) (w : E) :
    σ w = F.π₀ w • F.e₀ + F.ψ w • F.u + σ (F.proj w) := by
  conv_lhs => rw [F.decomp w]
  rw [map_add, map_add, map_smul, map_smul, hσ.1, hσ.2.1]

theorem levi_comp_ψ {σ : E ≃ₗ[ZMod 2] E} (hσ : σ ∈ F.levi) (w : E) : F.ψ (σ w) = F.ψ w := by
  rw [F.levi_apply σ hσ, map_add, map_add, map_smul, map_smul, F.ψ_e₀, F.ψ_u,
    (F.levi_apply_mem hσ (F.proj_mem w)).1, smul_zero, zero_add, add_zero, smul_eq_mul, mul_one]

theorem levi_comp_π₀ {σ : E ≃ₗ[ZMod 2] E} (hσ : σ ∈ F.levi) (w : E) : F.π₀ (σ w) = F.π₀ w := by
  rw [F.levi_apply σ hσ, map_add, map_add, map_smul, map_smul, F.π₀_e₀, F.π₀_u,
    (F.levi_apply_mem hσ (F.proj_mem w)).2, smul_eq_mul, mul_one, smul_zero, add_zero, add_zero]

theorem proj_levi_apply {σ : E ≃ₗ[ZMod 2] E} (hσ : σ ∈ F.levi) (w : E) :
    F.proj (σ w) = σ (F.proj w) := by
  rw [F.levi_apply σ hσ, map_add, map_add, map_smul, map_smul, F.proj_e₀, F.proj_u,
    F.proj_of_mem (F.levi_apply_mem hσ (F.proj_mem w)), smul_zero, smul_zero, zero_add, zero_add]

@[expose] noncomputable def restrict : F.levi →* (F.E' ≃ₗ[ZMod 2] F.E') where
  toFun σ := (σ : E ≃ₗ[ZMod 2] E).ofSubmodules F.E' F.E' σ.2.2.2
  map_one' := by
    ext w
    rfl
  map_mul' σ τ := by
    ext w
    rfl

theorem coe_restrict_apply (σ : F.levi) (w : F.E') :
    (F.restrict σ w : E) = (σ : E ≃ₗ[ZMod 2] E) w :=
  rfl

theorem restrict_eq_one_iff (σ : F.levi) : F.restrict σ = 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  refine Subtype.ext (LinearEquiv.ext fun w => ?_)
  rw [F.levi_apply σ σ.2 w]
  have : (σ : E ≃ₗ[ZMod 2] E) (F.proj w) = F.proj w := by
    have := congrArg (fun φ : F.E' ≃ₗ[ZMod 2] F.E' => (φ ⟨F.proj w, F.proj_mem w⟩ : E)) h
    exact this
  rw [this, ← F.decomp w]
  rfl

theorem restrict_extend {f : Dual (ZMod 2) F.E'} {d : F.E'} (h : f d = 0) :
    ∃ σ : F.levi, F.restrict σ = LinearEquiv.transvection h ∧
      ∃ (h' : (f ∘ₗ F.projE') (d : E) = 0), (σ : E ≃ₗ[ZMod 2] E) = LinearEquiv.transvection h' := by
  have hd : F.projE' (d : E) = d := Subtype.ext (F.proj_of_mem d.2)
  have h' : (f ∘ₗ F.projE') (d : E) = 0 := by rw [LinearMap.comp_apply, hd, h]
  have hσ : LinearEquiv.transvection h' ∈ F.levi := by
    refine ⟨?_, ?_, map_eq_of_mul_self (transvection_mul_self h') fun w hw => ?_⟩
    · rw [transvection_apply, LinearMap.comp_apply,
        show F.projE' F.e₀ = 0 from Subtype.ext F.proj_e₀, map_zero, zero_smul, add_zero]
    · rw [transvection_apply, LinearMap.comp_apply,
        show F.projE' F.u = 0 from Subtype.ext F.proj_u, map_zero, zero_smul, add_zero]
    · rw [transvection_apply]
      exact add_mem hw (smul_mem _ _ d.2)
  refine ⟨⟨_, hσ⟩, ?_, h', rfl⟩
  ext w
  rw [coe_restrict_apply, transvection_apply, transvection_apply, LinearMap.comp_apply,
    show F.projE' (w : E) = w from Subtype.ext (F.proj_of_mem w.2)]
  rfl

theorem transvection_mem_levi {χ : Dual (ZMod 2) E} {k : E} (hk : k ∈ F.E')
    (hχk : χ k = 0) (hχe₀ : χ F.e₀ = 0) (hχu : χ F.u = 0) :
    LinearEquiv.transvection hχk ∈ F.levi := by
  refine ⟨?_, ?_, map_eq_of_mul_self (transvection_mul_self hχk) fun w hw => ?_⟩
  · rw [transvection_apply, hχe₀, zero_smul, add_zero]
  · rw [transvection_apply, hχu, zero_smul, add_zero]
  · rw [transvection_apply]
    exact add_mem hw (smul_mem _ _ hk)

theorem exists_smul_add_of_forall {k z : E} (hk : F.ψ k = 0) (hz : F.ψ z = 0)
    (h : ∀ χ : Dual (ZMod 2) E, χ F.e₀ = 0 → χ F.u = 0 → χ k = 0 → χ z = 0) :
    ∃ c : ZMod 2, ∃ y ∈ (ZMod 2) ∙ F.e₀, z = c • k + y := by
  have hmem : z ∈ span (ZMod 2) {F.e₀, F.u, k} := by
    by_contra hz'
    obtain ⟨χ, hχ, hχz⟩ := exists_dual_eq_one_of_notMem hz'
    rw [h χ (hχ _ (subset_span (by simp))) (hχ _ (subset_span (by simp)))
      (hχ _ (subset_span (by simp)))] at hχz
    exact zero_ne_one hχz
  obtain ⟨α, z', hz', rfl⟩ := mem_span_insert.1 hmem
  obtain ⟨β, c, rfl⟩ := mem_span_pair.1 hz'
  have hβ : β = 0 := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, F.ψ_e₀, F.ψ_u, hk, smul_zero,
      smul_zero, zero_add, add_zero, smul_eq_mul, mul_one] at hz
    exact hz
  refine ⟨c, α • F.e₀, smul_mem _ _ (mem_span_singleton_self _), ?_⟩
  rw [hβ, zero_smul, zero_add, add_comm]

theorem inv_mul_transvection_mul {σ : E ≃ₗ[ZMod 2] E} (hσ : σ ∈ F.levi) {k k' : E}
    (hk : F.ψ k = 0) (hk' : F.ψ k' = 0) (hσk : σ k = k') :
    σ⁻¹ * LinearEquiv.transvection hk' * σ = LinearEquiv.transvection hk := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply, transvection_apply,
    F.levi_comp_ψ hσ, ← hσk]
  change σ.symm (σ w + F.ψ w • σ k) = _
  rw [← map_smul, ← map_add, LinearEquiv.symm_apply_apply]

theorem exists_decomp [FiniteDimensional (ZMod 2) E] {σ : E ≃ₗ[ZMod 2] E} (h₀ : σ F.e₀ = F.e₀)
    (hψ : ∀ w, F.ψ (σ w) = F.ψ w) :
    ∃ (k : E) (hk : F.ψ k = 0) (χ : Dual (ZMod 2) E) (hχ : χ F.e₀ = 0) (σ₂ : E ≃ₗ[ZMod 2] E),
      k ∈ F.E' ∧ σ₂ ∈ F.levi ∧
        σ = LinearEquiv.transvection hk * LinearEquiv.transvection hχ * σ₂ := by
  set k := F.proj (σ F.u) with hkdef
  have hkE : k ∈ F.E' := F.proj_mem _
  have hk : F.ψ k = 0 := hkE.1
  set σ₁ := LinearEquiv.transvection hk * σ with hσ₁
  have hσ₁e₀ : σ₁ F.e₀ = F.e₀ := by
    rw [hσ₁, LinearEquiv.mul_apply, h₀, transvection_apply, F.ψ_e₀, zero_smul, add_zero]
  have hσ₁ψ : ∀ w, F.ψ (σ₁ w) = F.ψ w := fun w => by
    rw [hσ₁, LinearEquiv.mul_apply, transvection_apply, map_add, map_smul, hk, smul_zero,
      add_zero, hψ]
  have hσ₁u : σ₁ F.u = F.π₀ (σ F.u) • F.e₀ + F.u := by
    rw [hσ₁, LinearEquiv.mul_apply, transvection_apply, hψ, F.ψ_u, one_smul]
    conv_lhs => rw [F.decomp (σ F.u)]
    rw [hψ, F.ψ_u, one_smul, ← hkdef]
    calc F.π₀ (σ F.u) • F.e₀ + F.u + k + k = F.π₀ (σ F.u) • F.e₀ + F.u + (k + k) := by abel
      _ = _ := by rw [two_add_self, add_zero]
  set χ : Dual (ZMod 2) E := F.π₀ + F.π₀ ∘ₗ (σ₁.symm : E →ₗ[ZMod 2] E) with hχdef
  have hσ₁e₀' : σ₁.symm F.e₀ = F.e₀ := by
    rw [LinearEquiv.symm_apply_eq, hσ₁e₀]
  have hχ : χ F.e₀ = 0 := by
    rw [hχdef, LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hσ₁e₀', F.π₀_e₀]
    exact two_add_self _
  set σ₂ := LinearEquiv.transvection hχ * σ₁ with hσ₂
  have hσ₂π₀ : ∀ w, F.π₀ (σ₂ w) = F.π₀ w := fun w => by
    rw [hσ₂, LinearEquiv.mul_apply, transvection_apply, map_add, map_smul, F.π₀_e₀, smul_eq_mul,
      mul_one, hχdef, LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, ← add_assoc, two_add_self, zero_add]
  have hσ₂ψ : ∀ w, F.ψ (σ₂ w) = F.ψ w := fun w => by
    rw [hσ₂, LinearEquiv.mul_apply, transvection_apply, map_add, map_smul, F.ψ_e₀, smul_zero,
      add_zero, hσ₁ψ]
  have hσ₂e₀ : σ₂ F.e₀ = F.e₀ := by
    rw [hσ₂, LinearEquiv.mul_apply, hσ₁e₀, transvection_apply, hχ, zero_smul, add_zero]
  have hσ₂u : σ₂ F.u = F.u := by
    refine F.ext_of_coord (by rw [hσ₂π₀]) (by rw [hσ₂ψ]) ?_
    rw [hσ₂, LinearEquiv.mul_apply, transvection_apply, map_add, map_smul, F.proj_e₀, smul_zero,
      add_zero, hσ₁u, map_add, map_smul, F.proj_e₀, F.proj_u, smul_zero, add_zero]
  have hσ₂E : ∀ w ∈ F.E', σ₂ w ∈ F.E' := fun w hw =>
    ⟨show F.ψ (σ₂ w) = 0 by rw [hσ₂ψ]; exact hw.1,
      show F.π₀ (σ₂ w) = 0 by rw [hσ₂π₀]; exact hw.2⟩
  have hσ₂L : σ₂ ∈ F.levi := by
    refine ⟨hσ₂e₀, hσ₂u, ?_⟩
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.map_le_iff_le_comap.2 fun w hw => hσ₂E w hw) ?_
    exact LinearEquiv.finrank_map_eq σ₂ F.E'
  refine ⟨k, hk, χ, hχ, σ₂, hkE, hσ₂L, ?_⟩
  rw [hσ₂, hσ₁, ← mul_assoc, ← mul_assoc, mul_assoc (LinearEquiv.transvection hk),
    transvection_mul_self, mul_one, transvection_mul_self, one_mul]

end Frame

theorem exists_frame {e₀ : E} {ψ : Dual (ZMod 2) E} (he₀ : e₀ ≠ 0) (hψ : ψ ≠ 0)
    (hψe₀ : ψ e₀ = 0) : ∃ F : Frame E, F.e₀ = e₀ ∧ F.ψ = ψ := by
  obtain ⟨u, hu⟩ : ∃ u, ψ u ≠ 0 := by
    by_contra! h
    exact hψ (LinearMap.ext h)
  have hu1 := zmod_two_eq_one_of_ne_zero hu
  have he₀u : e₀ ∉ (ZMod 2) ∙ u := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact he₀ h
    · rw [h, hu1] at hψe₀
      exact one_ne_zero hψe₀
  obtain ⟨π₀, hπ₀, hπ₀e₀⟩ := exists_dual_eq_one_of_notMem he₀u
  exact ⟨⟨e₀, u, ψ, π₀, hψe₀, hu1, hπ₀e₀, hπ₀ u (mem_span_singleton_self u)⟩, rfl, rfl⟩

end CFSG.GroupTheory.GLnTwoSplitting
