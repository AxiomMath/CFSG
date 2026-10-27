module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Dick
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG L2Dick

section Pair

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem pair_le_normalizer (hf : Hyp89 p ρ K a) {k : Γ} (hk : k ∈ K) :
    Subgroup.closure ({a, k * a * k⁻¹} : Set Γ) ≤ normalizer (K : Set Γ) := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact hf.norm
  · exact (normalizer (K : Set Γ)).mul_mem
      ((normalizer (K : Set Γ)).mul_mem (le_normalizer hk) hf.norm)
      ((normalizer (K : Set Γ)).inv_mem (le_normalizer hk))

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem center_quot_trivial (hf : Hyp89 p ρ K a) {F₀ : Type} [Field F₀]
    (e0 : (↥K ⧸ center ↥K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) :
    ∀ z : ↥K ⧸ center ↥K, (∀ x, z * x = x * z) → z = 1 := by
  intro z hz
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hf.quasi.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ center ↥K)) with h | h
  · have : z ∈ Subgroup.center (↥K ⧸ center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [h] at this
    exact this
  · exfalso
    obtain ⟨a', b', hab⟩ := psl2_not_comm F₀
    apply hab
    have h1 : e0.symm a' ∈ Subgroup.center (↥K ⧸ center ↥K) := by rw [h]; trivial
    rw [Subgroup.mem_center_iff] at h1
    have := h1 (e0.symm b')
    apply e0.symm.injective
    rw [map_mul, map_mul]
    exact this.symm

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem pair_central {yh : Γ} (hyh : yh ∈ K) {c : Γ} (hc : c ∈ centralizer (K : Set Γ))
    {k : Γ} (hk : k ∈ K) {w : Γ} (hwC : w ∈ centralizer (K : Set Γ))
    (hw : w ∈ Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ)) :
    Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ) ≤ centralizer ({w} : Set Γ) := by
  have hcK : ∀ x ∈ K, x * c = c * x := fun x hx => (Subgroup.mem_centralizer_iff.mp hc x hx)
  have hwK : ∀ x ∈ K, x * w = w * x := fun x hx => (Subgroup.mem_centralizer_iff.mp hwC x hx)
  have hcN : c ∈ normalizer (K : Set Γ) := Subgroup.centralizer_le_normalizer (K : Set Γ) hc
  have hle : Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ) ≤ K ⊔ zpowers c := by
    rw [Subgroup.closure_le]
    have h1 : yh * c ∈ K ⊔ zpowers c :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hyh) (Subgroup.mem_sup_right (mem_zpowers c))
    have h2 : k * (yh * c) * k⁻¹ = (k * yh * k⁻¹) * c := by
      have : k * c * k⁻¹ = c := by rw [hcK k hk]; group
      calc k * (yh * c) * k⁻¹ = k * yh * (k⁻¹ * k) * c * k⁻¹ := by group
        _ = k * yh * k⁻¹ * (k * c * k⁻¹) := by group
        _ = (k * yh * k⁻¹) * c := by rw [this]
    rintro _ (rfl | rfl)
    · exact h1
    · rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hk hyh) (Subgroup.inv_mem _ hk)))
        (Subgroup.mem_sup_right (mem_zpowers c))
  obtain ⟨i, κ, hκ, hwd⟩ := mem_sup_zpowers_decomp hcN (hle hw)
  have hwc : w * c = c * w := by
    have h1 : κ * c = c * κ := hcK κ hκ
    rw [hwd]
    calc c ^ i * κ * c = c ^ i * (κ * c) := by group
      _ = c ^ i * (c * κ) := by rw [h1]
      _ = c * (c ^ i * κ) := by
        rw [← mul_assoc, ← mul_assoc, (Commute.zpow_self c i).symm.eq]
  have hga : w * (yh * c) = (yh * c) * w := by
    calc w * (yh * c) = (w * yh) * c := by group
      _ = (yh * w) * c := by rw [← hwK yh hyh]
      _ = yh * (w * c) := by group
      _ = yh * (c * w) := by rw [hwc]
      _ = (yh * c) * w := by group
  have hgb : w * (k * (yh * c) * k⁻¹) = (k * (yh * c) * k⁻¹) * w := by
    have hk' : k⁻¹ ∈ K := Subgroup.inv_mem _ hk
    calc w * (k * (yh * c) * k⁻¹) = (w * k) * (yh * c) * k⁻¹ := by group
      _ = (k * w) * (yh * c) * k⁻¹ := by rw [← hwK k hk]
      _ = k * (w * (yh * c)) * k⁻¹ := by group
      _ = k * ((yh * c) * w) * k⁻¹ := by rw [hga]
      _ = k * (yh * c) * (w * k⁻¹) := by group
      _ = k * (yh * c) * (k⁻¹ * w) := by rw [hwK k⁻¹ hk']
      _ = (k * (yh * c) * k⁻¹) * w := by group
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hga.symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hgb.symm


theorem conj_inj_of_centerless {Y : Type} [Group Y] (hcen : ∀ z : Y, (∀ x, z * x = x * z) → z = 1) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [Subgroup.mem_bot]
  refine hcen z (fun x => ?_)
  have := DFunLike.congr_fun hz x
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  exact mul_inv_eq_iff_eq_mul.mp this

theorem exists_iota (hf : Hyp89 p ρ K a) {y : ↥K ⧸ center ↥K}
    (hy : bAutN K a hf.norm = MulAut.conj y)
    (hcen : ∀ z : ↥K ⧸ center ↥K, (∀ x, z * x = x * z) → z = 1) {k : Γ} (hk : k ∈ K) :
    ∃ ι : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) →* (↥K ⧸ center ↥K),
      ι ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = y ∧
      ι ⟨k * a * k⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ =
        (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ center ↥K) * y * (QuotientGroup.mk ⟨k, hk⟩)⁻¹ ∧
      ∀ w : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)),
        ι w = 1 ↔ (w : Γ) ∈ centralizer (K : Set Γ) := by
  classical
  have : Group.IsPerfect ↥K := hf.quasi.1
  have hinj := conj_inj_of_centerless hcen
  let φ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) →* MulAut (↥K ⧸ center ↥K) :=
    (YCfg.yAct K).comp (Subgroup.inclusion (pair_le_normalizer hf hk))
  have hφ : ∀ w : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)),
      φ w = YCfg.yAct K ⟨(w : Γ), pair_le_normalizer hf hk w.2⟩ := fun w => rfl
  set a₀ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) :=
    ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ with ha₀
  set b₀ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) :=
    ⟨k * a * k⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    with hb₀
  have hφa : φ a₀ = MulAut.conj y := by
    rw [hφ]
    exact hy
  have hφb : φ b₀ = MulAut.conj ((QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ center ↥K) * y *
      (QuotientGroup.mk ⟨k, hk⟩)⁻¹) := by
    rw [hφ]
    have e1 : (⟨(b₀ : Γ), pair_le_normalizer hf hk b₀.2⟩ : ↥(normalizer (K : Set Γ))) =
        ⟨k, le_normalizer hk⟩ * ⟨a, hf.norm⟩ * ⟨k, le_normalizer hk⟩⁻¹ := rfl
    have hkact : YCfg.yAct K ⟨k, le_normalizer hk⟩ =
        MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ center ↥K) :=
      YCfg.yAct_of_mem K ⟨k, hk⟩
    rw [e1, map_mul, map_mul, map_inv, hkact]
    have : YCfg.yAct K ⟨a, hf.norm⟩ = MulAut.conj y := hy
    rw [this, map_mul, map_mul, map_inv]
  have hgen := closure_pair_generates a (k * a * k⁻¹)
  have hle : φ.range ≤
      (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · exact ⟨y, hφa.symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, hφb.symm⟩
  have hR : ∀ w : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)),
      φ w ∈ (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range :=
    fun w => hle ⟨w, rfl⟩
  let cY := MonoidHom.ofInjective hinj
  let ι : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) →* (↥K ⧸ center ↥K) :=
    cY.symm.toMonoidHom.comp (φ.codRestrict _ hR)
  have hιw : ∀ (w : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) (z : ↥K ⧸ center ↥K),
      φ w = MulAut.conj z → ι w = z := by
    intro w z hz
    show cY.symm ⟨φ w, hR w⟩ = z
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hz
  refine ⟨ι, hιw a₀ y hφa, hιw b₀ _ hφb, fun w => ?_⟩
  have h1 : ι w = 1 ↔ φ w = 1 := by
    show cY.symm ⟨φ w, hR w⟩ = 1 ↔ φ w = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, hφ]
  exact YCfg.yAct_eq_one_iff K ⟨(w : Γ), pair_le_normalizer hf hk w.2⟩

end Pair

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
