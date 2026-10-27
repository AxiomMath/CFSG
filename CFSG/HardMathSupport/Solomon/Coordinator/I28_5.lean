module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Section
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Assembly

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

namespace i285_Setup

variable (S : i285_Setup M)

theorem isMcLaughlinGroup_H [Finite M] (h : McLaughlinTypes) {R : Submodule (ZMod 2) M}
    (hR : S.IsMin R) : UniquenessMaximal.IsMcLaughlinGroup ↥(S.H R) := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hG := h (↥R ⧸ S.Q.comap R.subtype) (S.ρ hR).range
    ⟨(S.ρ hR) '' (Subtype.val ⁻¹' S.T R), ?_, ?_, S.ρ_range hR⟩ (fun U hU => S.ρ_irred hR U hU)
  · exact i285_isMcLaughlinGroup_of_mulEquiv (MonoidHom.ofInjective (S.ρ_injective hR)) hG
  · obtain ⟨d, hd⟩ := S.T_nonempty hR
    exact ⟨_, ⟨⟨d, Subgroup.subset_closure hd⟩, hd, rfl⟩⟩
  · rintro _ ⟨⟨d, hdH⟩, hd, rfl⟩
    exact S.ρ_transvection hR hd

theorem decomp [Finite M] (h : McLaughlinTypes) :
    ∃ (r : ℕ) (W : Fin (r + 1) → Subgroup 𝔾), i285_Decomp S.X S.τ r W := by
  have : Finite (Submodule (ZMod 2) M) :=
    Finite.of_injective (fun T : Submodule (ZMod 2) M => (T : Set M)) SetLike.coe_injective
  obtain ⟨R₁, hR₁⟩ := S.exists_isMin
  obtain ⟨x₀, hx₀, hτ₀⟩ := S.exists_mem_T hR₁ S.τ_mem_D
  set R₀ := R₁.map ((x₀ : 𝔾) : M →ₗ[ZMod 2] M)
  have hR₀ : S.IsMin R₀ := S.isMin_map hR₁ hx₀
  let U : Set (Submodule (ZMod 2) M) := {R | ∃ x ∈ S.X, R = R₀.map ((x : 𝔾) : M →ₗ[ZMod 2] M)}
  have hR₀U : R₀ ∈ U := ⟨1, S.X.one_mem, (i285_map_one R₀).symm⟩
  obtain ⟨r, f, hf0, hfinj, hfrange⟩ := i285_exists_enum (Set.toFinite U) hR₀U
  have hfU : ∀ i, f i ∈ U := fun i => hfrange ▸ Set.mem_range_self i
  have hUf : ∀ x ∈ S.X, ∃ i, f i = R₀.map ((x : 𝔾) : M →ₗ[ZMod 2] M) := fun x hx => by
    have : R₀.map ((x : 𝔾) : M →ₗ[ZMod 2] M) ∈ Set.range f := hfrange ▸ ⟨x, hx, rfl⟩
    exact this
  have hmin : ∀ i, S.IsMin (f i) := fun i => by
    obtain ⟨x, hx, hxi⟩ := hfU i
    rw [hxi]
    exact S.isMin_map hR₀ hx
  have hne : ∀ i j, i ≠ j → f i ≠ f j := fun i j hij hfij => hij (hfinj hfij)
  have hPfix : ∀ w : 𝔾, (∀ i, w ∈ i285_fix (f i)) → w ∈ S.W → w = 1 := by
    intro w hw hwW
    have hP : S.P ≤ i285_fixSub w := by
      rw [← S.isMin_iSup_map hR₀]
      refine iSup_le fun x => ?_
      obtain ⟨i, hi⟩ := hUf x x.2
      rw [← hi]
      intro v hv
      exact i285_mem_fixSub.2 (hw i v hv)
    refine S.faithful hwW fun v hv => ?_
    rw [i285_mem_fixSub.1 (hP hv), sub_self]
    exact S.Q.zero_mem
  refine ⟨r, fun i => S.H (f i), ?_, fun i => S.H_le_X _, fun i j hij =>
    S.H_le_centralizer (hmin i) (hmin j) (hne i j hij), fun i => ?_, fun i => ?_,
    fun g hg i => ?_, ?_, fun i => S.isMcLaughlinGroup_H h (hmin i)⟩
  · apply le_antisymm (iSup_le fun i => S.H_le_W _)
    change S.W ≤ _
    rw [W, Subgroup.closure_le]
    intro d hd
    obtain ⟨x, hx, hdx⟩ := S.exists_mem_T hR₀ hd
    obtain ⟨i, hi⟩ := hUf x hx
    rw [← hi] at hdx
    exact (le_iSup (fun i => S.H (f i)) i) (Subgroup.subset_closure hdx)
  · rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    rw [Subgroup.mem_bot]
    refine hPfix w (fun k => ?_) (S.H_le_W _ hw1)
    by_cases hki : k = i
    · subst hki
      have : (⨆ j : {j // j ≠ k}, S.H (f j)) ≤ i285_fix (f k) :=
        iSup_le fun j => S.H_le_fix (hmin j) (hmin k) (hne j k j.2)
      exact this hw2
    · exact S.H_le_fix (hmin i) (hmin k) (hne i k (Ne.symm hki)) hw1
  · obtain ⟨x, hx, hxi⟩ := hfU i
    refine ⟨x⁻¹, S.X.inv_mem hx, ?_⟩
    rw [S.H_conj (S.X.inv_mem hx), inv_inv, hf0, ← hxi]
  · obtain ⟨x, hx, hxi⟩ := hfU i
    obtain ⟨j, hj⟩ := hUf (g⁻¹ * x) (S.X.mul_mem (S.X.inv_mem hg) hx)
    refine ⟨j, ?_⟩
    rw [S.H_conj hg, hxi, ← i285_map_mul, ← hj]
  · show S.τ ∈ S.H (f 0)
    rw [hf0]
    exact Subgroup.subset_closure hτ₀

end i285_Setup

theorem i285_linear (h : McLaughlinTypes) [Finite M] (X : Subgroup 𝔾) (τ : 𝔾) (hτX : τ ∈ X)
    (hτ : IsF2Transvection τ)
    (hO2 : ∀ K : Subgroup 𝔾, K ≤ X → (∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) →
      (∀ k ∈ K, k ^ 4 = 1) → K = ⊥) :
    ∃ (r : ℕ) (W : Fin (r + 1) → Subgroup 𝔾), i285_Decomp X τ r W := by
  obtain ⟨φ, a, hφa, hφ, ha, rfl⟩ := (isF2Transvection_iff τ).1 hτ
  exact (⟨X, φ, a, hφa, hφ, ha, hτX, hO2⟩ : i285_Setup M).decomp h

end Assembly

section Transfer

theorem i285_GLBConj_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G)
    (H : Subgroup G) :
    CFSG.Open.GLBConj (e g) (H.map e.toMonoidHom) =
      (CFSG.Open.GLBConj g H).map e.toMonoidHom := by
  unfold CFSG.Open.GLBConj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem i285_Decomp.map {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {X : Subgroup G}
    {τ : G} {r : ℕ} {W : Fin (r + 1) → Subgroup G} (hW : i285_Decomp X τ r W) :
    i285_Decomp (X.map e.toMonoidHom) (e τ) r (fun i => (W i).map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hW
  refine ⟨?_, fun i => Subgroup.map_mono (h2 i), ?_, fun i => ?_, fun i => ?_, ?_, ⟨τ, h7, rfl⟩,
    fun i => ?_⟩
  · rw [← Subgroup.map_iSup, h1, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨e g, ⟨g, hg, rfl⟩, by simp⟩
    · rintro ⟨g', ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g⁻¹ * τ * g, ⟨g, hg, rfl⟩, by simp⟩
  · intro i j hij
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (h3 i j hij hx) y hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · rw [← Subgroup.map_iSup, ← Subgroup.map_inf_eq _ _ _ e.injective, h4 i, Subgroup.map_bot]
  · obtain ⟨g, hg, hgi⟩ := h5 i
    exact ⟨e g, ⟨g, hg, rfl⟩, by rw [i285_GLBConj_map, hgi]⟩
  · rintro _ ⟨g, hg, rfl⟩ i
    obtain ⟨j, hj⟩ := h6 g hg i
    refine ⟨j, ?_⟩
    change CFSG.Open.GLBConj (e g) ((W i).map e.toMonoidHom) = (W j).map e.toMonoidHom
    rw [i285_GLBConj_map, hj]
  · exact i285_isMcLaughlinGroup_of_mulEquiv
      ((W i).equivMapOfInjective e.toMonoidHom e.injective).symm (h8 i)

theorem i285_map_map_symm {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (X : Subgroup G) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  ext x
  simp

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] def i285_Φ : MulAut V ≃* LinearMap.GeneralLinearGroup (ZMod 2) (Additive V) where
  toFun σ :=
    { val := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive σ.toMonoidHom)
      inv := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive σ.symm.toMonoidHom)
      val_inv := LinearMap.ext fun v => by
        change Additive.ofMul (σ (σ.symm (Additive.toMul v))) = v
        simp
      inv_val := LinearMap.ext fun v => by
        change Additive.ofMul (σ.symm (σ (Additive.toMul v))) = v
        simp }
  invFun g :=
    { toFun := fun v => Additive.toMul ((g : Additive V →ₗ[ZMod 2] Additive V) (Additive.ofMul v))
      invFun := fun v => Additive.toMul
        (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive V)) :
          Additive V →ₗ[ZMod 2] Additive V) (Additive.ofMul v))
      left_inv := fun v => by
        simp only [ofMul_toMul]
        rw [i285_inv_apply_apply]
        rfl
      right_inv := fun v => by
        simp only [ofMul_toMul]
        rw [i285_apply_inv_apply]
        rfl
      map_mul' := fun x y => by
        simp only [ofMul_mul, map_add, toMul_add] }
  left_inv σ := MulEquiv.ext fun v => rfl
  right_inv g := Units.ext (LinearMap.ext fun v => rfl)
  map_mul' σ τ := Units.ext (LinearMap.ext fun v => rfl)

theorem i285_isF2Transvection_Φ [Finite V] (hV : UniquenessMaximal.IsElemAbelianTwo V)
    {τ : MulAut V} (hτ : UniquenessMaximal.IsTransvection τ) :
    IsF2Transvection (i285_Φ τ) := by
  obtain ⟨hτ1, hcard⟩ := hτ
  refine ⟨fun h1 => hτ1 (i285_Φ.injective (h1.trans (map_one _).symm)), ?_⟩
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  let f : V →* V :=
    { toFun := fun v => τ v * v⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hclos : Subgroup.closure (Set.range fun v : V => τ v * v⁻¹) = f.range := by
    rw [← Subgroup.closure_eq f.range, MonoidHom.coe_range]
    rfl
  have hmem : ∀ x : Additive V, x ∈ commutatorSpace (i285_Φ τ) ↔ Additive.toMul x ∈ f.range := by
    intro x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨Additive.toMul w, ?_⟩
      change τ (Additive.toMul w) * (Additive.toMul w)⁻¹ =
        Additive.toMul (w + Additive.ofMul (τ (Additive.toMul w)))
      rw [toMul_add, toMul_ofMul, hinv, mul_comm]
    · rintro ⟨v, hv⟩
      refine ⟨Additive.ofMul v, ?_⟩
      change Additive.ofMul v + Additive.ofMul (τ (Additive.toMul (Additive.ofMul v))) = x
      have hfv : v * τ v = f v := by
        change v * τ v = τ v * v⁻¹
        rw [hinv, mul_comm]
      rw [toMul_ofMul, ← ofMul_mul, hfv, hv, ofMul_toMul]
  have hcardC : Nat.card ↥(commutatorSpace (i285_Φ τ)) =
      Nat.card ↥(Subgroup.closure (Set.range fun v : V => τ v * v⁻¹)) := by
    rw [hclos]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul hmem)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have h2 := hcardC.trans hcard
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h2
  exact Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)

theorem i285_hO2_Φ {X : Subgroup (MulAut V)} (hX : CFSG.Open.pCoreOf 2 X = ⊥)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive V)))
    (hKX : K ≤ X.map i285_Φ.toMonoidHom)
    (hn : ∀ x ∈ X.map i285_Φ.toMonoidHom, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (h4 : ∀ k ∈ K, k ^ 4 = 1) : K = ⊥ := by
  have hK0 := i285_eq_bot_of_pCoreOf hX (K := K.comap i285_Φ.toMonoidHom) ?_ ?_ ?_
  · rw [eq_bot_iff]
    intro k hk
    have hk' : i285_Φ.symm k ∈ K.comap i285_Φ.toMonoidHom := by
      simpa using hk
    rw [hK0, Subgroup.mem_bot] at hk'
    rw [Subgroup.mem_bot]
    simpa using congrArg i285_Φ hk'
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hKX hx
    have : y = x := i285_Φ.injective hyx
    rw [← this]
    exact hy
  · intro x hx k hk
    change i285_Φ (x * k * x⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hn _ ⟨x, hx, rfl⟩ _ hk
  · intro k hk
    apply i285_Φ.injective
    rw [map_pow, map_one]
    exact h4 _ hk

end Transfer

theorem input28_5_of_types (h : McLaughlinTypes) : UniquenessMaximal.Input28_5 := by
  intro V _ _ hV X hX τ hτX hτ
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    exact hV _
  obtain ⟨r, W', hW'⟩ := i285_linear h (X.map i285_Φ.toMonoidHom) (i285_Φ τ) ⟨τ, hτX, rfl⟩
    (i285_isF2Transvection_Φ hV hτ) (i285_hO2_Φ hX)
  refine ⟨r, fun i => (W' i).map i285_Φ.symm.toMonoidHom, ?_⟩
  have := hW'.map i285_Φ.symm
  rw [i285_map_map_symm, MulEquiv.symm_apply_apply] at this
  exact this

end CFSG.HardMathSupport.Solomon.Coordinator
