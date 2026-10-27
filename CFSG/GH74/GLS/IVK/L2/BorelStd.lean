module

public import CFSG.GH74.GLS.IVK.L2.Borel
public import CFSG.GH74.GLS.IVK.L2.BorelPGL
public import CFSG.GH74.GLS.IVK.L2.BorelField

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.PSL2Table CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups Pointwise

namespace L2Borel

section Std

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

@[expose] noncomputable def wt (t : F) : K := (toPSL e).symm (mk (unip t))

omit [Finite F] in
@[simp] theorem toPSL_wt (t : F) : toPSL e (wt e t) = mk (unip t) := by
  simp [wt]

omit [Finite F] in
theorem wt_injective (h2 : (2 : F) ≠ 0) : Function.Injective (wt e) := by
  intro s t h
  have := congrArg (toPSL e) h
  simp only [toPSL_wt] at this
  exact (mk_unip_eq_mk_unip_iff h2 s t).1 this

omit [Finite F] in
theorem wt_zero : wt e (0 : F) = 1 := by
  simp [wt, unip_zero]

omit [Finite F] in
theorem wt_add (s t : F) : wt e (s + t) = wt e s * wt e t := by
  apply (toPSL e).injective
  simp [unip_add]

@[expose] noncomputable def wtHom : Multiplicative F →* K where
  toFun t := wt e (Multiplicative.toAdd t)
  map_one' := wt_zero e
  map_mul' _ _ := wt_add e _ _

omit [Finite F] in
theorem orderOf_wt_dvd (h2 : (2 : F) ≠ 0) (b : F) : orderOf (wt e b) ∣ Nat.card F := by
  have hinj : Function.Injective (wtHom e) := fun s t h => by
    exact Multiplicative.toAdd.injective (wt_injective e h2 h)
  have h := orderOf_injective (wtHom e) hinj (Multiplicative.ofAdd b)
  have h' : orderOf (Multiplicative.ofAdd b) ∣ Nat.card (Multiplicative F) := orderOf_dvd_natCard _
  have h'' : orderOf (wt e b) = orderOf (Multiplicative.ofAdd b) := h
  rw [h'']
  exact h'

@[expose] def IsStd (W : Subgroup K) : Prop := ∀ k, k ∈ W ↔ toPSL e k ∈ unipotent F

variable {e} {W : Subgroup K}

omit [Finite F] in
theorem IsStd.wt_mem (h : IsStd e W) (t : F) : wt e t ∈ W :=
  (h _).2 (by rw [toPSL_wt]; exact mk_unip_mem_unipotent t)

omit [Finite F] in
theorem IsStd.exists_wt (h : IsStd e W) {k : K} (hk : k ∈ W) : ∃ t : F, k = wt e t := by
  obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).1 ((h k).1 hk)
  exact ⟨t, (toPSL e).injective (by rw [toPSL_wt]; exact ht)⟩

omit [Finite F] in
theorem psl2FieldAut_mk_unip (σ : F ≃+* F) (t : F) :
    psl2FieldAut F σ (mk (unip t)) = mk (unip (σ t)) := by
  have h : Matrix.SpecialLinearGroup.map σ.toRingHom (unip t) = unip (σ t) := by
    apply SL_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) =
    QuotientGroup.mk' (Subgroup.center _) (unip (σ t))
  rw [psl2RingEquiv_mk, h]

omit [Finite F] in
theorem fieldAutHom_wt (σ : F ≃+* F) (t : F) : fieldAutHom e σ (wt e t) = wt e (σ t) := by
  apply (toPSL e).injective
  rw [toPSL_fieldAutHom, toPSL_wt, toPSL_wt, psl2FieldAut_mk_unip]

omit [Finite F] in
theorem mem_stabilizer_iff_forall {α : MulAut K} :
    α ∈ MulAction.stabilizer (MulAut K) W ↔ ∀ k, α k ∈ W ↔ k ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h k
    have := SetLike.ext_iff.1 h (α k)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa using this.symm
  · intro h
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have := h (α⁻¹ • x)
    simpa using this.symm

omit [Finite F] in
theorem IsStd.fieldAutHom_mem (h : IsStd e W) (σ : F ≃+* F) {k : K} (hk : k ∈ W) :
    fieldAutHom e σ k ∈ W := by
  obtain ⟨t, rfl⟩ := h.exists_wt hk
  rw [fieldAutHom_wt]
  exact h.wt_mem _

omit [Finite F] in
theorem IsStd.fieldAutHom_mem_stabilizer (h : IsStd e W) (σ : F ≃+* F) :
    fieldAutHom e σ ∈ MulAction.stabilizer (MulAut K) W := by
  rw [mem_stabilizer_iff_forall]
  intro k
  refine ⟨fun hk => ?_, fun hk => h.fieldAutHom_mem σ hk⟩
  have := h.fieldAutHom_mem σ⁻¹ hk
  rw [map_inv] at this
  simpa using this

theorem exists_decomp (α : MulAut K) :
    ∃ (g : PGL2 F) (σ : F ≃+* F), α = innDiagHom e g * fieldAutHom e σ := by
  obtain ⟨x, hx⟩ := (semilinearEquivAut F).surjective ((MulAut.congr (toPSL e)) α)
  refine ⟨x.left, x.right, ?_⟩
  apply (MulAut.congr (toPSL e)).injective
  have h1 : (semilinearEquivAut F)
      (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) =
      (MulAut.congr (toPSL e)) α := by
    rw [SemidirectProduct.inl_left_mul_inr_right]
    exact hx
  rw [map_mul, semilinearEquivAut_inl, semilinearEquivAut_inr] at h1
  rw [map_mul, innDiagHom_apply', fieldAutHom_apply', MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  exact h1.symm

theorem exists_bor_decomp (h : IsStd e W) {α : MulAut K}
    (hα : α ∈ MulAction.stabilizer (MulAut K) W) :
    ∃ (a : Fˣ) (b : F) (σ : F ≃+* F), α = innDiagHom e (bor a b) * fieldAutHom e σ := by
  obtain ⟨g, σ, hασ⟩ := exists_decomp (e := e) α
  have hd : innDiagHom e g ∈ MulAction.stabilizer (MulAut K) W := by
    have : innDiagHom e g = α * (fieldAutHom e σ)⁻¹ := by rw [hασ]; group
    rw [this]
    exact mul_mem hα (inv_mem (h.fieldAutHom_mem_stabilizer σ))
  have h1 : innDiagHom e g (wt e 1) ∈ W :=
    (mem_stabilizer_iff_forall.1 hd _).2 (h.wt_mem 1)
  obtain ⟨s, hs⟩ := h.exists_wt h1
  have h3 := toPGL_toPSL_innDiagHom e g (wt e 1)
  rw [hs, toPSL_wt, toPSL_wt] at h3
  obtain ⟨a, b, hab⟩ := exists_eq_bor h3.symm
  exact ⟨a, b, σ, by rw [hασ, hab]⟩

theorem innDiagHom_bor_wt (a : Fˣ) (b t : F) :
    innDiagHom e (bor a b) (wt e t) = wt e ((a : F) * t) := by
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom, toPSL_wt, toPSL_wt, bor_conj_unip]

theorem action_wt (a : Fˣ) (b : F) (σ : F ≃+* F) (t : F) :
    (innDiagHom e (bor a b) * fieldAutHom e σ) (wt e t) = wt e ((a : F) * σ t) := by
  rw [MulAut.mul_apply, fieldAutHom_wt, innDiagHom_bor_wt]

theorem pow_action_wt (a : Fˣ) (b : F) (σ : F ≃+* F) (j : ℕ) (t : F) :
    ((innDiagHom e (bor a b) * fieldAutHom e σ) ^ j) (wt e t) =
      wt e ((fun x => (a : F) * σ x)^[j] t) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih => rw [pow_succ, MulAut.mul_apply, action_wt, ih, Function.iterate_succ_apply]

theorem trivial_action (h : IsStd e W) (h2 : (2 : F) ≠ 0) {α : MulAut K}
    (hα : α ∈ MulAction.stabilizer (MulAut K) W) (htriv : ∀ t, α (wt e t) = wt e t) :
    ∃ b : F, α = MulAut.conj (wt e b) := by
  obtain ⟨a, b, σ, hασ⟩ := exists_bor_decomp h hα
  have h1 : ∀ t, (a : F) * σ t = t := fun t => by
    apply wt_injective e h2
    rw [← action_wt (e := e) a b σ t, ← hασ]
    exact htriv t
  have ha : (a : F) = 1 := by simpa using h1 1
  have hσ : σ = 1 := RingEquiv.ext fun t => by simpa [ha] using h1 t
  refine ⟨b, ?_⟩
  have ha' : a = 1 := Units.ext ha
  rw [hασ, hσ, ha', map_one, mul_one, bor_one, ← toPSL_wt e b, innDiagHom_toPGL_toPSL]

theorem exists_generator {G : Type*} [Group G] {D : Subgroup G} (hD : IsCyclic D) :
    ∃ α ∈ D, D = Subgroup.zpowers α ∧ orderOf α = Nat.card D := by
  obtain ⟨g, hg⟩ := hD
  refine ⟨(g : G), g.2, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    · intro hx
      exact (Subgroup.zpowers_le (H := D)).2 g.2 hx
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg

theorem le_innDiagSub_of_cyclic (h : IsStd e W) (h2 : (2 : F) ≠ 0) {D : Subgroup (MulAut K)}
    (hD : D ≤ MulAction.stabilizer (MulAut K) W) (hcyc : IsCyclic D)
    (hDcard : Nat.card D = Nat.card F - 1) : D ≤ innDiagSub e := by
  obtain ⟨α, hαD, hDα, hord⟩ := exists_generator hcyc
  have hαstab := hD hαD
  obtain ⟨a, b, σ, hα⟩ := exists_bor_decomp h hαstab
  by_cases hσ : σ = 1
  · have : α ∈ innDiagSub e := by
      rw [hα, hσ, map_one, mul_one]
      exact ⟨_, rfl⟩
    rw [hDα]
    exact (Subgroup.zpowers_le).2 this
  · exfalso
    obtain ⟨m, hm0, hmlt, hmid⟩ := exists_iterate_eq_id σ hσ a.ne_zero
    have htriv : ∀ t, (α ^ m) (wt e t) = wt e t := fun t => by
      rw [hα, pow_action_wt, hmid]
    have hstab : α ^ m ∈ MulAction.stabilizer (MulAut K) W := pow_mem hαstab m
    obtain ⟨b', hb'⟩ := trivial_action h h2 hstab htriv
    have h1 : orderOf (α ^ m) ∣ Nat.card F := by
      rw [hb']
      exact (orderOf_map_dvd (MulAut.conj : K →* MulAut K) _).trans (orderOf_wt_dvd e h2 b')
    have h3 : orderOf (α ^ m) ∣ Nat.card F - 1 := by
      rw [← hDcard]
      exact Subgroup.orderOf_dvd_natCard D (pow_mem hαD m)
    have h4 : orderOf (α ^ m) ∣ Nat.gcd (Nat.card F) (Nat.card F - 1) := Nat.dvd_gcd h1 h3
    have h5 : Nat.gcd (Nat.card F) (Nat.card F - 1) = 1 := by
      obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by
        have := Nat.card_pos (α := F)
        omega⟩
      rw [hr]
      simp
    rw [h5] at h4
    have h6 : α ^ m = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
    have h7 := orderOf_dvd_of_pow_eq_one h6
    rw [hord, hDcard] at h7
    exact absurd (Nat.le_of_dvd hm0 h7) (by omega)

end Std

end L2Borel

end CFSG.GH74.GLS.IVK
