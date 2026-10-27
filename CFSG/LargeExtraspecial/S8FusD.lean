module

public import CFSG.LargeExtraspecial.S8FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_apply_eq_one_eq_zero {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {β : LinearMap.BilinForm (ZMod 2) U} (hnd : β.Nondegenerate) {c₁ c₂ : U} (h1 : c₁ ≠ 0)
    (h12 : c₁ ≠ c₂) : ∃ w, β c₁ w = 1 ∧ β c₂ w = 0 := by
  have h3 : c₁ + c₂ ≠ 0 := fun h => h12 (by
    have := eq_neg_of_add_eq_zero_left h
    rwa [vec_neg] at this)
  obtain ⟨w, hw1, hw2⟩ := exists_apply_eq_one_both hnd h1 h3
  refine ⟨w, hw1, ?_⟩
  rw [map_add, LinearMap.add_apply, hw1] at hw2
  have : β c₂ w = 1 + 1 := by
    calc β c₂ w = (1 + β c₂ w) + 1 := by
          rw [add_comm (1 : ZMod 2), add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      _ = 1 + 1 := by rw [hw2]
  rw [this]
  rfl

theorem center_eq_of_mul {N V : Type*} [Group N] [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {φ : N →* (V ≃ₗ[ZMod 2] V)}
    (hasch : ∀ n, φ n ≠ 1 → ∃ c : V, Q c = 1 ∧
      (∀ v, φ n v = v + polar Q v c • c) ∧ commSpace (φ n) = (ZMod 2) ∙ c)
    {n n₀ : N} {c c₀ : V} (hc : Q c = 1) (hcv : ∀ v, φ n v = v + polar Q v c • c)
    (hc₀ : Q c₀ = 1) (hc₀v : ∀ v, φ n₀ v = v + polar Q v c₀ • c₀) : c = c₀ := by
  by_contra hne
  have hc0 : c ≠ 0 := fun h0 => by rw [h0, map_zero] at hc; exact zero_ne_one hc
  have hc₀0 : c₀ ≠ 0 := fun h0 => by rw [h0, map_zero] at hc₀; exact zero_ne_one hc₀
  obtain ⟨w₁, hw11, hw12⟩ := exists_apply_eq_one_eq_zero hQ hc0 hne
  obtain ⟨w₂, hw21, hw22⟩ := exists_apply_eq_one_eq_zero hQ hc₀0 (Ne.symm hne)
  rw [polarBilin_apply_apply] at hw11 hw12 hw21 hw22
  have e1 : φ (n * n₀) w₁ - w₁ = c := by
    rw [map_mul, LinearEquiv.mul_apply, hc₀v, polar_comm Q w₁ c₀, hw12, zero_smul, add_zero,
      hcv, polar_comm Q w₁ c, hw11, one_smul]
    abel
  have e2 : φ (n * n₀) w₂ - w₂ = c₀ + polar Q c₀ c • c := by
    rw [map_mul, LinearEquiv.mul_apply, hc₀v, polar_comm Q w₂ c₀, hw21, one_smul, hcv,
      polar_add_left, polar_comm Q w₂ c, hw22, zero_add]
    abel
  have hn1 : φ (n * n₀) ≠ 1 := by
    intro h1
    rw [h1, LinearEquiv.coe_one, id_eq, sub_self] at e1
    exact hc0 e1.symm
  obtain ⟨c', -, -, hc's⟩ := hasch (n * n₀) hn1
  have hm1 : c ∈ (ZMod 2) ∙ c' := by rw [← hc's, ← e1]; exact sub_mem_commSpace _ _
  have hm2 : c₀ + polar Q c₀ c • c ∈ (ZMod 2) ∙ c' := by
    rw [← hc's, ← e2]; exact sub_mem_commSpace _ _
  have hm3 : c₀ ∈ (ZMod 2) ∙ c' := by
    have h4 := ((ZMod 2) ∙ c').sub_mem hm2 (((ZMod 2) ∙ c').smul_mem (polar Q c₀ c) hm1)
    rwa [add_sub_cancel_right] at h4
  obtain ⟨a₁, ha₁⟩ := Submodule.mem_span_singleton.mp hm1
  obtain ⟨a₂, ha₂⟩ := Submodule.mem_span_singleton.mp hm3
  rcases zmod2_eq_zero_or_eq_one a₁ with rfl | rfl
  · rw [zero_smul] at ha₁; exact hc0 ha₁.symm
  rcases zmod2_eq_zero_or_eq_one a₂ with rfl | rfl
  · rw [zero_smul] at ha₂; exact hc₀0 ha₂.symm
  rw [one_smul] at ha₁ ha₂
  exact hne (ha₁.symm.trans ha₂)

theorem exists_center_of_hom {N V : Type*} [Group N] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (φ : N →* (V ≃ₗ[ZMod 2] V))
    (hO : ∀ n, φ n ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hsq : ∀ n, φ n * φ n = 1)
    (hanis : ∀ n, ∀ c ∈ commSpace (φ n), Q c = 0 → c = 0) :
    ∃ c : V, (c = 0 ∨ ∃ n v, φ n v - v = c) ∧ ∀ n v, φ n v - v ∈ (ZMod 2) ∙ c := by
  have hasch : ∀ n, φ n ≠ 1 → ∃ c : V, Q c = 1 ∧
      (∀ v, φ n v = v + polar Q v c • c) ∧ commSpace (φ n) = (ZMod 2) ∙ c := by
    intro n hn
    obtain ⟨-, c, hc, hcv, hcs, -⟩ :=
      eq_transvection_of_anisotropic_commSpace hQ (hO n) (hsq n) hn (hanis n)
    exact ⟨c, hc, hcv, hcs⟩
  by_cases hex : ∀ n, φ n = 1
  · refine ⟨0, Or.inl rfl, fun n v => ?_⟩
    rw [hex n, LinearEquiv.coe_one, id_eq, sub_self]
    exact zero_mem _
  push Not at hex
  obtain ⟨n₀, hn₀⟩ := hex
  obtain ⟨c₀, hc₀, hc₀v, hc₀s⟩ := hasch n₀ hn₀
  have hc₀0 : c₀ ≠ 0 := fun h0 => by rw [h0, map_zero] at hc₀; exact zero_ne_one hc₀
  have huniq : ∀ n, ∀ c : V, Q c = 1 → (∀ v, φ n v = v + polar Q v c • c) → c = c₀ :=
    fun n c hc hcv => center_eq_of_mul hQ hasch hc hcv hc₀ hc₀v
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, φ n₀ v₀ - v₀ = c₀ := by
    have : c₀ ∈ commSpace (φ n₀) := by rw [hc₀s]; exact Submodule.mem_span_singleton_self _
    exact mem_commSpace.mp this
  refine ⟨c₀, Or.inr ⟨n₀, v₀, hv₀⟩, fun n v => ?_⟩
  by_cases hn1 : φ n = 1
  · rw [hn1, LinearEquiv.coe_one, id_eq, sub_self]
    exact zero_mem _
  · obtain ⟨c, hc, hcv, -⟩ := hasch n hn1
    rw [← huniq n c hc hcv, hcv, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

section Center

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)} (hQ : Q.polarBilin.Nondegenerate)
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
  (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
  (hNsq : ∀ x ∈ Nbar S g t, x * x ∈ zpowers t)
include H C ht1 hVQ hQ hsing hfus hN hNsq

theorem exists_center_of_fusion_beta {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n)
    (hV1W : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t)
    (hanis : ∀ d ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), d ∉ orbit S g t) :
    ∃ d₀ ∈ Vt S g t, ∀ n ∈ Nbar S g t, ∀ w ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (n : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ d₀ := by
  have hV1eq : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hmemV1 : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun v hv => by
    rw [hV1eq]; exact ⟨v, hv, rfl⟩
  have hWt := (commSpace_t_eq H C ht ht1 hVQ).2
  have hy : ∀ n ∈ Nbar S g t, x⁻¹ * n * x ∈ CMt S t := by
    intro n hn
    refine mem_CMt.mpr ⟨mul_mem (mul_mem (inv_mem hxM) (Rbar_le_Mbar (Nbar_le_Rbar hn))) hxM, ?_⟩
    have ht' : t = x⁻¹ * τ * x := by rw [hxτ]; group
    rw [ht']
    calc x⁻¹ * n * x * (x⁻¹ * τ * x) = x⁻¹ * (n * τ) * x := by group
      _ = x⁻¹ * (τ * n) * x := by rw [hcN n hn]
      _ = x⁻¹ * τ * x * (x⁻¹ * n * x) := by group
  obtain ⟨φ, hφ⟩ : ∃ φ : Nbar S g t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t), ∀ n v,
      ((φ n v : Vt S g t) : S.Qt) = ((x⁻¹ * n * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
    ⟨(resCV S g H.conj_mem t).comp
      { toFun := fun n => ⟨x⁻¹ * n * x, hy n n.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun n₁ n₂ => Subtype.ext (by simp [mul_assoc]) }, fun n v => rfl⟩
  have hφO : ∀ n, φ n ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro n
    have e : φ n = resCV S g H.conj_mem t ⟨_, hy n n.2⟩ :=
      LinearEquiv.ext fun v => Subtype.ext (hφ n v)
    rw [e]
    exact resCV_mem_orthogonalGroup H ht hsing hfus _
  have hφx : ∀ n v, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((φ n v : Vt S g t) : S.Qt) =
      (n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    intro n v
    rw [hφ]
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) = _
    rw [apply_inv_apply_O]
  have hφsq : ∀ n, φ n * φ n = 1 := by
    intro n
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [← map_mul]
    have h1 := hφx (n * n) v
    have hnn := hNsq n n.2
    have hxv : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S g t := hV1W (hmemV1 v v.2)
    have h2 : ((n * n : Nbar S g t) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      have htt := mul_self_of_mem_Lbar S H.conj_mem ht
      rcases eq_one_or_eq_of_mem_zpowers htt hnn with h0 | h0
      · change ((n * n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
        rw [h0]; rfl
      · change ((n * n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
        rw [h0]
        exact mem_fixSpace.mp (hWt ▸ hxv)
    rw [h2] at h1
    have := congrArg (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
    rwa [inv_apply_apply_O, inv_apply_apply_O] at this
  have hφanis : ∀ n, ∀ c ∈ commSpace (φ n), Q c = 0 → c = 0 := by
    intro n c hc hQc
    by_contra hc0
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hc
    have horb : ((φ n v - v : Vt S g t) : S.Qt) ∈ orbit S g t :=
      (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ((hsing _ hc0).mp hQc)
    have hd : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((φ n v - v : Vt S g t) : S.Qt) ∈
        Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [Submodule.coe_sub, map_sub, hφx]
      refine ⟨hN n n.2 _ (hV1W (hmemV1 v v.2)), sub_mem ?_ (hmemV1 v v.2)⟩
      exact apply_mem_commSpace_of_commute (hcN n n.2) (hmemV1 v v.2)
    refine hanis _ hd ?_
    obtain ⟨k, hk, hkv⟩ := exists_of_mem_orbit horb H.conj_mem
    obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem hxM (Rbar_le_Mbar hk))
    have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((φ n v - v : Vt S g t) : S.Qt) =
        S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) := by
      rw [hkv, ← ρ_cl_conj_z S k H.conj_mem, ← ρ_cl_conj_z S k' H.conj_mem, hk']
      rfl
    rw [e] at hd ⊢
    exact hfus k' hd.1
  obtain ⟨c₀, hc₀, hc₀n⟩ := exists_center_of_hom hQ φ hφO hφsq hφanis
  refine ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) c₀, ?_, fun n hn w hw => ?_⟩
  · rcases hc₀ with h0 | ⟨n₀, v₀, hv₀⟩
    · rw [h0, Submodule.coe_zero, map_zero]; exact zero_mem _
    · rw [← hv₀, Submodule.coe_sub, map_sub, hφx]
      exact hN n₀ n₀.2 _ (hV1W (hmemV1 v₀ v₀.2))
  · rw [hV1eq] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hc₀n ⟨n, hn⟩ ⟨v, hv⟩)
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    have h1 := congrArg (fun u : Vt S g t => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt)) ha
    simp only [Submodule.coe_smul, Submodule.coe_sub, map_smul, map_sub] at h1
    rw [h1, hφx]
    rfl

end Center

theorem exists_Abar_fix_of_fusion_beta (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {V₁ : Submodule (ZMod 2) S.Qt}
    (hV1W : V₁ ≤ Wt S g t) {d₀ : S.Qt} (hd₀ : d₀ ∈ Vt S g t)
    (hd : ∀ n ∈ Nbar S g t, ∀ w ∈ V₁, (n : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ d₀) :
    ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ ∀ α ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t, ∀ w ∈ V₁,
      (α : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  by_cases hd0 : d₀ = 0
  · refine ⟨1, by rw [map_one]; exact one_mem _, fun α hα w hw => ?_⟩
    have h1 := hd α hα.2 w hw
    rw [hd0, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  obtain ⟨k, hk, hdk⟩ : ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧
      d₀ ∉ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
    by_contra hcon
    push Not at hcon
    apply hd0
    set D : Vt S g t := ⟨d₀, hd₀⟩
    set f : Vt S g t →ₗ[ZMod 2] ZMod 2 := (beta H C ht ht1 hVQ).flip D with hf
    have hspan : Vt S g t ≤ (LinearMap.ker f).map (Vt S g t).subtype := by
      refine (Vt_eq_span_orbit H ht).le.trans ?_
      rw [Submodule.span_le]
      intro u hu
      obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hu H.conj_mem
      have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
      refine ⟨bV htk, ?_, rfl⟩
      change beta H C ht ht1 hVQ (bV htk) D = 0
      exact (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk D).mpr (hcon k hk)
    have hzero : D = 0 := (beta_nondegenerate H C ht ht1 hVQ).2 D fun v => by
      obtain ⟨v', hv', hvv'⟩ := hspan v.2
      have : v' = v := Subtype.ext hvv'
      rw [← this]
      exact hv'
    exact congrArg Subtype.val hzero
  refine ⟨k, hk, fun α hα w hw => ?_⟩
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have h1 := apply_sub_mem_clSub_of_mem_Wt (C.mul k) (cl_mem_Vt htk) (conj_mem_QG' S k.2
    H.conj_mem) (hV1W hw) hα.1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hd α hα.2 w hw)
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  · rw [one_smul] at hc
    exact absurd (hc ▸ h1) hdk

end CFSG.LargeExtraspecial.S8
