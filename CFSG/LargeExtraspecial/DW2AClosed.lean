module

public import CFSG.LargeExtraspecial.DW2AJanko

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

section Count

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixIn (T : Subgroup (V ≃ₗ[ZMod 2] V)) (W : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V where
  carrier := {w | w ∈ W ∧ ∀ t ∈ T, t w = w}
  add_mem' := fun {u v} hu hv => ⟨W.add_mem hu.1 hv.1, fun t ht => by
    rw [map_add, hu.2 t ht, hv.2 t ht]⟩
  zero_mem' := ⟨W.zero_mem, fun t _ => map_zero t⟩
  smul_mem' := fun c v hv => ⟨W.smul_mem c hv.1, fun t ht => by rw [map_smul, hv.2 t ht]⟩

theorem mem_fixIn {T : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {w : V} :
    w ∈ fixIn T W ↔ w ∈ W ∧ ∀ t ∈ T, t w = w :=
  Iff.rfl

theorem card_mul_card_fixIn_le [FiniteDimensional (ZMod 2) V] {T : Subgroup (V ≃ₗ[ZMod 2] V)}
    {W : Submodule (ZMod 2) V} {c : V} (hc : c ≠ 0)
    (hTW : ∀ t ∈ T, ∀ w ∈ W, t w - w ∈ ZMod 2 ∙ c)
    (hinj : ∀ t ∈ T, (∀ w ∈ W, t w = w) → t = 1) :
    Nat.card T * Nat.card (fixIn T W) ≤ Nat.card W := by
  classical
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hc
  have hcoef : ∀ t ∈ T, ∀ w ∈ W, t w - w = ψ (t w - w) • c := by
    intro t ht w hw
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hTW t ht w hw)
    rw [← hμ, map_smul, hψ, smul_eq_mul, mul_one]
  let φ : T → Module.Dual (ZMod 2) W := fun t =>
    ψ ∘ₗ (((t : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ W.subtype
  have hφ : ∀ (t : T) (w : W), φ t w = ψ ((t : V ≃ₗ[ZMod 2] V) w - w) := fun _ _ => rfl
  set Ψ : Submodule (ZMod 2) (Module.Dual (ZMod 2) W) := Submodule.span (ZMod 2) (Set.range φ)
  have : Finite (Module.Dual (ZMod 2) W) := Module.finite_of_finite (ZMod 2)
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have hinjφ : Function.Injective
      (fun t : T => (⟨φ t, Submodule.subset_span ⟨t, rfl⟩⟩ : Ψ)) := by
    intro s t hst
    have h1 : φ s = φ t := congrArg Subtype.val hst
    have h2 : ∀ w ∈ W, (s : V ≃ₗ[ZMod 2] V) w = (t : V ≃ₗ[ZMod 2] V) w := by
      intro w hw
      have e : ψ ((s : V ≃ₗ[ZMod 2] V) w - w) = ψ ((t : V ≃ₗ[ZMod 2] V) w - w) :=
        LinearMap.congr_fun h1 ⟨w, hw⟩
      have : (s : V ≃ₗ[ZMod 2] V) w - w = (t : V ≃ₗ[ZMod 2] V) w - w := by
        rw [hcoef s s.2 w hw, hcoef t t.2 w hw, e]
      exact sub_left_injective this
    have h3 : t⁻¹ * s = 1 := by
      apply Subtype.ext
      refine hinj _ (t⁻¹ * s).2 fun w hw => ?_
      change (t : V ≃ₗ[ZMod 2] V).symm ((s : V ≃ₗ[ZMod 2] V) w) = w
      rw [h2 w hw]
      exact LinearEquiv.symm_apply_apply _ _
    exact (inv_mul_eq_one.mp h3).symm
  have hcard1 : Nat.card T ≤ Nat.card Ψ := Nat.card_le_card_of_injective _ hinjφ
  have hco : ∀ w : W, w ∈ Ψ.dualCoannihilator ↔ (w : V) ∈ fixIn T W := by
    intro w
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h
      refine ⟨w.2, fun t ht => ?_⟩
      have h0 := h (φ ⟨t, ht⟩) (Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩)
      rw [hφ] at h0
      have e := hcoef t ht w w.2
      rw [h0, zero_smul, sub_eq_zero] at e
      exact e
    · intro h φ' hφ'
      induction hφ' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        rw [hφ, h.2 t t.2, sub_self, map_zero]
      | zero => rfl
      | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  have hcard2 : Nat.card Ψ.dualCoannihilator = Nat.card (fixIn T W) := by
    refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨((w : W) : V), (hco w).mp w.2⟩)
      ⟨fun a b h => ?_, fun v => ⟨⟨⟨v, v.2.1⟩, (hco ⟨v, v.2.1⟩).mpr v.2⟩, rfl⟩⟩)
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq Ψ
  have e1 : Nat.card Ψ = 2 ^ finrank (ZMod 2) Ψ := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have e2 : Nat.card Ψ.dualCoannihilator = 2 ^ finrank (ZMod 2) Ψ.dualCoannihilator := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have e3 : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← hcard2, e3, ← hdim, pow_add, ← e1, ← e2]
  exact Nat.mul_le_mul_right _ hcard1

end Count


variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] noncomputable def Abar (A : Subgroup G) (g : G) : Subgroup S.O :=
  ((conjSub A g ⊓ S.M).subgroupOf S.M).map S.ρ

theorem mem_Abar {A : Subgroup G} {g : G} {t : S.O} :
    t ∈ Abar S A g ↔ ∃ a, ∃ h : a ∈ conjSub A g ⊓ S.M, S.ρ ⟨a, h.2⟩ = t := by
  constructor
  · rintro ⟨⟨a, haM⟩, ha, rfl⟩
    exact ⟨a, ⟨mem_subgroupOf.mp ha |>.1, haM⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha.2⟩, mem_subgroupOf.mpr ha, rfl⟩

theorem Abar_le_Mbar (A : Subgroup G) (g : G) : Abar S A g ≤ S.Mbar := map_le_range _ _

section Closed

variable {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
  (hDQ : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → S.cl (h * S.z * h⁻¹) ∈ W)
  (hWs : ∀ v ∈ W, S.q v = 0) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG)
  (hxW : S.cl (g * S.z * g⁻¹) ∈ W) (hxz : g * S.z * g⁻¹ ≠ S.z)
include hW hDQ hWs hxQ hxW hxz

theorem card_Abar_mul :
    Nat.card (Abar S (S.clPre W) g) * Nat.card (S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g)) =
      Nat.card W := by
  set H := conjSub (S.clPre W) g ⊓ S.M
  have hHM : H ≤ S.M := inf_le_right
  set f : H →* S.O := S.ρ.comp (inclusion hHM)
  have hrange : f.range = Abar S (S.clPre W) g := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : f.ker = S.QG.subgroupOf H := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have h1 := card_ker_mul_card_range f
  rw [hrange, hker] at h1
  have hle : conjSub (S.clPre W) g ≤ S.M := conjSub_le_M_of_mem hW hWs hxQ hxW hxz
  have hQH : S.QG ⊓ H = S.clPre W ⊓ conjSub (S.clPre W) g := by
    ext b
    constructor
    · rintro ⟨hbQ, hb, -⟩
      exact ⟨mem_clPre_of_mem_conjSub hW hDQ hbQ hb, hb⟩
    · rintro ⟨hbA, hb⟩
      exact ⟨hbA.1, hb, hle hb⟩
  have hk : Nat.card (S.QG.subgroupOf H) = 2 * Nat.card (S.clSub (S.clPre W ⊓
      conjSub (S.clPre W) g)) := by
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hQH,
      ← S.card_clPre, S.clPre_clSub (inf_le_left.trans (S.clPre_le_QG W))
        ⟨S.z_mem_clPre W, z_mem_conjSub_of_mem hW hxQ hxW hxz⟩]
  have hH : Nat.card H = 2 * Nat.card W := by
    have e : H = conjSub (S.clPre W) g := inf_eq_left.mpr hle
    rw [e, conjSub, card_map_of_injective (MulAut.conj g).injective, S.card_clPre]
  rw [hk, hH] at h1
  have : Nat.card (S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g)) * Nat.card (Abar S (S.clPre W) g)
      = Nat.card W := by
    have h2 := h1
    rw [mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_left two_pos h2
  rw [mul_comm]
  exact this

theorem fix_iff_mem_clSub_inf {u : S.Qt} (hu : u ∈ W) :
    (∀ t ∈ Abar S (S.clPre W) g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) ↔
      u ∈ S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g) := by
  set C := S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g)
  set T := (Abar S (S.clPre W) g).map S.O.subtype
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := by
    rw [Ne, S.cl_eq_zero_iff hxQ, not_or]
    exact ⟨S.s12_conj_z_ne_one g, hxz⟩
  have hTW : ∀ t ∈ T, ∀ w ∈ W, t w - w ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨t, ht, rfl⟩ w hw
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    exact ρ_sub_mem_span hW hDQ hWs hxQ hxW hxz ha.1 hw
  have hinj : ∀ t ∈ T, (∀ w ∈ W, t w = w) → t = 1 := by
    rintro _ ⟨t, ht, rfl⟩ h
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    have := eq_one_of_fix_clSub hW hDQ hWs hxQ hxW hxz ha.1 h
    change ((S.ρ _ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1
    rw [this]
    rfl
  have hcount := card_mul_card_fixIn_le hx0 hTW hinj
  have hTcard : Nat.card T = Nat.card (Abar S (S.clPre W) g) :=
    card_map_of_injective S.O.subtype_injective
  rw [hTcard, ← card_Abar_mul hW hDQ hWs hxQ hxW hxz] at hcount
  have hCle : C ≤ fixIn T W := by
    intro v hv
    obtain ⟨c, hc, hcQ, rfl⟩ := S.mem_clSub_iff.mp hv
    refine ⟨hc.1.2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    change ((S.ρ ⟨a, ha.2⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) = S.cl c
    rw [S.ρ_cl _ hcQ]
    change S.cl (a * c * a⁻¹) = S.cl c
    have hcomm : a * c = c * a := by
      have h1 := mem_conjSub.mp ha.1
      have h2 := mem_conjSub.mp hc.2
      have hWW : W ≤ perp S W := fun w hw => mem_perp.mpr fun v hv => by
        rw [polar, hWs _ (W.add_mem hv hw), hWs v hv, hWs w hw]
        rfl
      have := commute_of_mem_clPre hWW h1 h2
      have := congrArg (fun y => g * y * g⁻¹) this
      simpa [mul_assoc] using this
    rw [hcomm, mul_inv_cancel_right]
  have hpos : 0 < Nat.card (Abar S (S.clPre W) g) := Nat.card_pos
  have hle2 : Nat.card (fixIn T W) ≤ Nat.card C := by
    have := hcount
    exact (Nat.mul_le_mul_left_iff hpos).mp this
  have heq : C = fixIn T W := by
    refine Submodule.eq_of_le_of_finrank_le hCle ?_
    rw [S.card_submodule, S.card_submodule] at hle2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle2
  constructor
  · intro h
    rw [heq]
    refine ⟨hu, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  · intro h t ht
    rw [heq] at h
    exact h.2 _ ⟨t, ht, rfl⟩

theorem exists_ρ_apply_eq_add {u : S.Qt} (hu : u ∈ W) (hu0 : u ≠ 0)
    (hux : u ≠ S.cl (g * S.z * g⁻¹)) :
    ∃ m : S.M, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + S.cl (g * S.z * g⁻¹) := by
  by_cases hC : u ∈ S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g)
  · obtain ⟨c, hc, hcQ, rfl⟩ := S.mem_clSub_iff.mp hC
    have hcQa : c ∈ S.Qa g := by
      have := mem_conjSub.mp hc.2
      rw [Setting.Qa_eq_map]
      exact ⟨g⁻¹ * c * g, this.1, by simp [mul_assoc]⟩
    obtain ⟨-, y, hy, hyc⟩ := S.conj_L0_of_mem_QG_inf_Qa hxQ hxz ⟨hcQ, hcQa⟩ ⟨hu0, hux⟩
    refine ⟨⟨y, S.L0_le_M g hy⟩, ?_⟩
    rw [S.ρ_cl _ hcQ]
    change S.cl (y * c * y⁻¹) = _
    rw [hyc, S.cl_mul hxQ hcQ, add_comm]
  · rw [← fix_iff_mem_clSub_inf hW hDQ hWs hxQ hxW hxz hu] at hC
    push Not at hC
    obtain ⟨t, ht, htu⟩ := hC
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    refine ⟨⟨a, ha.2⟩, ?_⟩
    have h1 := ρ_sub_mem_span hW hDQ hWs hxQ hxW hxz ha.1 hu
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h1
    rcases zmod2_cases μ with rfl | rfl
    · exfalso
      apply htu
      rw [zero_smul, eq_comm, sub_eq_zero] at hμ
      exact hμ
    · rw [one_smul] at hμ
      rw [hμ]
      abel

end Closed

variable (S) in
@[expose] noncomputable def spanD : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) {v | ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ S.cl (h * S.z * h⁻¹) = v}

omit [Finite G] in
theorem cl_conj_mem_spanD {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG) :
    S.cl (h * S.z * h⁻¹) ∈ spanD S :=
  Submodule.subset_span ⟨h, hQ, rfl⟩

theorem isMbarInvariant_spanD : IsMbarInvariant S (spanD S) := by
  intro m v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hQ, rfl⟩ := hx
    rw [S.ρ_cl m hQ, show (m : G) * (h * S.z * h⁻¹) * (m : G)⁻¹ =
      ((m : G) * h) * S.z * ((m : G) * h)⁻¹ by group]
    exact cl_conj_mem_spanD (by
      rw [show ((m : G) * h) * S.z * ((m : G) * h)⁻¹ = (m : G) * (h * S.z * h⁻¹) * (m : G)⁻¹ by
        group]
      exact S.conj_mem_QG m.2 hQ)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

section Trans

variable {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
  (hDQ : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → S.cl (h * S.z * h⁻¹) ∈ W)
  (hWs : ∀ v ∈ W, S.q v = 0)
include hW hDQ hWs

theorem cl_conj_add_mem {h h' : G} (hQ : h * S.z * h⁻¹ ∈ S.QG) (hQ' : h' * S.z * h'⁻¹ ∈ S.QG)
    (h0 : S.cl (h * S.z * h⁻¹) ≠ 0) (h0' : S.cl (h' * S.z * h'⁻¹) ≠ 0)
    (hne : S.cl (h' * S.z * h'⁻¹) ≠ S.cl (h * S.z * h⁻¹)) :
    ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧
      S.cl (k * S.z * k⁻¹) = S.cl (h * S.z * h⁻¹) + S.cl (h' * S.z * h'⁻¹) := by
  have hxz : h * S.z * h⁻¹ ≠ S.z := fun e => h0 (by rw [e, S.cl_z])
  obtain ⟨m, hm⟩ := exists_ρ_apply_eq_add hW hDQ hWs hQ (hDQ h hQ) hxz (hDQ h' hQ') h0' hne
  refine ⟨m * h', ?_, ?_⟩
  · rw [show (m : G) * h' * S.z * ((m : G) * h')⁻¹ = m * (h' * S.z * h'⁻¹) * (m : G)⁻¹ by group]
    exact S.conj_mem_QG m.2 hQ'
  · rw [show (m : G) * h' * S.z * ((m : G) * h')⁻¹ = m * (h' * S.z * h'⁻¹) * (m : G)⁻¹ by group,
      ← S.ρ_cl m hQ', hm, add_comm]

theorem exists_ρ_apply_eq_of_conj {h h' : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hQ' : h' * S.z * h'⁻¹ ∈ S.QG) (h0 : S.cl (h * S.z * h⁻¹) ≠ 0)
    (h0' : S.cl (h' * S.z * h'⁻¹) ≠ 0) :
    ∃ m : S.M, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) =
      S.cl (h' * S.z * h'⁻¹) := by
  by_cases heq : S.cl (h' * S.z * h'⁻¹) = S.cl (h * S.z * h⁻¹)
  · exact ⟨1, by rw [map_one, heq]; rfl⟩
  obtain ⟨k, hkQ, hk⟩ := cl_conj_add_mem hW hDQ hWs hQ hQ' h0 h0' heq
  have hk0 : S.cl (k * S.z * k⁻¹) ≠ 0 := by
    rw [hk]
    intro e
    apply heq
    have := congrArg (· + S.cl (h' * S.z * h'⁻¹)) e
    simp only [add_assoc, add_self_zmod2, add_zero, zero_add] at this
    exact this.symm
  have hkz : k * S.z * k⁻¹ ≠ S.z := fun e => hk0 (by rw [e, S.cl_z])
  have hne : S.cl (h * S.z * h⁻¹) ≠ S.cl (k * S.z * k⁻¹) := by
    rw [hk]
    intro e
    apply h0'
    have := congrArg (S.cl (h * S.z * h⁻¹) + ·) e
    simp only [← add_assoc, add_self_zmod2, zero_add] at this
    exact this.symm
  obtain ⟨m, hm⟩ := exists_ρ_apply_eq_add hW hDQ hWs hkQ (hDQ k hkQ) hkz (hDQ h hQ) h0 hne
  refine ⟨m, ?_⟩
  rw [hm, hk, ← add_assoc, add_self_zmod2, zero_add]

theorem exists_conj_of_mem_spanD {v : S.Qt} (hv : v ∈ spanD S) :
    v = 0 ∨ ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ S.cl (h * S.z * h⁻¹) = v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Or.inr hx
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨h, hQ, rfl⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨h', hQ', rfl⟩
    · rw [add_zero]
      exact Or.inr ⟨h, hQ, rfl⟩
    by_cases h0 : S.cl (h * S.z * h⁻¹) = 0
    · rw [h0, zero_add]
      exact Or.inr ⟨h', hQ', rfl⟩
    by_cases h0' : S.cl (h' * S.z * h'⁻¹) = 0
    · rw [h0', add_zero]
      exact Or.inr ⟨h, hQ, rfl⟩
    by_cases hne : S.cl (h' * S.z * h'⁻¹) = S.cl (h * S.z * h⁻¹)
    · rw [hne, add_self_zmod2]
      exact Or.inl rfl
    obtain ⟨k, hkQ, hk⟩ := cl_conj_add_mem hW hDQ hWs hQ hQ' h0 h0' hne
    exact Or.inr ⟨k, hkQ, hk⟩
  | smul a x _ hx =>
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul]
      exact Or.inl rfl
    · rwa [one_smul]

theorem eq_spanD_of_isMbarInvariant {U : Submodule (ZMod 2) S.Qt} (hU : IsMbarInvariant S U)
    (hUD : U ≤ spanD S) (hU0 : U ≠ ⊥) : U = spanD S := by
  refine le_antisymm hUD ?_
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain hu | ⟨h, hQ, rfl⟩ := exists_conj_of_mem_spanD hW hDQ hWs (hUD huU)
  · exact absurd hu hu0
  rw [spanD, Submodule.span_le]
  rintro _ ⟨h', hQ', rfl⟩
  by_cases h0' : S.cl (h' * S.z * h'⁻¹) = 0
  · rw [h0']
    exact zero_mem _
  obtain ⟨m, hm⟩ := exists_ρ_apply_eq_of_conj hW hDQ hWs hQ hQ' hu0 h0'
  rw [← hm]
  exact hU m _ huU

end Trans

end CFSG.LargeExtraspecial.DW
