module

public import CFSG.LargeExtraspecial.DW2AFull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] noncomputable def axisD (g : G) : Submodule (ZMod 2) S.Qt :=
  S.clSub (S.clPre (spanD S) ⊓ conjSub (S.clPre (spanD S)) g)

omit [Finite G] in
theorem axisD_le_spanD (g : G) : axisD S g ≤ spanD S := by
  have := S.clSub_mono (inf_le_left : S.clPre (spanD S) ⊓ conjSub (S.clPre (spanD S)) g ≤
    S.clPre (spanD S))
  rwa [S.clSub_clPre] at this

section Struct

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)
include hWs

omit hWs [Finite G] in
theorem hDQ_spanD : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG → S.cl (k * S.z * k⁻¹) ∈ spanD S :=
  fun _ hk => cl_conj_mem_spanD hk

omit hWs [Finite G] in
theorem cl_ne_zero_iff {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ≠ 0 ↔ g * S.z * g⁻¹ ≠ S.z := by
  rw [Ne, S.cl_eq_zero_iff hxQ, not_or]
  exact ⟨fun h => h.2, fun h => ⟨S.s12_conj_z_ne_one g, h⟩⟩

omit hWs in
theorem cl_mem_axisD_iff {g h : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) :
    S.cl (h * S.z * h⁻¹) ∈ axisD S g ↔ h * S.z * h⁻¹ ∈ S.Qa g := by
  have hW := isMbarInvariant_spanD (S := S)
  constructor
  · intro hc
    obtain ⟨y, hy, hyQ', hyx⟩ := S.mem_clSub_iff.mp hc
    have hyQa : y ∈ S.Qa g := by
      have := mem_conjSub.mp hy.2
      rw [Setting.Qa_eq_map]
      exact ⟨g⁻¹ * y * g, this.1, by simp [mul_assoc]⟩
    rcases (S.cl_eq_cl_iff hyQ' hyQ).mp hyx with e | e
    · rw [e]
      exact hyQa
    · rw [e]
      exact (S.Qa g).mul_mem hyQa (S.z_mem_Qa_of_mem_QG rfl hxQ hxz)
  · intro hQa
    have hyA : h * S.z * h⁻¹ ∈ S.clPre (spanD S) := ⟨hyQ, cl_conj_mem_spanD hyQ⟩
    exact S.cl_mem_clSub ⟨hyA, mem_conjSub_of_mem_Qa hW hDQ_spanD hQa hyA⟩ hyQ

omit hWs in
theorem cl_mem_axisD_comm {g h : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z) :
    S.cl (h * S.z * h⁻¹) ∈ axisD S g ↔ S.cl (g * S.z * g⁻¹) ∈ axisD S h := by
  rw [cl_mem_axisD_iff hxQ hxz hyQ, cl_mem_axisD_iff hyQ hyz hxQ]
  by_cases heq : g * S.z * g⁻¹ = h * S.z * h⁻¹
  · rw [S.Qa_eq_of_conj_eq heq, heq]
  · exact ⟨S.mem_Qa_symm (Ne.symm heq), S.mem_Qa_symm heq⟩

theorem axisD_eq_of_cl_eq {g h : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    (hcl : S.cl (g * S.z * g⁻¹) = S.cl (h * S.z * h⁻¹)) : axisD S g = axisD S h := by
  have hW := isMbarInvariant_spanD (S := S)
  have key : ∀ g h : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z →
      h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
      S.cl (g * S.z * g⁻¹) = S.cl (h * S.z * h⁻¹) → axisD S g ≤ axisD S h := by
    intro g h hxQ hxz hyQ hyz hcl v hv
    rcases exists_conj_of_mem_spanD hW hDQ_spanD hWs (axisD_le_spanD g hv) with
      rfl | ⟨k, hkQ, rfl⟩
    · exact zero_mem _
    by_cases hkz : k * S.z * k⁻¹ = S.z
    · rw [hkz, S.cl_z]
      exact zero_mem _
    have h1 := (cl_mem_axisD_comm hxQ hxz hkQ hkz).mp hv
    rw [hcl] at h1
    exact (cl_mem_axisD_comm hyQ hyz hkQ hkz).mpr h1
  exact le_antisymm (key g h hxQ hxz hyQ hyz hcl) (key h g hyQ hyz hxQ hxz hcl.symm)

omit hWs [Finite G] in
theorem cl_mem_axisD_self {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ∈ axisD S g :=
  S.cl_mem_clSub ⟨⟨hxQ, cl_conj_mem_spanD hxQ⟩, conj_mem_conjSub (S.z_mem_clPre _)⟩ hxQ

theorem mem_axisD_mul_iff {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (m : S.M) (v : S.Qt) :
    v ∈ axisD S ((m : G) * g) ↔ ((S.ρ m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ axisD S g := by
  have hW := isMbarInvariant_spanD (S := S)
  have hmx : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = m * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  have hmxQ : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG := by
    rw [hmx]
    exact S.conj_mem_QG m.2 hxQ
  have hmxz : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ≠ S.z := by
    rw [hmx]
    intro e
    apply hxz
    calc g * S.z * g⁻¹ = (m : G)⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * m := by group
      _ = (m : G)⁻¹ * S.z * m := by rw [e]
      _ = S.z := by simpa using S.s12_conj_z_of_mem_M (S.M.inv_mem m.2)
  by_cases hv : v ∈ spanD S
  · rcases exists_conj_of_mem_spanD hW hDQ_spanD hWs hv with rfl | ⟨k, hkQ, rfl⟩
    · simp only [map_zero, zero_mem]
    have hk' : ((m⁻¹ : S.M) : G) * (k * S.z * k⁻¹) * ((m⁻¹ : S.M) : G)⁻¹ =
        ((m : G)⁻¹ * k) * S.z * ((m : G)⁻¹ * k)⁻¹ := by
      simp only [InvMemClass.coe_inv]
      group
    have hk'Q : ((m : G)⁻¹ * k) * S.z * ((m : G)⁻¹ * k)⁻¹ ∈ S.QG := by
      rw [← hk']
      exact S.conj_mem_QG (m⁻¹ : S.M).2 hkQ
    by_cases hkz : k * S.z * k⁻¹ = S.z
    · rw [hkz, S.cl_z, map_zero]
      simp only [zero_mem]
    have hk'z : ((m : G)⁻¹ * k) * S.z * ((m : G)⁻¹ * k)⁻¹ ≠ S.z := by
      intro e
      apply hkz
      calc k * S.z * k⁻¹ = (m : G) * (((m : G)⁻¹ * k) * S.z * ((m : G)⁻¹ * k)⁻¹) * (m : G)⁻¹ := by
            group
        _ = (m : G) * S.z * (m : G)⁻¹ := by rw [e]
        _ = S.z := S.s12_conj_z_of_mem_M m.2
    rw [S.ρ_cl _ hkQ, hk', cl_mem_axisD_iff hmxQ hmxz hkQ, cl_mem_axisD_iff hxQ hxz hk'Q,
      S.s12_Qa_mul]
    constructor
    · rintro ⟨y, hy, hye⟩
      have : (m : G)⁻¹ * k * S.z * ((m : G)⁻¹ * k)⁻¹ = y := by
        rw [show (m : G)⁻¹ * k * S.z * ((m : G)⁻¹ * k)⁻¹ =
          (m : G)⁻¹ * (k * S.z * k⁻¹) * m by group, ← hye]
        simp [mul_assoc]
      rw [this]
      exact hy
    · intro hQa
      refine ⟨_, hQa, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · constructor
    · intro h
      exact absurd (axisD_le_spanD _ h) hv
    · intro h
      exfalso
      apply hv
      have := hW m _ (axisD_le_spanD g h)
      rwa [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
        at this

theorem finrank_axisD_eq {g h : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z) :
    finrank (ZMod 2) (axisD S g) = finrank (ZMod 2) (axisD S h) := by
  have hW := isMbarInvariant_spanD (S := S)
  obtain ⟨m, hm⟩ := exists_ρ_apply_eq_of_conj hW hDQ_spanD hWs hxQ hyQ
    ((cl_ne_zero_iff hxQ).mpr hxz) ((cl_ne_zero_iff hyQ).mpr hyz)
  have hmx : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = m * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  have hmxQ : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG := by
    rw [hmx]
    exact S.conj_mem_QG m.2 hxQ
  have hcl : S.cl (((m : G) * g) * S.z * ((m : G) * g)⁻¹) = S.cl (h * S.z * h⁻¹) := by
    rw [hmx, ← S.ρ_cl m hxQ, hm]
  have hmxz : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ≠ S.z := fun e => hyz (by
    have h1 := hcl
    rw [e, S.cl_z, eq_comm, S.cl_eq_zero_iff hyQ] at h1
    exact h1.resolve_left (S.s12_conj_z_ne_one h))
  rw [← axisD_eq_of_cl_eq hWs hmxQ hmxz hyQ hyz hcl]
  have hmap : axisD S ((m : G) * g) =
      (axisD S g).map (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    ext v
    rw [mem_axisD_mul_iff hWs hxQ hxz m v, Submodule.mem_map_equiv]
    rfl
  rw [hmap, LinearEquiv.finrank_map_eq]

theorem mem_fixIn_Abar_iff {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    {u : S.Qt} (hu : u ∈ spanD S) :
    u ∈ fixIn ((Abar S (S.clPre (spanD S)) h).map S.O.subtype) (spanD S) ↔ u ∈ axisD S h := by
  rw [mem_fixIn, axisD, ← fix_iff_mem_clSub_inf isMbarInvariant_spanD hDQ_spanD hWs hyQ
    (cl_conj_mem_spanD hyQ) hyz hu]
  constructor
  · rintro ⟨-, h1⟩ t ht
    exact h1 _ ⟨t, ht, rfl⟩
  · rintro h1
    refine ⟨hu, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact h1 t ht

theorem axisD_le_sup {g h : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    (hy : S.cl (h * S.z * h⁻¹) ∉ axisD S g) :
    axisD S g ≤ axisD S h ⊔ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  have hW := isMbarInvariant_spanD (S := S)
  set c := S.cl (g * S.z * g⁻¹) with hc
  set c' := S.cl (h * S.z * h⁻¹) with hc'
  intro s hs
  by_contra hsH
  have hcW : c ∈ spanD S := cl_conj_mem_spanD hxQ
  have hc'W : c' ∈ spanD S := cl_conj_mem_spanD hyQ
  have hsW : s ∈ spanD S := axisD_le_spanD g hs
  have hcC : c ∉ axisD S h := fun h1 => hy ((cl_mem_axisD_comm hxQ hxz hyQ hyz).mpr h1)
  have hsC : s ∉ axisD S h := fun h1 => hsH (Submodule.mem_sup_left h1)
  have hcsC : c + s ∉ axisD S h := fun h1 => hsH (by
    have : s = (c + s) + c := by rw [add_comm c s, add_assoc, add_self_zmod2, add_zero]
    rw [this]
    exact add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)))
  set T := (Abar S (S.clPre (spanD S)) h).map S.O.subtype
  have hc'0 : c' ≠ 0 := (cl_ne_zero_iff hyQ).mpr hyz
  have hTW' : ∀ t ∈ T, ∀ w ∈ spanD S, t w - w ∈ ZMod 2 ∙ c' := by
    rintro _ ⟨t, ht, rfl⟩ w hw
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    exact ρ_sub_mem_span hW hDQ_spanD hWs hyQ hc'W hyz ha.1 hw
  have hTW : ∀ t ∈ T, ∀ w ∈ spanD S, t w = w ∨ t w = w + c' := by
    intro t ht w hw
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hTW' t ht w hw)
    rcases zmod2_cases μ with rfl | rfl
    · left
      rw [zero_smul, eq_comm, sub_eq_zero] at hμ
      exact hμ
    · right
      rw [one_smul] at hμ
      rw [hμ]
      abel
  have hTc : ∀ t ∈ T, t c' = c' := by
    intro t ht
    rcases hTW t ht c' hc'W with h1 | h1
    · exact h1
    · exfalso
      rw [add_self_zmod2] at h1
      exact hc'0 ((LinearEquiv.map_eq_zero_iff t).mp h1)
  have hfix : ∀ {u : S.Qt}, u ∈ spanD S → u ∉ axisD S h → u ∉ fixIn T (spanD S) :=
    fun hu hu' h1 => hu' ((mem_fixIn_Abar_iff hWs hyQ hyz hu).mp h1)
  obtain ⟨t, ht, htc, hts⟩ := exists_fix_move hTc hTW hcW hsW (hfix hcW hcC) (hfix hsW hsC)
    (hfix (add_mem hcW hsW) hcsC)
  obtain ⟨τ, hτ, rfl⟩ := ht
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp hτ
  set m : S.M := ⟨a, ha.2⟩
  have hmx : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = m * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  have hmxQ : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG := by
    rw [hmx]
    exact S.conj_mem_QG m.2 hxQ
  have hcl : S.cl (((m : G) * g) * S.z * ((m : G) * g)⁻¹) = c := by
    rw [hmx, ← S.ρ_cl m hxQ]
    exact htc
  have hmxz : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ≠ S.z := fun e => hxz (by
    have h1 := hcl
    rw [e, S.cl_z, eq_comm, hc, S.cl_eq_zero_iff hxQ] at h1
    exact h1.resolve_left (S.s12_conj_z_ne_one g))
  have heq := axisD_eq_of_cl_eq hWs hmxQ hmxz hxQ hxz hcl
  have h1 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) s ∈ axisD S g := by
    rw [← heq, mem_axisD_mul_iff hWs hxQ hxz m, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
      ← map_mul, inv_mul_cancel, map_one]
    exact hs
  change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) s = s + c' at hts
  rw [hts] at h1
  apply hy
  have := sub_mem h1 hs
  rwa [add_sub_cancel_left] at this

omit hWs in
theorem not_perp_le_of_finrank_lt {W : Submodule (ZMod 2) S.Qt}
    (hlt : finrank (ZMod 2) W < S.width) : ¬ perp S W ≤ W := by
  intro hle
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width] at h2
  rw [perp] at h1
  omega

theorem axisD_ne_spanD (hlt : finrank (ZMod 2) (spanD S) < S.width) {g : G}
    (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z) : axisD S g ≠ spanD S := by
  intro heq
  have hW := isMbarInvariant_spanD (S := S)
  set A := S.clPre (spanD S)
  have hle : conjSub A g ≤ S.M := conjSub_le_M_of_mem hW hWs hxQ (cl_conj_mem_spanD hxQ) hxz
  have hQ : ∀ a ∈ conjSub A g, a ∈ S.QG := by
    intro a ha
    have h1 : S.ρ ⟨a, hle ha⟩ = 1 := by
      have := eq_one_of_fix_clSub hW hDQ_spanD hWs hxQ (cl_conj_mem_spanD hxQ) hxz ha
        fun w hw => by
          have h2 := (fix_iff_mem_clSub_inf hW hDQ_spanD hWs hxQ (cl_conj_mem_spanD hxQ) hxz
            hw).mpr (by rw [← axisD, heq]; exact hw)
          exact h2 _ (mem_Abar.mpr ⟨a, ⟨ha, hle ha⟩, rfl⟩)
      exact this
    exact (S.ρ_eq_one_iff _).mp h1
  have hsub : conjSub A g ≤ A := fun a ha =>
    mem_clPre_of_mem_conjSub hW hDQ_spanD (hQ a ha) ha
  have heqA : conjSub A g = A := by
    refine Subgroup.eq_of_le_of_card_ge hsub ?_
    rw [conjSub, card_map_of_injective (MulAut.conj g).injective]
  have hgN : g ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← heqA]
      exact conj_mem_conjSub ha
    · intro ha
      rw [← heqA] at ha
      simpa [mem_conjSub, mul_assoc] using ha
  have hgM := normalizer_clPre_le_M hW (not_perp_le_of_finrank_lt hlt) hgN
  exact hxz (S.s12_conj_z_of_mem_M hgM)

theorem exists_conj_of_mem_spanD_ne {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) :
    ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧ k * S.z * k⁻¹ ≠ S.z ∧ S.cl (k * S.z * k⁻¹) = c := by
  rcases exists_conj_of_mem_spanD isMbarInvariant_spanD hDQ_spanD hWs hc with h | ⟨k, hkQ, hk⟩
  · exact absurd h hc0
  · exact ⟨k, hkQ, fun e => hc0 (by rw [← hk, e, S.cl_z]), hk⟩

theorem finrank_axisD_le_one_or (hlt : finrank (ZMod 2) (spanD S) < S.width) {g : G}
    (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z) :
    finrank (ZMod 2) (axisD S g) ≤ 1 ∨
      finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g) + 1 := by
  classical
  let rep : S.Qt → G := fun c =>
    if h : c ∈ spanD S ∧ c ≠ 0 then (exists_conj_of_mem_spanD_ne hWs h.1 h.2).choose else 1
  have hrep : ∀ c ∈ spanD S, c ≠ 0 → rep c * S.z * (rep c)⁻¹ ∈ S.QG ∧
      rep c * S.z * (rep c)⁻¹ ≠ S.z ∧ S.cl (rep c * S.z * (rep c)⁻¹) = c := by
    intro c hc hc0
    have h : c ∈ spanD S ∧ c ≠ 0 := ⟨hc, hc0⟩
    simp only [rep, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
    exact (exists_conj_of_mem_spanD_ne hWs h.1 h.2).choose_spec
  refine finrank_le_one_or_add_one_ge (U := spanD S) (fun c => axisD S (rep c)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc hc0
    obtain ⟨h1, -, h3⟩ := hrep c hc hc0
    have := cl_mem_axisD_self h1
    rwa [h3] at this
  · intro c _ _
    exact axisD_le_spanD _
  · intro c hc hc0
    obtain ⟨h1, h2, -⟩ := hrep c hc hc0
    exact finrank_axisD_eq hWs h1 h2 hxQ hxz
  · intro c hc c' hc' hc0 hc'0
    obtain ⟨h1, h2, h3⟩ := hrep c hc hc0
    obtain ⟨h1', h2', h3'⟩ := hrep c' hc' hc'0
    have := cl_mem_axisD_comm h1 h2 h1' h2'
    rwa [h3, h3'] at this
  · intro c hc c' hc' hc0 hc'0 hnot
    obtain ⟨h1, h2, h3⟩ := hrep c hc hc0
    obtain ⟨h1', h2', h3'⟩ := hrep c' hc' hc'0
    have := axisD_le_sup hWs h1 h2 h1' h2' (by rwa [h3'])
    rwa [h3] at this
  · exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (axisD_le_spanD g) (axisD_ne_spanD hWs hlt hxQ hxz))

end Struct

end CFSG.LargeExtraspecial.DW
