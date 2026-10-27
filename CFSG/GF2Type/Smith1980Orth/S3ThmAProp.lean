module

public import CFSG.GF2Type.Smith1980Orth.S3Bad
import CFSG.GF2Type.Smith1980Orth.S3Good

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtProp (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

private theorem finrank_le_add_of_forall_sub_mem {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (c : V ≃ₗ[ZMod 2] V)
    (φ : V →ₗ[ZMod 2] ZMod 2) (Y : Submodule (ZMod 2) V) (hY : ∀ u, φ u = 0 → c u - u ∈ Y) :
    finrank (ZMod 2) V ≤ finrank (ZMod 2) (fixSpace c) + finrank (ZMod 2) Y + 1 := by
  let N : LinearMap.ker φ →ₗ[ZMod 2] V :=
    ((c : V →ₗ[ZMod 2] V) - 1) ∘ₗ (LinearMap.ker φ).subtype
  have hrange : LinearMap.range N ≤ Y := by
    rintro _ ⟨u, rfl⟩
    exact hY u u.2
  have hker : finrank (ZMod 2) (LinearMap.ker N) ≤ finrank (ZMod 2) (fixSpace c) := by
    have hle : (LinearMap.ker N).map (LinearMap.ker φ).subtype ≤ fixSpace c := by
      rintro _ ⟨u, hu, rfl⟩
      exact hu
    rw [← Submodule.finrank_map_subtype_eq]
    exact Submodule.finrank_mono hle
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : finrank (ZMod 2) (LinearMap.range φ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range φ)
  have h4 := Submodule.finrank_mono hrange
  omega

private theorem coord_sub_coord_zero (D : S2Data S) (a b : Vt S D.g D.t) :
    D.coord (a, 0) - D.coord (b, 0) = D.coord (a - b, 0) := by
  rw [← map_sub]
  exact congrArg D.coord (Prod.ext rfl (sub_self _))

private theorem coord_add_coord_add (D : S2Data S) (a b a' b' : Vt S D.g D.t) :
    D.coord (a, b) + D.coord (a', b') = D.coord (a + a', b + b') := by
  rw [← map_add]
  rfl

private theorem S2Data.cl_commutator_eq_coord (D : S2Data S) {x y : G} (hxM : x ∈ S.M)
    (hxC : S.ρ ⟨x, hxM⟩ ∈ D.Cbar) (hyQ : y ∈ S.QG) {u : Vt S D.g D.t}
    (hyc : S.cl y = D.coord (u, 0)) :
    S.cl (x * y * x⁻¹ * y⁻¹) = D.coord (D.resC ⟨_, hxC⟩ u - u, 0) := by
  have e1 : ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, 0)) =
      D.coord (D.resC ⟨_, hxC⟩ u, 0) := by
    have := D.Cbar_apply_coord ⟨S.ρ ⟨x, hxM⟩, hxC⟩ u 0
    rwa [map_zero] at this
  rw [S.cl_commutator hxM hyQ, hyc, e1, coord_sub_coord_zero]

private theorem commute_of_cl_mem_commSpace {x a : G} (hxM : x ∈ S.M) (hx2 : x ^ 2 = 1)
    (haQ : a ∈ S.QG) (hfix : S.fixQt x = S.clSub (S.QG ⊓ centralizer ({x} : Set G)))
    (ha : S.cl a ∈ commSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    x * a = a * x := by
  have h2 : S.cl a ∈ S.fixQt x := by
    rw [S.fixQt_of_mem hxM]
    exact commSpace_le_fixSpace (S.ρ_mul_self hxM hx2) ha
  rw [hfix] at h2
  obtain ⟨y, hy, hyQ, hyc⟩ := S.mem_clSub_iff.mp h2
  have hxy : y * x = x * y := mem_centralizer_singleton_iff.mp hy.2
  have hxz : x * S.z = S.z * x := S.z_comm hxM
  rcases (S.cl_eq_cl_iff hyQ haQ).mp hyc with e | e
  · rw [e]
    exact hxy.symm
  · rw [e]
    calc x * (y * S.z) = (x * y) * S.z := (mul_assoc _ _ _).symm
      _ = (y * x) * S.z := by rw [hxy]
      _ = y * (x * S.z) := mul_assoc _ _ _
      _ = y * (S.z * x) := by rw [hxz]
      _ = y * S.z * x := (mul_assoc _ _ _).symm

private theorem not_mem_Qa_of_bad {k h : G} (hbad : Bad S k) (haQ : h * S.z * h⁻¹ ∈ S.QG) :
    k * S.z * k⁻¹ ∉ S.Qa h := by
  intro hxa
  have hax : h * S.z * h⁻¹ ≠ k * S.z * k⁻¹ := fun e => hbad.not_mem_QG (by rw [← e]; exact haQ)
  have h1 : h * S.z * h⁻¹ ∈ S.Qa k := S.mem_Qa_symm (g₁ := k) (g₂ := h) hax.symm hxa
  exact hbad.not_mem (isConj_iff.mpr ⟨h, rfl⟩) ⟨haQ, h1⟩

private theorem S2Data.exists_mem_Dl_cl_commutator_eq (D : S2Data S) (hw6 : 6 ≤ S.width)
    {k x : G} (hk : k * S.z * k⁻¹ = x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) {d : G}
    (hdc : IsConj S.z d) (hd : d ∈ S.QG ⊓ S.Qa k) {y : G} (hy : y ∈ S.QG) :
    ∃ e ∈ S.QG ⊓ S.Qa k, S.cl (x * y * x⁻¹ * y⁻¹) = S.cl e := by
  subst hk
  have hT := D.types_of_good hw6 hxM hxQ ⟨d, hdc, hd⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp hdc
  have hxz := D.not_isConj_mul_z_of_mem rfl hxM hxQ hd
  have hΔ : S.QG ⊓ S.Qa k ≠ ⊥ := by
    intro hbot
    rw [hbot, mem_bot] at hd
    apply S.z_ne_one
    have h1 : IsConj S.z 1 := by
      rw [← hd]
      exact isConj_iff.mpr ⟨g, rfl⟩
    exact isConj_one_left.mp h1
  have hEq := D.clSub_Dl_eq_commSpace_of_types hxM hT hxQ hxz hΔ
  have hmem : S.cl (k * S.z * k⁻¹ * y * (k * S.z * k⁻¹)⁻¹ * y⁻¹) ∈ S.commQt (k * S.z * k⁻¹) :=
    (S.mem_commQt_iff hxM).mpr ⟨y, hy, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨e, he, -, hec⟩ := S.mem_clSub_iff.mp hmem
  exact ⟨e, he, hec.symm⟩

private theorem S2Data.exists_cl_commutator_mem {k h x : G} (Da : S2Data (S.conjBy h))
    (hw6 : 6 ≤ S.width) (hk : k * S.z * k⁻¹ = x) (hxM : x ∈ S.M) (hxMa : x ∈ (S.conjBy h).M)
    (hxQa : x ∉ (S.conjBy h).QG) (haQ : h * S.z * h⁻¹ ∈ S.QG) {d : G}
    (hdc : IsConj (S.conjBy h).z d) (hd : d ∈ (S.conjBy h).QG ⊓ (S.conjBy h).Qa (k * h⁻¹))
    {y : G} (hyQ : y ∈ S.QG) (hyT : y ∈ (S.conjBy h).QG) :
    ∃ δ ∈ S.clSub (S.QG ⊓ S.Qa k), S.cl (x * y * x⁻¹ * y⁻¹) = δ ∨
      S.cl (x * y * x⁻¹ * y⁻¹) = δ + S.cl (h * S.z * h⁻¹) := by
  have hMa : k * h⁻¹ * (S.conjBy h).z * (k * h⁻¹)⁻¹ = x := by
    rw [← hk]
    show k * h⁻¹ * (h * S.z * h⁻¹) * (k * h⁻¹)⁻¹ = k * S.z * k⁻¹
    group
  have hQa : (S.conjBy h).Qa (k * h⁻¹) = S.Qa k :=
    Setting.QG_eq_of_z_eq _ _ (hMa.trans hk.symm)
  have hw6a : 6 ≤ (S.conjBy h).width := by rw [Setting.width_conjBy]; exact hw6
  obtain ⟨e, he, hec⟩ := Da.exists_mem_Dl_cl_commutator_eq hw6a hMa hxMa hxQa hdc hd hyT
  have hc'S : x * y * x⁻¹ * y⁻¹ ∈ S.QG := S.commutator_mem_QG hxM hyQ
  have hc'T : x * y * x⁻¹ * y⁻¹ ∈ (S.conjBy h).QG := (S.conjBy h).commutator_mem_QG hxMa hyT
  have hQe : e ∈ S.Qa k := by
    rw [← hQa]
    exact he.2
  rcases ((S.conjBy h).cl_eq_cl_iff he.1 hc'T).mp hec.symm with e1 | e1
  · have heS : e ∈ S.QG := by
      rw [← e1]
      exact hc'S
    refine ⟨S.cl e, S.cl_mem_clSub ⟨heS, hQe⟩ heS, Or.inl ?_⟩
    rw [e1]
  · have e1' : x * y * x⁻¹ * y⁻¹ = e * (h * S.z * h⁻¹) := e1
    have heS : e ∈ S.QG := by
      have : e = x * y * x⁻¹ * y⁻¹ * (h * S.z * h⁻¹)⁻¹ := by
        rw [e1']
        group
      rw [this]
      exact S.QG.mul_mem hc'S (S.QG.inv_mem haQ)
    refine ⟨S.cl e, S.cl_mem_clSub ⟨heS, hQe⟩ heS, Or.inr ?_⟩
    rw [e1', S.cl_mul heS haQ]

private theorem S2Data.false_of_forall_sub_mem (D : S2Data S) {Δt : Submodule (ZMod 2) S.Qt}
    {c : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t}
    (hhalf : 2 * finrank (ZMod 2) (commSpace c) = S.width) {v : Vt S D.g D.t} (hv0 : v ≠ 0)
    (hΔ : (Δt = ⊥ ∧ 6 ≤ S.width) ∨ (∃ p : Vt S D.g D.t,
      (∀ x : S.Qt, x ∈ Δt ↔ ∃ α β : ZMod 2, x = D.coord (α • p, β • p)) ∧ 8 ≤ S.width))
    (hclS : ∀ u : Vt S D.g D.t, D.betaV v u = 0 → ∃ δ ∈ Δt,
      D.coord (c u - u, 0) = δ ∨ D.coord (c u - u, 0) = δ + D.coord (v, 0)) : False := by
  have hdim : ∀ Y : Submodule (ZMod 2) (Vt S D.g D.t), (∀ u, D.betaV v u = 0 → c u - u ∈ Y) →
      finrank (ZMod 2) (commSpace c) ≤ finrank (ZMod 2) Y + 1 := by
    intro Y hY
    have h1 := finrank_le_add_of_forall_sub_mem c (D.betaV v) Y hY
    have h2 := finrank_commSpace_add_finrank_fixSpace c
    rw [D.finrank_Vt] at h1 h2
    omega
  rcases hΔ with ⟨hbot, hw6⟩ | ⟨p, hspan, hw8⟩
  ·
    have hY : ∀ u, D.betaV v u = 0 → c u - u ∈ ZMod 2 ∙ v := by
      intro u hu
      obtain ⟨δ, hδ, hδ'⟩ := hclS u hu
      rw [hbot, Submodule.mem_bot] at hδ
      rw [hδ, zero_add] at hδ'
      rcases hδ' with e | e
      · have h1 : D.coord (c u - u, 0) = D.coord (0, 0) := by
          rw [e, Prod.mk_zero_zero, map_zero]
        rw [(Prod.mk.inj (D.coord.injective h1)).1]
        exact Submodule.zero_mem _
      · rw [(Prod.mk.inj (D.coord.injective e)).1]
        exact Submodule.mem_span_singleton_self v
    have h1 := hdim _ hY
    have h2 : finrank (ZMod 2) (ZMod 2 ∙ v) = 1 := finrank_span_singleton hv0
    omega
  ·
    have hpS : p ∈ Submodule.span (ZMod 2) ({p, v} : Set (Vt S D.g D.t)) :=
      Submodule.subset_span (by simp)
    have hvS : v ∈ Submodule.span (ZMod 2) ({p, v} : Set (Vt S D.g D.t)) :=
      Submodule.subset_span (by simp)
    have hY : ∀ u, D.betaV v u = 0 →
        c u - u ∈ Submodule.span (ZMod 2) ({p, v} : Set (Vt S D.g D.t)) := by
      intro u hu
      obtain ⟨δ, hδ, hδ'⟩ := hclS u hu
      obtain ⟨α, β, rfl⟩ := (hspan δ).mp hδ
      rcases hδ' with e | e
      · rw [(Prod.mk.inj (D.coord.injective e)).1]
        exact Submodule.smul_mem _ _ hpS
      · rw [coord_add_coord_add, add_zero] at e
        rw [(Prod.mk.inj (D.coord.injective e)).1]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hpS) hvS
    have h1 := hdim _ hY
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({p, v} : Set (Vt S D.g D.t))) ≤ 2 := by
      classical
      have h := finrank_span_finset_le_card (R := ZMod 2) ({p, v} : Finset (Vt S D.g D.t))
      rw [Set.finrank, Finset.coe_pair] at h
      exact h.trans Finset.card_le_two
    omega

theorem S2Data.bad_conjBy_of_bad (D : S2Data S) {k h : G} (hbad : Bad S k)
    (hxC : S.ρ ⟨k * S.z * k⁻¹, hbad.mem_M⟩ ∈ D.Cbar)
    (hhalf : 2 * finrank (ZMod 2) (commSpace (D.resC ⟨_, hxC⟩)) = S.width)
    (hfix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (hΔ : (S.QG ⊓ S.Qa k = ⊥ ∧ 6 ≤ S.width) ∨ (∃ p : Vt S D.g D.t,
        p ∈ commSpace (D.resC ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
        (∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) ∧
        8 ≤ S.width))
    (haQ : h * S.z * h⁻¹ ∈ S.QG) {v : Vt S D.g D.t}
    (hv : v ∈ commSpace (D.resC ⟨_, hxC⟩)) (hv0 : v ≠ 0) (_hvs : D.QV v = 0)
    (hcl : S.cl (h * S.z * h⁻¹) = D.coord (v, 0)) (Da : S2Data (S.conjBy h)) :
    Bad (S.conjBy h) (k * h⁻¹) := by
  have hxM : k * S.z * k⁻¹ ∈ S.M := hbad.mem_M
  have hw6 : 6 ≤ S.width := by
    rcases hΔ with ⟨-, h6⟩ | ⟨-, -, -, -, h8⟩ <;> omega
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hne : h * S.z * h⁻¹ ≠ S.z := by
    intro e
    rw [e, S.cl_z] at hcl
    have h1 : D.coord (v, 0) = D.coord (0, 0) := by
      rw [← hcl, Prod.mk_zero_zero, map_zero]
    exact hv0 (Prod.mk.inj (D.coord.injective h1)).1
  have hcomm : (k * S.z * k⁻¹) * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * (k * S.z * k⁻¹) :=
    commute_of_cl_mem_commSpace hxM hx2 haQ hfix (by
      rw [hcl]
      exact (D.mem_commSpace_iff_coord_of_mem_Cbar hxC).mpr
        ⟨v, 0, hv, Submodule.zero_mem _, rfl⟩)
  have hxMa : k * S.z * k⁻¹ ∈ (S.conjBy h).M := mem_centralizer_singleton_iff.mpr hcomm
  have hxQa : k * S.z * k⁻¹ ∉ (S.conjBy h).QG := not_mem_Qa_of_bad hbad haQ
  have hMa : k * h⁻¹ * (S.conjBy h).z * (k * h⁻¹)⁻¹ = k * S.z * k⁻¹ := by
    show k * h⁻¹ * (h * S.z * h⁻¹) * (k * h⁻¹)⁻¹ = k * S.z * k⁻¹
    group
  refine ⟨?_, ?_, fun d hdc hd => ?_⟩
  · rw [hMa]
    exact hxMa
  · rw [hMa]
    exact hxQa
  refine D.false_of_forall_sub_mem (Δt := S.clSub (S.QG ⊓ S.Qa k)) hhalf hv0 ?_ ?_
  · rcases hΔ with ⟨hbot, hw6⟩ | ⟨p, -, -, hspan, hw8⟩
    · refine Or.inl ⟨?_, hw6⟩
      rw [hbot, eq_bot_iff]
      intro δ hδ
      obtain ⟨y, hy, -, rfl⟩ := S.mem_clSub_iff.mp hδ
      rw [mem_bot.mp hy, S.cl_one]
      exact Submodule.zero_mem _
    · exact Or.inr ⟨p, hspan, hw8⟩
  · intro u hu
    have hmemP : D.coord (u, 0) ∈ S.clSub (S.QG ⊓ S.Qa h) := by
      rw [D.clSub_QG_inf_Qa_eq_Pfst haQ hne hcl]
      exact D.mem_Pfst_iff.mpr ⟨u, 0, hu, by rw [zero_smul]⟩
    obtain ⟨y, hy, hyQ, hyc⟩ := S.mem_clSub_iff.mp hmemP
    obtain ⟨δ, hδ, hδ'⟩ := Da.exists_cl_commutator_mem hw6 rfl hxM hxMa hxQa haQ hdc hd hyQ hy.2
    refine ⟨δ, hδ, ?_⟩
    rw [← D.cl_commutator_eq_coord hxM hxC hyQ hyc, ← hcl]
    exact hδ'

end CFSG.GF2Type.Smith1980Orth
