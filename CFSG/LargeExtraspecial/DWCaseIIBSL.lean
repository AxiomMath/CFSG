module

public import CFSG.LargeExtraspecial.DWCaseIIBSLA
public import CFSG.LargeExtraspecial.DWTransGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
  (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
  (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
  (hD : spanD S = S.clSub A)
include hA hM hII hbad hD

omit hM hII hbad hD in
theorem exists_mem_clSub_polar (h4 : 4 ≤ S.width) (u p p' : S.Qt) :
    ∃ c ∈ S.clSub A, polar S.q c u = 0 ∧ c ∉ Submodule.span (ZMod 2) {p, p'} := by
  have := finiteDimensional_Qt (S := S)
  by_contra hcon
  push Not at hcon
  set φ : S.Qt →ₗ[ZMod 2] ZMod 2 := S.q.polarBilin.flip u
  have hKle : S.clSub A ⊓ LinearMap.ker φ ≤ Submodule.span (ZMod 2) {p, p'} :=
    fun v ⟨hv, hv'⟩ => hcon v hv (by simpa [φ] using hv')
  have hker := LinearMap.finrank_range_add_finrank_ker φ
  have hr : finrank (ZMod 2) (LinearMap.range φ) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  rw [S.finrank_Qt_eq_two_mul_width] at hker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub A) (LinearMap.ker φ)
  have hsup := Submodule.finrank_le (S.clSub A ⊔ LinearMap.ker φ)
  rw [hA.finrank_clSub] at hsum
  rw [S.finrank_Qt_eq_two_mul_width] at hsup
  have hpair : finrank (ZMod 2) (Submodule.span (ZMod 2) ({p, p'} : Set S.Qt)) ≤ 2 := by
    classical
    calc _ ≤ ({p, p'} : Set S.Qt).toFinset.card := finrank_span_le_card _
      _ ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_le_two
  have := Submodule.finrank_mono hKle
  omega

theorem false_of_sl (h4 : 4 ≤ S.width)
    (hsl : ∀ h : G, h * S.z * h⁻¹ ∈ A → h * S.z * h⁻¹ ≠ S.z →
      axisA S A h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹))
    {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z) : False := by
  have := finiteDimensional_Qt (S := S)
  have hWs := q_spanD hII
  have hxQ := hA.le_QG hxA
  set c₀ := S.cl (g * S.z * g⁻¹) with hc₀
  have hx0 : c₀ ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hslx := hsl g hxA hxz
  have hxAt : c₀ ∈ S.clSub A := S.cl_mem_clSub hxA hxQ
  have hxE : c₀ ∈ S.clSub (S.QG ⊓ S.Qa g) := S.cl_mem_clSub (hA.conj_mem_E hxA) hxQ
  obtain ⟨w, hw⟩ := exists_polar_eq_one hx0
  have hex : ∃ t ∈ S.Lbar g, ∃ v ∈ S.clSub (S.QG ⊓ S.Qa g),
      polar S.q v ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : S.clSub (S.QG ⊓ S.Qa g) ≤ ZMod 2 ∙ c₀ := by
      intro v hv
      obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
      have hfix : ∀ k ∈ S.L0 g, S.cl (k * e * k⁻¹) = S.cl e := by
        intro k hk
        have ht : S.ρ ⟨k, hk.2⟩ ∈ S.Lbar g := mem_Lbar.mpr ⟨k, hk, rfl⟩
        have h1 := sub_eq_polar_smul (Lbar_apply_cl hxQ ht) hw
          (Lbar_sub_mem_span_of_mem_E ht hv)
        rw [hcon _ ht _ hv, zero_smul, sub_eq_zero, S.ρ_cl _ heQ] at h1
        exact h1
      rcases S.mem_of_cl_fixed_by_L0 hxQ hxz he hfix with h | h | h | h
      · rw [h, S.cl_one]
        exact zero_mem _
      · rw [h]
        exact Submodule.mem_span_singleton_self _
      · rw [h, S.cl_z]
        exact zero_mem _
      · rw [h, S.cl_mul S.z_mem_QG hxQ, S.cl_z, zero_add]
        exact Submodule.mem_span_singleton_self _
    have h1 := Submodule.finrank_mono hle
    rw [hA.finrank_clSub_E hM hII hbad hD hxA hxz, finrank_span_singleton hx0] at h1
    omega
  obtain ⟨t, ht, e₀, he₀, hne⟩ := hex
  set u := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w with hu_def
  have htx : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) c₀ = c₀ := Lbar_apply_cl hxQ ht
  have hu : polar S.q c₀ u = 0 := by
    have h2 := polar_apply_apply t c₀ w
    rw [htx] at h2
    rw [hu_def, polar_sub_right, h2, sub_self]
  have htv : ∀ v, polar S.q c₀ v = 0 →
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar S.q v u • c₀ := by
    intro v hv
    have := sub_eq_polar_smul htx hw
      (hA.Lbar_sub_mem_span_of_polar hM hII hbad hD hxA hxz hslx ht hv)
    rw [← this]
    abel
  obtain ⟨α, hα, ε, hε, huαε⟩ :=
    Submodule.mem_sup.mp (hA.mem_sup_of_polar hM hII hbad hD hxA hxz hslx hu)
  have hαe : polar S.q e₀ α ≠ 0 := by
    rwa [← huαε, polar_add_right, polar_E_E hxz he₀ hε, add_zero] at hne
  have hαx : α ∉ ZMod 2 ∙ c₀ := by
    intro h
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp h
    apply hαe
    obtain ⟨e, he, -, rfl⟩ := S.mem_clSub_iff.mp he₀
    rw [polar_smul_right, polar_comm, hA.polar_cl_E hxA he, smul_zero]
  obtain ⟨c, hcA, hcu, hcn⟩ := hA.exists_mem_clSub_polar h4 u c₀ α
  have hc0 : c ≠ 0 := fun h => hcn (h ▸ zero_mem _)
  have hαn : (⟨α, hα⟩ : S.clSub A) ∉
      Submodule.span (ZMod 2) {(⟨c₀, hxAt⟩ : S.clSub A), ⟨c, hcA⟩} := by
    intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    have hab' : a • c₀ + b • c = α := congrArg Subtype.val hab
    rcases zmod2_dichotomy b with rfl | rfl
    · apply hαx
      rw [← hab', zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · apply hcn
      have : c = a • c₀ + α := by
        rw [← hab', one_smul, ← add_assoc, ZModModule.add_self, zero_add]
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
  obtain ⟨f, hfα, hfle⟩ := Submodule.exists_le_ker_of_notMem hαn
  have hfx : f ⟨c₀, hxAt⟩ = 0 := hfle (Submodule.subset_span (by simp))
  have hfc : f ⟨c, hcA⟩ = 0 := hfle (Submodule.subset_span (by simp))
  have hfα1 : f ⟨α, hα⟩ = 1 := by
    rcases zmod2_dichotomy (f ⟨α, hα⟩) with h | h
    · exact absurd h hfα
    · exact h
  have hcD : c ∈ spanD S := by rw [hD]; exact hcA
  obtain ⟨hk1, hk2, hk3⟩ := repD_spec hWs hcD hc0
  have hkcA := hII _ hk1
  obtain ⟨m, hm, hmw⟩ := hA.exists_Abar_eq hM hII hkcA hk2 f fun v hv => by
    rw [hsl _ hkcA hk2, hk3] at hv
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hv
    have : v = μ • (⟨c, hcA⟩ : S.clSub A) := Subtype.ext hμ.symm
    rw [this, map_smul, hfc, smul_zero]
  rw [hk3] at hmw
  have hmv : ∀ v (hv : v ∈ S.clSub A), (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + f ⟨v, hv⟩ • c :=
    fun v hv => hmw ⟨v, hv⟩
  have hmx : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) c₀ = c₀ := by
    rw [hmv c₀ hxAt, hfx, zero_smul, add_zero]
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp hm
  have hax : S.cl (a * (g * S.z * g⁻¹) * a⁻¹) = c₀ := by
    rw [← S.ρ_cl ⟨a, ha.2⟩ hxQ]
    exact hmx
  obtain ⟨k, hkM, hkx, hkρ⟩ : ∃ k, ∃ hk : k ∈ S.M,
      k * (g * S.z * g⁻¹) * k⁻¹ = g * S.z * g⁻¹ ∧ S.ρ ⟨k, hk⟩ = S.ρ ⟨a, ha.2⟩ := by
    rcases (S.cl_eq_cl_iff hxQ (S.conj_mem_QG ha.2 hxQ)).mp hax.symm with h | h
    · exact ⟨a, ha.2, h, rfl⟩
    · obtain ⟨q, hq, hqx⟩ := S.exists_conj_eq_mul_z hxQ (S.s12_conj_z_ne_one g) hxz
      have hqM : q⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hq)
      refine ⟨q⁻¹ * a, S.M.mul_mem hqM ha.2, ?_, ?_⟩
      · calc q⁻¹ * a * (g * S.z * g⁻¹) * (q⁻¹ * a)⁻¹
            = q⁻¹ * (a * (g * S.z * g⁻¹) * a⁻¹) * q := by group
          _ = q⁻¹ * (q * (g * S.z * g⁻¹) * q⁻¹) * q := by rw [h, hqx]
          _ = g * S.z * g⁻¹ := by group
      · have : (⟨q⁻¹ * a, S.M.mul_mem hqM ha.2⟩ : S.M) = ⟨q⁻¹, hqM⟩ * ⟨a, ha.2⟩ := rfl
        rw [this, map_mul, (S.ρ_eq_one_iff _).mpr (S.QG.inv_mem hq), one_mul]
  set mm : S.O := S.ρ ⟨a, ha.2⟩ with hmm
  have hkxM : k ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]
    calc k * (g * S.z * g⁻¹) = k * (g * S.z * g⁻¹) * k⁻¹ * k := by group
      _ = (g * S.z * g⁻¹) * k := by rw [hkx]
  have hmE : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g),
      (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    intro v hv
    obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [← hkρ, S.ρ_cl ⟨k, hkM⟩ heQ]
    exact S.cl_mem_clSub ⟨S.conj_mem_QG hkM heQ, (S.conjBy g).conj_mem_QG hkxM he.2⟩
      (S.conj_mem_QG hkM heQ)
  have hcomm : mm * t = t * mm := by
    have hmM : mm ∈ S.Mbar := ⟨_, rfl⟩
    have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
    have key : resAt S A hM ⟨mm * t, S.Mbar.mul_mem hmM htM⟩ =
        resAt S A hM ⟨t * mm, S.Mbar.mul_mem htM hmM⟩ := by
      refine LinearEquiv.ext fun v => Subtype.ext ?_
      rw [coe_resAt_apply, coe_resAt_apply]
      change (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      have hvx : polar S.q c₀ v = 0 := hA.polar_cl_A hxA v.2
      have hcx : polar S.q c₀ c = 0 := hA.polar_cl_A hxA hcA
      have h1 : (v : S.Qt) + polar S.q v u • c₀ ∈ S.clSub A :=
        add_mem v.2 (Submodule.smul_mem _ _ hxAt)
      have hf1 : f ⟨(v : S.Qt) + polar S.q v u • c₀, h1⟩ = f v := by
        rw [show (⟨(v : S.Qt) + polar S.q v u • c₀, h1⟩ : S.clSub A) =
          v + polar S.q v u • ⟨c₀, hxAt⟩ from rfl, map_add, map_smul, hfx, smul_zero, add_zero]
      rw [htv v hvx, hmv _ h1, hf1, hmv v v.2, map_add, map_smul, htv c hcx, hcu, zero_smul,
        add_zero, htv v hvx]
    exact congrArg Subtype.val (hA.resAt_injective hM key)
  have hd : polar S.q c₀ ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) = 0 := by
    have h2 := polar_apply_apply mm c₀ w
    rw [hmx] at h2
    rw [polar_sub_right, h2, sub_self]
  have hmu : (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ ZMod 2 ∙ c₀ := by
    have e1 : (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
      congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) hcomm
    have htd := hA.Lbar_sub_mem_span_of_polar hM hII hbad hD hxA hxz hslx ht hd
    have e2 : (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
          ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
      rw [hu_def]
      simp only [map_sub]
      rw [e1]
      abel
    rw [e2]
    exact htd
  have hmα : (mm : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α + c := by rw [hmv α hα, hfα1, one_smul]
  have hcE : c ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    have e3 : c = ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) -
        ((mm : S.Qt ≃ₗ[ZMod 2] S.Qt) ε - ε) := by
      rw [← huαε, map_add, hmα]
      abel
    rw [e3]
    refine sub_mem ?_ (sub_mem (hmE ε hε) hε)
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmu
    rw [← hμ]
    exact Submodule.smul_mem _ _ hxE
  exact hcn (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    (hA.mem_span_of_mem_clSub_E hM hII hslx hcA hcE))

end MaxEA

end CFSG.LargeExtraspecial.DW
