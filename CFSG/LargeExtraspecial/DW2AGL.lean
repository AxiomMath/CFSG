module

public import CFSG.LargeExtraspecial.DW2AXbar
public import CFSG.LargeExtraspecial.DW2ACocycle
public import CFSG.LargeExtraspecial.DW2AEnd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem map_spanD_eq {t : S.O} (ht : t ∈ S.Mbar) :
    (spanD S).map ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = spanD S := by
  obtain ⟨m, rfl⟩ := ht
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨w, hw, rfl⟩
  exact isMbarInvariant_spanD m w hw

variable (S) in
@[expose] noncomputable def resD : XbarD S →* (spanD S ≃ₗ[ZMod 2] spanD S) where
  toFun t := LinearEquiv.ofSubmodules ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (spanD S) (spanD S)
    (map_spanD_eq (XbarD_le_Mbar t.2))
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem coe_resD_apply (t : XbarD S) (w : spanD S) :
    ((resD S t w : spanD S) : S.Qt) = ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w :=
  rfl

section SLCase

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)
include hWs

theorem Abar_apply_spanD {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ Abar S (S.clPre (spanD S)) h) {w : S.Qt} (hw : w ∈ spanD S) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
  exact ρ_sub_mem_span isMbarInvariant_spanD hDQ_spanD hWs hyQ (cl_conj_mem_spanD hyQ) hyz ha.1 hw

theorem Abar_apply_cl {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ Abar S (S.clPre (spanD S)) h) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
  have h1 := Abar_apply_spanD hWs hyQ hyz ht (cl_conj_mem_spanD hyQ)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h1
  rcases zmod2_cases μ with rfl | rfl
  · rw [zero_smul, eq_comm, sub_eq_zero] at hμ
    exact hμ
  · exfalso
    rw [one_smul, eq_comm, sub_eq_iff_eq_add, add_self_zmod2] at hμ
    exact (cl_ne_zero_iff hyQ).mpr hyz ((LinearEquiv.map_eq_zero_iff _).mp hμ)

theorem exists_mem_Abar_eq_transvection {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG)
    (hyz : h * S.z * h⁻¹ ≠ S.z) (hax : axisD S h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹))
    (f : Module.Dual (ZMod 2) (spanD S))
    (hf : f ⟨S.cl (h * S.z * h⁻¹), cl_conj_mem_spanD hyQ⟩ = 0) :
    ∃ t ∈ Abar S (S.clPre (spanD S)) h, ∀ w : spanD S,
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + f w • S.cl (h * S.z * h⁻¹) := by
  set d := S.cl (h * S.z * h⁻¹)
  have hd0 : d ≠ 0 := (cl_ne_zero_iff hyQ).mpr hyz
  obtain ⟨t, ⟨τ, hτ, rfl⟩, ht⟩ := exists_eq_add_smul_of_dual (V := S.Qt)
    (T := (Abar S (S.clPre (spanD S)) h).map S.O.subtype) (W := spanD S) (c := d) hd0
    (by rintro _ ⟨τ, hτ, rfl⟩; exact Abar_apply_cl hWs hyQ hyz hτ)
    (by rintro _ ⟨τ, hτ, rfl⟩ w hw; exact Abar_apply_spanD hWs hyQ hyz hτ hw) f
    (fun w hw => by
      have h1 := (mem_fixIn_Abar_iff hWs hyQ hyz w.2).mp hw
      rw [hax] at h1
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h1
      have : w = μ • (⟨d, cl_conj_mem_spanD hyQ⟩ : spanD S) := Subtype.ext hμ.symm
      rw [this, map_smul, hf, smul_zero])
  exact ⟨τ, hτ, ht⟩

end SLCase

theorem le_perp_of_forall_q {W : Submodule (ZMod 2) S.Qt} (hWs : ∀ v ∈ W, S.q v = 0) :
    W ≤ perp S W := fun w hw => mem_perp.mpr fun v hv => by
  rw [polar, hWs _ (W.add_mem hv hw), hWs v hv, hWs w hw]
  rfl

theorem resD_injective (hWs : ∀ v ∈ spanD S, S.q v = 0) : Function.Injective (resD S) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  refine Subtype.ext (XbarD_eq_one hWs t.2 fun w hw => ?_)
  have := congrArg Subtype.val (LinearEquiv.congr_fun ht ⟨w, hw⟩)
  rw [coe_resD_apply] at this
  exact this

theorem false_of_axisD_eq_span_of_nondeg [IsSimpleGroup G] (hn : 2 ≤ S.width)
    (hP : NondegWeaklyClosed S)
    (hWs : ∀ v ∈ spanD S, S.q v = 0) (hlt : finrank (ZMod 2) (spanD S) < S.width)
    (hk : 3 ≤ finrank (ZMod 2) (spanD S))
    (hGL : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
      axisD S h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹)) {g₀ : G} (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG)
    (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) : False := by
  set W := spanD S with hWdef
  have hW := isMbarInvariant_spanD (S := S)
  have hWW : W ≤ perp S W := le_perp_of_forall_q hWs
  have hc₁ := cl_conj_mem_spanD hg₀Q
  have hc₁0 : S.cl (g₀ * S.z * g₀⁻¹) ≠ 0 := (cl_ne_zero_iff hg₀Q).mpr hg₀
  have hW0 : W ≠ ⊥ := fun h => hc₁0 (by
    have h2 : S.cl (g₀ * S.z * g₀⁻¹) ∈ W := hc₁
    rw [h, Submodule.mem_bot] at h2
    exact h2)
  have hlift : ∀ (f : Module.Dual (ZMod 2) W) (d : W) (hfd : f d = 0), ∃ t : XbarD S,
      resD S t = LinearEquiv.transvection hfd ∧ ((d : S.Qt) ≠ 0 → ∃ k : G,
        k * S.z * k⁻¹ ∈ S.QG ∧ k * S.z * k⁻¹ ≠ S.z ∧ S.cl (k * S.z * k⁻¹) = d ∧
          (t : S.O) ∈ Abar S (S.clPre (spanD S)) k) := by
    intro f d hfd
    by_cases hd : (d : S.Qt) = 0
    · have hd' : d = 0 := Subtype.ext hd
      subst hd'
      exact ⟨1, by rw [map_one, transvection_eq_one], fun h => absurd hd h⟩
    · obtain ⟨k, hkQ, hkz, hkd⟩ := exists_conj_of_mem_spanD_ne hWs d.2 hd
      have hfk : f ⟨S.cl (k * S.z * k⁻¹), cl_conj_mem_spanD hkQ⟩ = 0 := by
        rw [show (⟨S.cl (k * S.z * k⁻¹), cl_conj_mem_spanD hkQ⟩ : W) = d from Subtype.ext hkd]
        exact hfd
      obtain ⟨τ, hτ, hτw⟩ := exists_mem_Abar_eq_transvection hWs hkQ hkz (hGL k hkQ hkz) f hfk
      refine ⟨⟨τ, Abar_le_XbarD hkQ hkz hτ⟩, ?_, fun _ => ⟨k, hkQ, hkz, hkd, hτ⟩⟩
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      rw [coe_resD_apply, hτw, transvection_apply, Submodule.coe_add, Submodule.coe_smul, hkd]
  have hcob : ∀ v ∈ perp S W, ∃ w ∈ W, v + w ∈ fixD S := by
    intro v hv
    let δ : XbarD S → W := fun t => ⟨((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v,
      XbarD_sub_mem hWs t.2 v hv⟩
    have hδ : ∀ s t, δ (s * t) = δ s + resD S s (δ t) := by
      intro s t
      apply Subtype.ext
      simp only [δ, Submodule.coe_add, coe_resD_apply]
      rw [map_sub]
      change ((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v = _
      abel
    have hker : ∀ t, resD S t = 1 → δ t = 0 := by
      intro t ht
      have : t = 1 := resD_injective hWs (by rw [ht, map_one])
      subst this
      apply Subtype.ext
      simp [δ]
    have hcen : ∀ (f : Module.Dual (ZMod 2) W) (d : W) (h : f d = 0) (l : XbarD S),
        resD S l = LinearEquiv.transvection h → δ l ∈ (ZMod 2) ∙ d := by
      intro f d hfd l hl
      obtain ⟨t, ht, ht'⟩ := hlift f d hfd
      have hlt' : l = t := resD_injective hWs (by rw [hl, ht])
      subst hlt'
      by_cases hd : (d : S.Qt) = 0
      · have hd' : d = 0 := Subtype.ext hd
        subst hd'
        have h1 : l = 1 := resD_injective hWs (by rw [hl, map_one, transvection_eq_one])
        subst h1
        rw [hker 1 (map_one _)]
        exact zero_mem _
      · obtain ⟨k, hkQ, hkz, hkd, hlk⟩ := ht' hd
        obtain ⟨a, ha, hae⟩ := mem_Abar.mp hlk
        have h1 := ρ_sub_mem_span_of_mem_perp hW hDQ_spanD hWs hkQ (cl_conj_mem_spanD hkQ) hkz
          ha.1 hv
        rw [hae, hkd] at h1
        obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h1
        exact Submodule.mem_span_singleton.mpr ⟨μ, Subtype.ext hμ⟩
    have hdim : 3 ≤ finrank (ZMod 2) W := hk
    obtain ⟨w, hw⟩ := exists_eq_of_isCocycle_of_mem_span hdim (resD S)
      (fun f d h => (hlift f d h).imp fun t ht => ht.1) δ hδ hker hcen
    refine ⟨w, w.2, mem_fixD.mpr ⟨add_mem hv (hWW w.2), fun t ht => ?_⟩⟩
    have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w + w :=
      congrArg Subtype.val (hw ⟨t, ht⟩)
    rw [map_add]
    have : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w + w) := by
      rw [← h1]
      abel
    rw [this, show v + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w + w) + (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      v + w + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w + (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) by abel,
      add_self_zmod2, add_zero]
  have hTW0 : fixD S ⊓ W = ⊥ := by
    obtain ⟨c₂, hc₂W, hc₂⟩ : ∃ c₂ ∈ W, c₂ ∉ ZMod 2 ∙ S.cl (g₀ * S.z * g₀⁻¹) := by
      by_contra hc
      push Not at hc
      have := Submodule.finrank_mono (show W ≤ ZMod 2 ∙ S.cl (g₀ * S.z * g₀⁻¹) from hc)
      rw [finrank_span_singleton hc₁0] at this
      omega
    have hc₂0 : c₂ ≠ 0 := fun h => hc₂ (h ▸ zero_mem _)
    obtain ⟨k, hkQ, hkz, hkc⟩ := exists_conj_of_mem_spanD_ne hWs hc₂W hc₂0
    rw [eq_bot_iff]
    rintro v ⟨hvT, hvW⟩
    have hfix : ∀ {h : G}, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
        v ∈ ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
      intro h hQ hz
      rw [← hGL h hQ hz, ← mem_fixIn_Abar_iff hWs hQ hz hvW]
      refine ⟨hvW, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact (mem_fixD.mp hvT).2 t (Abar_le_XbarD hQ hz ht)
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hfix hg₀Q hg₀)
    obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp (hfix hkQ hkz)
    rw [Submodule.mem_bot]
    rcases zmod2_cases μ with rfl | rfl
    · rw [← hμ, zero_smul]
    rcases zmod2_cases ν with rfl | rfl
    · rw [← hν, zero_smul]
    exfalso
    apply hc₂
    rw [← hkc, ← one_smul (ZMod 2) (S.cl (k * S.z * k⁻¹)), hν, ← hμ, one_smul]
    exact Submodule.mem_span_singleton_self _
  have hTle : fixD S ≤ perp S W := fun v hv => (mem_fixD.mp hv).1
  have hle : perp S W ≤ fixD S ⊔ W := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hcob v hv
    have : v = (v + w) + w := by rw [add_assoc, add_self_zmod2, add_zero]
    rw [this]
    exact add_mem (Submodule.mem_sup_left hvw) (Submodule.mem_sup_right hw)
  exact false_of_sup_ge_of_nondeg hn hP hg₀Q hg₀ hW hWW hW0 hlt isMbarInvariant_fixD hTle hTW0
    (le_trans (Submodule.finrank_mono hle) (Nat.le_succ _))

end CFSG.LargeExtraspecial.DW
