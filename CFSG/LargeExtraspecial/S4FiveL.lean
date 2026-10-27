module

public import CFSG.LargeExtraspecial.S4Res
public import CFSG.LargeExtraspecial.S4FiveB
public import CFSG.LargeExtraspecial.S4Lin
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commute_inv {t x : S.O} (hx : x * t = t * x) : x⁻¹ * t = t * x⁻¹ := by
  calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hx]
    _ = t * x⁻¹ := by group

theorem V_le_Qa_mul (H : Hyp4 S g) {t : S.O} (hVQ : V S g t ≤ S.Qa g) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) : V S g t ≤ S.Qa ((k : G) * g) := by
  intro x hx
  rw [mem_Qa_mul_iff]
  apply hVQ
  have hk' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
    rw [map_inv]
    exact commute_inv (commute_of_mem_Rbar H.conj_mem hk)
  have := conj_mem_V_of_commute H hk' hx
  simpa using this

theorem exists_of_mem_orbit {t : S.O} {u : S.Qt} (hu : u ∈ orbit S g t)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ u = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  exact ⟨k, hx, ρ_cl_conj_z S k haQ⟩

theorem mem_Lbar_mul_of_mem_Rbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) : t ∈ S.Lbar ((k : G) * g) := by
  have h1 := conj_mem_Lbar_mul S k ht
  rwa [commute_of_mem_Rbar H.conj_mem hk, mul_assoc, mul_inv_cancel, mul_one] at h1

theorem add_mem_orbit_of_V_le (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hVQ : V S g t ≤ S.Qa g) {u v : S.Qt} (hu : u ∈ orbit S g t) (hv : v ∈ orbit S g t)
    (huv : u ≠ v) : u + v ∈ orbit S g t := by
  have haQ := H.conj_mem
  obtain ⟨k₁, hk₁, rfl⟩ := exists_of_mem_orbit hu haQ
  obtain ⟨k₂, hk₂, rfl⟩ := exists_of_mem_orbit hv haQ
  set b := (k₁ : G) * g * S.z * ((k₁ : G) * g)⁻¹ with hb
  set c := (k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹ with hc
  have hbQ : b ∈ S.QG := conj_mem_QG' S k₁.2 haQ
  have hcQ : c ∈ S.QG := conj_mem_QG' S k₂.2 haQ
  have hbV : b ∈ V S g t := ⟨hbQ, orbit_subset_Vt ht haQ hu⟩
  have hbQc : b ∈ S.Qa ((k₂ : G) * g) := V_le_Qa_mul H hVQ hk₂ hbV
  set T := S.conjBy ((k₂ : G) * g) with hT
  have hTz : T.z = c := rfl
  have hzc : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl hcQ (conj_ne_z' S k₂.2 H.conj_ne)
  have hb1 : T.cl b ≠ 0 := by
    intro h
    rcases (T.cl_eq_zero_iff hbQc).mp h with h1 | h1
    · exact conj_z_ne_one S _ h1
    · exact huv (by rw [show b = c from h1])
  have hbz : T.cl b ≠ T.cl S.z := by
    intro h
    rcases (T.cl_eq_cl_iff hzc hbQc).mp h.symm with h1 | h1
    · exact conj_ne_z' S k₁.2 H.conj_ne h1
    · apply huv
      rw [show b = S.z * c from h1, S.cl_mul S.z_mem_QG hcQ, S.cl_z, zero_add]
  obtain ⟨w, hw0, hw1⟩ := T.exists_polar_eq_zero_eq_one hb1 hbz
  obtain ⟨y, hyQ, rfl⟩ := T.exists_cl w
  have hyz : y * S.z = S.z * y := (T.polar_cl_eq_zero_iff hyQ hzc).mp hw0
  have hyb : y * b ≠ b * y := (T.polar_cl_eq_one_iff hyQ hbQc).mp hw1
  have hyM : y ∈ S.M := S.mem_M_iff.mpr hyz
  have hyL : y ∈ S.L0 ((k₂ : G) * g) := ⟨hyQ, hyM⟩
  have hybc : y * b * y⁻¹ = c * b := by
    rcases T.mul_comm_or hyQ hbQc with h | h
    · exact absurd h hyb
    · rw [h, hTz]
      group
  have hyR : S.ρ ⟨y, hyM⟩ ∈ Rbar S g t :=
    Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht hk₂) (ρ_mem_Lbar S hyL)
  have hmem := apply_mem_orbit hyR hu
  rwa [S.ρ_cl ⟨y, hyM⟩ hbQ, hybc, S.cl_mul hcQ hbQ, add_comm] at hmem

theorem mem_orbit_of_V_le (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hVQ : V S g t ≤ S.Qa g) {v : S.Qt} (hv : v ∈ Vt S g t) (hv0 : v ≠ 0) :
    v ∈ orbit S g t := by
  let K : Submodule (ZMod 2) S.Qt :=
    { carrier := {w | w = 0 ∨ w ∈ orbit S g t}
      add_mem' := by
        rintro u w (rfl | hu) (rfl | hw)
        · exact Or.inl (add_zero 0)
        · exact Or.inr (by rwa [zero_add])
        · exact Or.inr (by rwa [add_zero])
        · by_cases huw : u = w
          · exact Or.inl (by rw [huw, OrthoF2.vec_add_self])
          · exact Or.inr (add_mem_orbit_of_V_le H ht hVQ hu hw huw)
      zero_mem' := Or.inl rfl
      smul_mem' := by
        rintro c u hu
        rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
        · exact Or.inl (zero_smul _ _)
        · rwa [one_smul] }
  have hle : Vt S g t ≤ K := by
    rw [Vt_eq_span_orbit H ht, Submodule.span_le]
    intro w hw
    exact Or.inr hw
  exact (hle hv).resolve_left hv0

theorem Vt_le_clSub_of_V_le {t : S.O} (hVQ : V S g t ≤ S.Qa g) :
    Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  exact S.cl_mem_clSub ⟨hx, hVQ ⟨hx, hv⟩⟩ hx

@[expose] noncomputable def aV {t : S.O} (ht : t ∈ S.Lbar g) : Vt S g t :=
  ⟨S.cl (g * S.z * g⁻¹), cl_a_mem_Vt ht⟩

theorem aV_ne_zero (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : aV ht ≠ 0 := fun h =>
  cl_conj_z_ne_zero S H.conj_mem H.conj_ne (congrArg Subtype.val h)

theorem fixSpaceOf_LmodN_le (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    fixSpaceOf (LmodN S g t) ≤ (ZMod 2) ∙ aV ht := by
  intro u hu
  rw [mem_span_singleton_subtype]
  change (u : S.Qt) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
  rw [← H.fixSub_eq]
  intro s hs
  have h1 := (mem_fixSpaceOf.mp hu) (resL H.conj_mem ht ⟨s, hs⟩)
    ((range_resL H.conj_mem ht) ▸ ⟨⟨s, hs⟩, rfl⟩)
  exact congrArg Subtype.val h1

theorem LmodN_eq_centreGroup (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hVQ : V S g t ≤ S.Qa g) : LmodN S g t = centreGroup (Vt S g t) (aV ht) := by
  have haQ := H.conj_mem
  have hψ : ∀ x (u : Vt S g t), resL haQ ht x u - u ∈ (ZMod 2) ∙ aV ht := by
    intro x u
    rw [mem_span_singleton_subtype]
    obtain ⟨y, hy, -, hyu⟩ := S.mem_clSub_iff.mp (Vt_le_clSub_of_V_le hVQ u.2)
    have := Lbar_apply_sub_mem_span haQ hy x.2
    rw [hyu] at this
    exact this
  have hle : LmodN S g t ≤ centreGroup (Vt S g t) (aV ht) := by
    rw [← range_resL haQ ht]
    rintro _ ⟨x, rfl⟩
    exact hψ x
  have hcard := card_range_of_transvections (isPGroup_Lbar S haQ) (resL haQ ht) (aV ht) hψ
  rw [range_resL haQ ht] at hcard
  have hfix : fixSpaceOf (LmodN S g t) = (ZMod 2) ∙ aV ht := by
    refine le_antisymm (fixSpaceOf_LmodN_le H ht) ?_
    rw [Submodule.span_singleton_le_iff_mem, mem_fixSpaceOf]
    rintro e ⟨s, hs, hes⟩
    apply Subtype.ext
    rw [hes]
    exact (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _) s hs
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  refine eq_of_le_of_card_ge hle ?_
  rw [card_centreGroup (aV_ne_zero H ht), hcard.1, hfix, finrank_span_singleton (aV_ne_zero H ht)]

theorem exists_RmodN_of_mem_orbit {t : S.O} (ht : t ∈ S.Lbar g) (haQ : g * S.z * g⁻¹ ∈ S.QG)
    {v : Vt S g t} (hv : (v : S.Qt) ∈ orbit S g t) : ∃ e ∈ RmodN S g t, e (aV ht) = v := by
  obtain ⟨x, hx, hxv⟩ := hv
  refine ⟨resV haQ t ⟨x, hx⟩, (range_resV haQ t) ▸ ⟨_, rfl⟩, Subtype.ext ?_⟩
  rw [coe_resV_apply]
  exact hxv.symm

theorem conj_mem_centreGroup {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {c : U} {e f : U ≃ₗ[ZMod 2] U} (hf : f ∈ centreGroup U c) :
    e * f * e⁻¹ ∈ centreGroup U (e c) := by
  intro u
  have h1 := hf (e⁻¹ u)
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h1
  rw [Submodule.mem_span_singleton]
  refine ⟨k, ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    show f (e⁻¹ u) = e⁻¹ u + k • c by rw [hk]; abel, map_add, map_smul,
    show e (e⁻¹ u) = u from e.apply_symm_apply u]
  abel

theorem centreGroup_le_RmodN (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hVQ : V S g t ≤ S.Qa g) (c : Vt S g t) : centreGroup (Vt S g t) c ≤ RmodN S g t := by
  by_cases hc : c = 0
  · intro f hf
    have : f = 1 := LinearEquiv.ext fun u => by
      have := hf u
      rw [hc, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    rw [this]
    exact one_mem _
  obtain ⟨e, he, rfl⟩ := exists_RmodN_of_mem_orbit ht H.conj_mem
    (mem_orbit_of_V_le H ht hVQ c.2 fun h => hc (Subtype.ext h))
  intro f hf
  have hf' : e⁻¹ * f * e ∈ centreGroup (Vt S g t) (aV ht) := by
    have := conj_mem_centreGroup (e := e⁻¹) hf
    rwa [inv_inv, show e⁻¹ (e (aV ht)) = aV ht from e.symm_apply_apply _] at this
  rw [← LmodN_eq_centreGroup H ht hVQ] at hf'
  have := mul_mem (mul_mem he (LmodN_le_RmodN ht hf')) (inv_mem he)
  rwa [show e * (e⁻¹ * f * e) * e⁻¹ = f by group] at this

end CFSG.LargeExtraspecial.S4
