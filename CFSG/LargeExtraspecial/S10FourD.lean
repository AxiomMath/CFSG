module

public import CFSG.LargeExtraspecial.S10FourC
public import CFSG.LargeExtraspecial.S5Fus
public import CFSG.LargeExtraspecial.S10FourA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem mem_span_singleton_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {c w : V} :
    w ∈ (ZMod 2) ∙ c ↔ w = 0 ∨ w = c := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem exists_mul_of_two_fix {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {H : Type*}
    [Group H] (φ : H →* (V ≃ₗ[ZMod 2] V)) {L : Subgroup H} {c u u' : V}
    (hc : ∀ l ∈ L, φ l c = c) (hu : ∀ l ∈ L, φ l u - u ∈ (ZMod 2) ∙ c)
    (hu' : ∀ l ∈ L, φ l u' - u' ∈ (ZMod 2) ∙ c) {l₀ : H} (hl₀ : l₀ ∈ L)
    (hmove : φ l₀ (u + u') ≠ u + u') {l : H} (hl : l ∈ L) :
    ∃ l₁ ∈ L, ∃ l₂ ∈ L, l = l₁ * l₂ ∧ φ l₁ u = u ∧ φ l₂ u' = u' := by
  have hcase : ∀ x ∈ L, ∀ w, φ x w - w ∈ (ZMod 2) ∙ c → φ x w = w ∨ φ x w = w + c := by
    intro x _ w hw
    rcases mem_span_singleton_zmod2.mp hw with h | h
    · left; exact sub_eq_zero.mp h
    · right; rw [← h]; abel
  have h2c : c + c = 0 := by
    rw [← two_smul (ZMod 2) c, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  by_cases h1 : φ l u = u
  · exact ⟨l, hl, 1, one_mem _, (mul_one l).symm, h1, by rw [map_one]; rfl⟩
  by_cases h2 : φ l u' = u'
  · exact ⟨1, one_mem _, l, hl, (one_mul l).symm, by rw [map_one]; rfl, h2⟩
  have hlu : φ l u = u + c := (hcase l hl u (hu l hl)).resolve_left h1
  have hlu' : φ l u' = u' + c := (hcase l hl u' (hu' l hl)).resolve_left h2
  obtain ⟨s, hs, hsu, hsu'⟩ : ∃ s ∈ L, φ s u = u + c ∧ φ s u' = u' := by
    rcases hcase l₀ hl₀ u (hu l₀ hl₀) with h3 | h3 <;>
      rcases hcase l₀ hl₀ u' (hu' l₀ hl₀) with h4 | h4
    · exact absurd (by rw [map_add, h3, h4]) hmove
    · refine ⟨l * l₀, mul_mem hl hl₀, ?_, ?_⟩
      · rw [map_mul, LinearEquiv.mul_apply, h3, hlu]
      · rw [map_mul, LinearEquiv.mul_apply, h4, map_add, hlu', hc l hl, add_assoc, h2c,
          add_zero]
    · exact ⟨l₀, hl₀, h3, h4⟩
    · exact absurd (by
        rw [map_add, h3, h4, show u + c + (u' + c) = u + u' + (c + c) by abel, h2c,
          add_zero]) hmove
  refine ⟨l * s, mul_mem hl hs, s⁻¹, inv_mem hs, by group, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, hsu, map_add, hlu, hc l hl, add_assoc, h2c, add_zero]
  · rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hsu']

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Lbar_mul_facts (X : Hyp10 S g t) (h : S.M) :
    (∀ l ∈ S.Lbar ((h : G) * g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∧
    (∀ l ∈ S.Lbar ((h : G) * g), ∀ w ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∧
    (∀ w, w ∉ (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) →
      ∃ l ∈ S.Lbar ((h : G) * g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) := by
  have H' := X.H.mul h
  refine ⟨fun l hl => ?_, fun l hl w hw => Lbar_apply_sub_mem_span' H'.conj_mem hw hl,
    fun w hw => ?_⟩
  · have hmem : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ fixSub S (S.Lbar ((h : G) * g)) := by
      rw [H'.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact hmem l hl
  · by_contra hcon
    push Not at hcon
    apply hw
    rw [← H'.fixSub_eq]
    exact fun l hl => hcon l hl

omit [Finite G] in
theorem mem_Qa_of_cl_mem' {g' c : G} (hz : S.z ∈ S.Qa g') (hcQ : c ∈ S.QG)
    (hc : S.cl c ∈ S.clSub (S.QG ⊓ S.Qa g')) : c ∈ S.Qa g' := by
  obtain ⟨x, hx, hxQ, hxc⟩ := S.mem_clSub_iff.mp hc
  rcases (S.cl_eq_cl_iff hxQ hcQ).mp hxc with h | h
  · rw [h]; exact hx.2
  · rw [h]; exact mul_mem hx.2 hz

theorem cl_mem_clSub_of_beta (X : Hyp10 S g t) {h k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hc : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk) ⟨_, hc⟩ = 0)
    (hne : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≠ (orbV X.haQ X.ht hk : S.Qt)) :
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
  have hcQ : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S h.2 X.haQ
  have hkQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 X.haQ
  have h1 := (beta_orbV_eq_zero_iff X hk _).mp hβ
  have h2 := mem_Qa_of_cl_mem' (S.z_mem_Qa_of_mem_QG rfl hkQ (conj_ne_z' S k.2 X.H.conj_ne))
    hcQ h1
  have h3 := S.mem_Qa_symm (fun e => hne (by rw [coe_orbV, ρ_cl_conj_z S k X.haQ, e])) h2
  exact S.cl_mem_clSub ⟨hkQ, h3⟩ hkQ

theorem StronglyClosedL.mem_Lbar_of_cl_mem_Vt (hSC : StronglyClosedL S g t) (X : Hyp10 S g t)
    (F : Frame X) {h : S.M} (hc : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t) :
    t ∈ S.Lbar ((h : G) * g) := by
  have haQ := X.haQ
  have hcQ : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S h.2 haQ
  have hcz : (h : G) * g * S.z * ((h : G) * g)⁻¹ ≠ S.z := conj_ne_z' S h.2 X.H.conj_ne
  have hv0 : (⟨_, hc⟩ : Vt S g t) ≠ 0 := fun h0 =>
    cl_conj_z_ne_zero S hcQ hcz (congrArg Subtype.val h0)
  by_cases hvo : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t
  · obtain ⟨k, hk, hck⟩ := exists_of_mem_orbit hvo haQ
    rw [Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 haQ) (conj_ne_z' S k.2 X.H.conj_ne) hcQ hck]
    exact mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  obtain ⟨k₁, k₂, hk₁, hk₂, h12, h1v, h2v⟩ := F.exists_pair_perp hv0 hvo
  have horb : ∀ {k : S.M} (hk : S.ρ k ∈ Rbar S g t), (orbV haQ X.ht hk : S.Qt) ∈ orbit S g t :=
    fun {k} hk => ⟨S.ρ k, hk, coe_orbV haQ X.ht hk⟩
  have hne : ∀ {k : S.M} (hk : S.ρ k ∈ Rbar S g t),
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≠ (orbV haQ X.ht hk : S.Qt) :=
    fun {k} hk e => hvo (e ▸ horb hk)
  have hu₁ := cl_mem_clSub_of_beta X hk₁ hc h1v (hne hk₁)
  have hu₂ := cl_mem_clSub_of_beta X hk₂ hc h2v (hne hk₂)
  obtain ⟨hfixc, htrans, hmove⟩ := Lbar_mul_facts X h
  have hcoe : ∀ {k : S.M} (hk : S.ρ k ∈ Rbar S g t),
      (orbV haQ X.ht hk : S.Qt) = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) :=
    fun {k} hk => by rw [coe_orbV, ρ_cl_conj_z S k haQ]
  have hsum : S.cl ((k₁ : G) * g * S.z * ((k₁ : G) * g)⁻¹) +
      S.cl ((k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹) ∉
        (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    intro hmem
    rcases mem_span_singleton_zmod2.mp hmem with h0 | h0
    · have e : orbV haQ X.ht hk₂ = orbV haQ X.ht hk₁ := Subtype.ext (by
        rw [hcoe, hcoe]
        exact (neg_eq_of_add_eq_zero_right h0).symm.trans (ZModModule.neg_eq_self _))
      rw [e, (beta_isAlt X.H X.C X.ht X.ht1 X.hVQ) _] at h12
      exact zero_ne_one h12
    · have e : orbV haQ X.ht hk₁ + orbV haQ X.ht hk₂ = ⟨_, hc⟩ := Subtype.ext (by
        rw [Submodule.coe_add, hcoe, hcoe]
        exact h0)
      have h3 := congrArg (beta X.H X.C X.ht X.ht1 X.hVQ (orbV haQ X.ht hk₁)) e
      rw [map_add, (beta_isAlt X.H X.C X.ht X.ht1 X.hVQ) _, h12, h1v, zero_add] at h3
      exact one_ne_zero h3
  obtain ⟨l₀, hl₀, hl₀m⟩ := hmove _ hsum
  have hfixk : ∀ {k : S.M} (hk : S.ρ k ∈ Rbar S g t), ∀ x ∈ S.Lbar ((h : G) * g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) → x * t = t * x := by
    intro k hk x hx hfix
    have hxM : x ∈ S.Mbar := S.Lbar_le_Mbar _ hx
    have hN := mem_normalizer_of_fix haQ X.H.conj_ne hxM hfix
    have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxM
    have h1 := hSC.eq_of_mem htk ((mem_normalizer_iff.mp hN t).mp htk)
    calc S.ρ y * t = S.ρ y * t * (S.ρ y)⁻¹ * S.ρ y := by group
      _ = t * S.ρ y := by rw [h1]
  have hcomm : ∀ x ∈ S.Lbar ((h : G) * g), x * t = t * x := by
    intro x hx
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, h1, h2⟩ := exists_mul_of_two_fix S.O.subtype hfixc
      (fun l hl => htrans l hl _ hu₁) (fun l hl => htrans l hl _ hu₂) hl₀ hl₀m hx
    have c1 := hfixk hk₁ l₁ hl₁ h1
    have c2 := hfixk hk₂ l₂ hl₂ h2
    calc l₁ * l₂ * t = l₁ * (l₂ * t) := by group
      _ = l₁ * (t * l₂) := by rw [c2]
      _ = (l₁ * t) * l₂ := by group
      _ = t * (l₁ * l₂) := by rw [c1]; group
  have hxL : S.ρ h * t * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := conj_mem_Lbar_mul S h X.ht
  have hmM : (S.ρ h)⁻¹ ∈ S.Mbar := inv_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hH' := X.H.mul h
  obtain ⟨n, -, hnN, hn⟩ := S5.exists_mem_normalizer_conj hH' (X.C.mul h) hmM
    (fun l hl => Lbar_comm S hH'.conj_mem hxL hl) (fun l hl => by
      rw [show (S.ρ h)⁻¹ * (S.ρ h * t * (S.ρ h)⁻¹) * (S.ρ h)⁻¹⁻¹ = t by group]
      exact (hcomm l hl).symm)
  rw [show (S.ρ h)⁻¹ * (S.ρ h * t * (S.ρ h)⁻¹) * (S.ρ h)⁻¹⁻¹ = t by group] at hn
  rw [hn]
  exact (mem_normalizer_iff.mp hnN _).mp hxL

end CFSG.LargeExtraspecial.S10
