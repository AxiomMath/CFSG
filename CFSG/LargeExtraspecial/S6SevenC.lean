module

public import CFSG.LargeExtraspecial.S6SevenB
public import CFSG.LargeExtraspecial.S6Five
public import CFSG.LargeExtraspecial.S6One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem cl_mem_orbit_of_omegaCase (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {h : S.M}
    (hhV : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
  obtain ⟨Qf, hQnd, hpol, -, -, horb'⟩ := hΩ.exists_form
  have horb : ∀ v : Vt S g t, v ≠ 0 → (Qf v = 0 ↔ (v : S.Qt) ∈ orbit S g t) := fun v hv =>
    (horb' v hv).trans (mem_orbitOf_RmodN_iff H.conj_mem ht)
  set β := beta H C ht ht1 hVQ with hβ
  have hpolar : ∀ x y : Vt S g t, polar Qf x y = β x y := fun x y => by
    rw [← polarBilin_apply_apply, hpol]
  have hnd : β.Nondegenerate := beta_nondegenerate H C ht ht1 hVQ
  set c := (h : G) * g * S.z * ((h : G) * g)⁻¹ with hc
  have hcQ : c ∈ S.QG := conj_mem_QG' S h.2 H.conj_mem
  have hcz : c ≠ S.z := conj_ne_z' S h.2 H.conj_ne
  set c' : Vt S g t := ⟨S.cl c, hhV⟩ with hc'
  have hc'0 : c' ≠ 0 := fun h0 => cl_conj_z_ne_zero S hcQ hcz (congrArg Subtype.val h0)
  by_contra hcorb
  have hQc : Qf c' = 1 := zmod2_eq_one_of_ne_zero fun h0 => hcorb ((horb c' hc'0).mp h0)
  have hWc : 3 ≤ finrank (ZMod 2) (LinearMap.ker (β c')) := by
    have := finrank_ker_add_one hnd hc'0
    omega
  obtain ⟨s, hsW, hs0, hQs⟩ := exists_ne_zero_q_eq_zero Qf hWc
  obtain ⟨k, hk, hks⟩ := exists_of_mem_orbit ((horb s hs0).mp hQs) H.conj_mem
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  set b := (k : G) * g * S.z * ((k : G) * g)⁻¹ with hb
  have hbQ : b ∈ S.QG := conj_mem_QG' S k.2 H.conj_mem
  have hbz : b ≠ S.z := conj_ne_z' S k.2 H.conj_ne
  have hsb : bV htk = s := Subtype.ext hks.symm
  have hβsc : β s c' = 0 := by
    rw [hβ, beta_symm]
    exact LinearMap.mem_ker.mp hsW
  have hcPb : (c' : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
    (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk c').mp (by rw [hsb]; exact hβsc)
  have hcQb : c ∈ S.Qa ((k : G) * g) := mem_Qa_of_cl_mem hcQ (S.z_mem_Qa hbQ hbz) hcPb
  have hcl_ne : S.cl c ≠ S.cl b := fun he => by
    have : c' = s := Subtype.ext (he.trans hks.symm)
    rw [this, hQs] at hQc
    exact zero_ne_one hQc
  have hcb : c ≠ b := fun he => hcl_ne (by rw [he])
  have hcbz : c ≠ b * S.z := fun he => hcl_ne (by rw [he, S.cl_mul_z hbQ])
  obtain ⟨k₃, hk₃, y, hyQ, hyM, hyb⟩ :=
    exists_swap_of_mem_Qa hbQ hcQ hbz hcz ⟨_, rfl⟩ hcQb hcb hcbz
  have hk₃Q : k₃ * S.z * k₃⁻¹ ∈ S.QG := by
    rw [hk₃]
    exact S.QG.mul_mem hbQ hcQ
  set d : Vt S g t := s + c' with hd
  have hdcl : (d : S.Qt) = S.cl (k₃ * S.z * k₃⁻¹) := by
    rw [hk₃, S.cl_mul hbQ hcQ, hd, Submodule.coe_add, hks]
  have hQd : Qf d = 1 := by
    rw [hd, map_add_eq, hQs, hQc, hpolar, hβsc]
    decide
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hQd
    exact zero_ne_one hQd
  set yM : S.M := ⟨y, hyM⟩ with hyM'
  have hyL : S.ρ yM ∈ S.Lbar k₃ := ρ_mem_Lbar S (show (yM : G) ∈ S.L0 k₃ from ⟨hyQ, hyM⟩)
  have htrans : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa k₃),
      ((S.ρ yM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ (d : S.Qt) := by
    intro v hv
    rw [hdcl]
    exact Lbar_apply_sub_mem_span' hk₃Q hv hyL
  have hyd : ((S.ρ yM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (d : S.Qt) = d := by
    rw [hdcl]
    exact (S.mem_fixLbar.mp (S.cl_mem_fixLbar_self hk₃Q)) _ hyL
  have hV0 : ∀ v : Vt S g t, β v d = 0 → (v : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa k₃) := fun v hv =>
    mem_clSub_of_beta_eq_zero H C ht ht1 hVQ hpol horb hdcl hk₃Q hQd hv
  set K0 := LinearMap.ker (β d) with hK0
  have hK0mem : ∀ v : Vt S g t, v ∈ K0 ↔ β v d = 0 := by
    intro v
    rw [hK0, LinearMap.mem_ker, hβ, beta_symm]
  set φ : Vt S g t →ₗ[ZMod 2] S.Qt :=
    ((((S.ρ yM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp
      (Vt S g t).subtype with hφ
  have hφapp : ∀ v : Vt S g t,
      φ v = ((S.ρ yM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := fun _ => rfl
  set F := K0 ⊓ LinearMap.ker φ with hF
  have hφd : ∀ v ∈ K0, v ∉ F → φ v = d := by
    intro v hv hvF
    have h1 := htrans _ (hV0 v ((hK0mem v).mp hv))
    rw [← hφapp] at h1
    rcases mem_span_singleton_iff.mp h1 with h0 | h0
    · exact absurd ⟨hv, LinearMap.mem_ker.mpr h0⟩ hvF
    · exact h0
  have hFdim : finrank (ZMod 2) K0 ≤ finrank (ZMod 2) F + 1 := by
    refine finrank_le_finrank_add_one_of_add_mem inf_le_left fun v hv w hw hvF hwF => ?_
    refine ⟨add_mem hv hw, LinearMap.mem_ker.mpr ?_⟩
    rw [map_add, hφd v hv hvF, hφd w hw hwF, vec_add_self]
  have hK0dim : finrank (ZMod 2) K0 + 1 = finrank (ZMod 2) (Vt S g t) :=
    finrank_ker_add_one hnd hd0
  have hdF : d ∈ F := ⟨LinearMap.mem_ker.mpr (beta_isAlt H C ht ht1 hVQ d),
    LinearMap.mem_ker.mpr (by rw [hφapp, hyd, sub_self])⟩
  obtain ⟨α, hαF, β', hβF, hQα, hQβ, hαβ⟩ := exists_hyperbolic_pair hQnd (F := F) (by omega)
    hdF hQd fun v hv => by rw [hpolar]; exact (hK0mem v).mp hv.1
  rw [hpolar] at hαβ
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαβ
  have hβ0 : β' ≠ 0 := by
    rintro rfl
    simp at hαβ
  obtain ⟨k₅, hk₅, hα⟩ := exists_of_mem_orbit ((horb α hα0).mp hQα) H.conj_mem
  obtain ⟨k₆, hk₆, hβeq⟩ := exists_of_mem_orbit ((horb β' hβ0).mp hQβ) H.conj_mem
  have htk₅ := mem_Lbar_mul_of_mem_Rbar H ht hk₅
  have htk₆ := mem_Lbar_mul_of_mem_Rbar H ht hk₆
  have hnot : (k₆ : G) * g * S.z * ((k₆ : G) * g)⁻¹ ∉ S.Qa ((k₅ : G) * g) := by
    intro hmem
    have h1 : (β' : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k₅ : G) * g)) := by
      rw [hβeq]
      exact S.cl_mem_clSub ⟨(H.mul k₆).conj_mem, hmem⟩ (H.mul k₆).conj_mem
    have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hk₅ htk₅ β').mpr h1
    rw [show bV htk₅ = α from Subtype.ext hα.symm] at h2
    rw [h2] at hαβ
    exact zero_ne_one hαβ
  have hgen := Rbar_le_sup_of_omegaCase H C ht ht1 hVQ hk₅ hk₆ hnot hNo hΩ
  have hN0 := Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ
  have hinf := timmesfeld_6_5_inf H ht hk₅ hk₆ hgen hN0 C ht1 hVQ
  have hyMbar : S.ρ yM ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨yM, rfl⟩
  have hfix : ∀ v ∈ F, ((S.ρ yM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) = v := by
    intro v hv
    have := LinearMap.mem_ker.mp hv.2
    rw [hφapp, sub_eq_zero] at this
    exact this
  have hn₅ := mem_normalizer_of_fix H.conj_mem H.conj_ne hyMbar (h := k₅)
    (by rw [← hα]; exact hfix α hαF)
  have hn₆ := mem_normalizer_of_fix H.conj_mem H.conj_ne hyMbar (h := k₆)
    (by rw [← hβeq]; exact hfix β' hβF)
  have ht' : S.ρ yM * t * (S.ρ yM)⁻¹ ∈ zpowers t := by
    rw [← hinf]
    exact ⟨(mem_normalizer_iff.mp hn₅ t).mp htk₅, (mem_normalizer_iff.mp hn₆ t).mp htk₆⟩
  have htt : S.ρ yM * t * (S.ρ yM)⁻¹ = t := by
    rcases (Setting.mem_zpowers_iff_of_mul_self (mul_self_of_mem_Lbar S H.conj_mem ht)).mp ht'
      with h1 | h1
    · exfalso
      apply ht1
      calc t = (S.ρ yM)⁻¹ * (S.ρ yM * t * (S.ρ yM)⁻¹) * S.ρ yM := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hth : t ∈ S.Lbar (((yM * k : S.M) : G) * g) := by
    have h1 := conj_mem_Lbar_mul S yM htk
    rw [htt] at h1
    rwa [Subgroup.coe_mul, mul_assoc]
  have hmem := (mem_orbitOf_RmodN_iff H.conj_mem ht).mp
    (bV_mem_orbitOf H C ht ht1 hVQ hNo hΩ.not_transitive hth)
  apply hcorb
  have e : (((yM * k : S.M) : G) * g) * S.z * (((yM * k : S.M) : G) * g)⁻¹ = c := by
    have hyy : (yM : G) = y := rfl
    rw [← hyb, Subgroup.coe_mul, hyy]
    group
  rw [coe_bV, e] at hmem
  exact hmem

theorem timmesfeld_6_7 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    orbit S g t = {v | v ∈ Vt S g t ∧ ∃ x ∈ S.Mbar,
        v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} ∨
      ∃ hVQ : ¬ V S g t ≤ S.Qa g, OmegaCase H C ht ht1 hVQ ∧
        finrank (ZMod 2) (Vt S g t) = 4 := by
  have key : (∀ h : S.M, S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t) →
      orbit S g t = {v | v ∈ Vt S g t ∧ ∃ x ∈ S.Mbar,
        v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} := by
    intro hfus
    ext v
    constructor
    · intro hv
      refine ⟨orbit_subset_Vt ht H.conj_mem hv, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨x, Rbar_le_Mbar hx, rfl⟩
    · rintro ⟨hvV, x, hxM, rfl⟩
      obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hxM
      rw [ρ_cl_conj_z S h H.conj_mem] at hvV ⊢
      exact hfus h hvV
  have htr : (∀ w : Vt S g t, w ≠ 0 → ∃ e ∈ RmodN S g t, e (aV ht) = w) →
      ∀ h : S.M, S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t →
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
    intro hT h hhV
    have h0 : (⟨_, hhV⟩ : Vt S g t) ≠ 0 := fun h0 =>
      cl_conj_ne_zero H h (congrArg Subtype.val h0)
    obtain ⟨e, he, hea⟩ := hT _ h0
    exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ⟨e, he, hea⟩
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR | hL | ⟨hVQ, hSp | hA6 | hΩ | hP⟩
  ·
    refine Or.inl (key fun h hhV => ?_)
    have hfixa : ∀ x ∈ Rbar S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      intro x hx
      rw [hR] at hx
      exact (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _)
        x hx
    have hle : Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      rw [Vt_eq_span_orbit H ht, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [hfixa x hx]
      exact Submodule.mem_span_singleton_self _
    rcases mem_span_singleton_iff.mp (hle hhV) with h0 | h0
    · exact absurd h0 (cl_conj_ne_zero H h)
    · rw [h0]
      exact cl_a_mem_orbit
  · exact Or.inl (key fun h hhV => hL.mem_orbit ⟨_, hhV⟩ fun h0 =>
      cl_conj_ne_zero H h (congrArg Subtype.val h0))
  · exact Or.inl (key (htr hSp.transitive))
  · exact Or.inl (key (htr hA6.transitive))
  · by_cases h4 : finrank (ZMod 2) (Vt S g t) = 4
    · exact Or.inr ⟨hVQ, hΩ, h4⟩
    · refine Or.inl (key fun h hhV => ?_)
      have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by
        obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
        have := four_le_finrank_Vt H C ht ht1 hVQ hNo
        omega
      exact cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hhV
  · exact Or.inl (key (htr hP.transitive))

end CFSG.LargeExtraspecial.S6
