module

public import CFSG.GF2Type.Smith1979.GammaU.Dict4
public import CFSG.GF2Type.Smith1979.GammaU.Model210

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

section

variable {i : ℕ}
  (hi : i = 0 ∨ i = 1) {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
  (H : Hyp4 S g) (C : Cons311 S g) (hw : S.width = 6) (T : ThetaInputs S g θ)

theorem exists_rows (hφ : NormTr S g θ i φ) {s : S.O} (hs : s ∈ S.Lbar g) :
    ∃ r ∈ compOf i, ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y :=
  (hφ.frame _).1 (mem_Ltr.2 ⟨s, hs, rfl⟩)

include hi hφ in
theorem mem_unitaryElts_of {s : S.O} {r : Array ℕ} (hr : r ∈ compOf i)
    (hsr : ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y) (hs1 : s ≠ 1)
    (hcomm : s * θ = θ * s) : r ∈ unitaryElts i := by
  have hcr := canon_of_mem_compOf Certificates.certificate16964 (by omega) hr
  refine mem_unitaryElts hr hcr ?_ fun x => ?_
  · rintro rfl
    apply hs1
    apply trS_injective φ
    refine LinearEquiv.ext fun y => ?_
    rw [hsr, linOfRows_idR]
    show y = trEquiv φ ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y
    rw [Subgroup.coe_one, map_one]
    rfl
  ·
    set X := trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
    have hXT : X * trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) = trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) * X := by
      have := congrArg (fun y : S.O => trEquiv φ (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) hcomm
      simpa only [Subgroup.coe_mul, map_mul] using this
    have hX : X * thetaU = thetaU * X := by
      rcases tr_theta hφ.theta with hT | hT
      · rwa [hT] at hXT
      · rw [hT] at hXT
        calc X * thetaU = thetaU * (thetaU⁻¹ * X) * thetaU := by group
          _ = thetaU * (X * thetaU⁻¹) * thetaU := by rw [hXT]
          _ = thetaU * X := by group
    have := LinearEquiv.congr_fun hX x
    simp only [LinearEquiv.mul_apply, thetaU_apply, hsr] at this
    exact this

include hi hφ H C hw T

theorem config_Mtr : ∀ r ∈ unitaryElts i, ∀ u₁ ∈ Mtr S φ, ∀ u₂ ∈ Mtr S φ,
    Viol.InFrame (compOf i) u₁ r → Viol.InFrame (compOf i) u₂ r →
      Viol.F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0)) → HasConfig i (Mtr S φ) r := by
  intro r hr u₁ hu₁ u₂ hu₂ hi₁ hi₂ hind
  obtain ⟨hrc, hne, hun⟩ := by
    simpa only [unitaryElts, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] using hr
  obtain ⟨s, hs, hsr⟩ := exists_realize hi hφ hrc
  have hcr := canon_of_mem_compOf Certificates.certificate16964 (by omega) hrc
  have hunit := unitary_spec hcr.2 hun
  have hcomm : s * θ = θ * s := comm_of_unitary hφ.theta fun x => by rw [hsr, hsr, hunit]
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hne
    refine rows_eq hcr.1 rfl hcr.2 (by decide) fun x => ?_
    rw [← hsr, linOfRows_idR, Subgroup.coe_one, map_one]
    rfl
  have h4 := four_le_finrank (theta0_mem_map_Vt H T.mem hφ.theta hcomm)
    (mem_map_Vt_of_inFrame hφ H hsr hu₁ hi₁) (mem_map_Vt_of_inFrame hφ H hsr hu₂ hi₂) hind
  rw [finrank_map_Vt] at h4
  obtain ⟨h, c1, c2, c3, c4, c5a, c5b, c5c, c6, c7⟩ := T.config s hs hs1 hcomm h4
  exact hasConfig_of_data hi hφ H C hw hrc hsr h c1 c2 c3 c4 c5a c5b c5c c6 c7

theorem canon_Mtr : ∀ m ∈ Mtr S φ, m (vecOf a0) = vecOf a0 → m ∈ gammaU := by
  intro m hm hfix
  obtain ⟨m₀, hm₀, rfl⟩ := mem_Mtr.1 hm
  have hfix' : (m₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g := by
    apply φ.injective
    rw [← trEquiv_apply_φ, hφ.base, hfix]
  exact mem_gammaU_of_conj (isom_of_mem_Mtr hφ.isom hm)
    (conj_thetaU_tr hφ.theta (T.canon m₀ hm₀ hfix'))

theorem hyp_frame : Hyp (vecOf a0) (spanOf d0) (Ltr S g φ) := by
  have hLθ : ∀ s ∈ S.Lbar g, s * θ * s⁻¹ = θ ∨ s * θ * s⁻¹ = θ⁻¹ := fun s hs =>
    T.canon s (S.Lbar_le_Mbar g hs) (Lbar_fix H hs)
  have := hyp_tr H C hw hφ.isom (Ltr_le_gammaU hφ.isom hφ.theta hLθ)
  rwa [hφ.base, hφ.dmap] at this

end

theorem Mtr_trans (φ : S.Qt ≃ₗ[ZMod 2] V12) (h : V12 ≃ₗ[ZMod 2] V12) :
    Mtr S (φ.trans h) = (Mtr S φ).map (MulAut.conj h).toMonoidHom := by
  ext l
  rw [mem_Mtr, mem_map_conj]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, mem_Mtr.2 ⟨m, hm, rfl⟩, (trEquiv_trans φ h _).symm⟩
  · rintro ⟨_, hl, rfl⟩
    obtain ⟨m, hm, rfl⟩ := mem_Mtr.1 hl
    exact ⟨m, hm, trEquiv_trans φ h _⟩

theorem NormTr.trans {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) : NormTr S g θ i (φ.trans h) where
  isom v := by rw [LinearEquiv.trans_apply, hh.mem.1, hφ.isom]
  theta := by
    rcases hφ.theta with hc | hc <;> rcases hh.mem.2 with hu | hu
    · left
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hc, hu]
    · right
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hc, hu]
    · right
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hc, hu, hu]
    · left
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hc, hu, hu, theta0_theta0_theta0]
  base := by rw [LinearEquiv.trans_apply, hφ.base, hh.fix]
  dmap := by
    rw [LinearEquiv.coe_trans, Submodule.map_comp, hφ.dmap]
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hh.d0 x).2 hx
    · intro hy
      refine ⟨h⁻¹ y, (hh.d0 _).1 ?_, apply_inv_apply h y⟩
      rwa [apply_inv_apply]
  frame l := by
    rw [Ltr_trans, mem_map_conj]
    constructor
    · rintro ⟨l', hl', rfl⟩
      exact (hh.norm l').2 ((hφ.frame l').1 hl')
    · intro hl
      refine ⟨h⁻¹ * l * h, (hφ.frame _).2 ((hh.norm _).1 ?_), by group⟩
      rwa [show h * (h⁻¹ * l * h) * h⁻¹ = l by group]

theorem false_of_thetaInputs
    (hw : S.width = 6) (hirr : ¬ S.IsReducible) (H : Hyp4 S g)
    (C : Cons311 S g) {θ : S.O} (T : ThetaInputs S g θ) : False := by
  have hLθ : ∀ s ∈ S.Lbar g, s * θ * s⁻¹ = θ ∨ s * θ * s⁻¹ = θ⁻¹ := fun s hs =>
    T.canon s (S.Lbar_le_Mbar g hs) (Lbar_fix H hs)
  obtain ⟨i, hi, φ, hφ⟩ := exists_normTr H C hw T.pow_three T.fix hLθ
  obtain ⟨s₁, hs₁, s₂, hs₂, hne, h1, h2, hc1, hc2, hd1, hd2⟩ := T.two
  obtain ⟨r₁, hr₁, hsr₁⟩ := exists_rows hφ hs₁
  obtain ⟨r₂, hr₂, hsr₂⟩ := exists_rows hφ hs₂
  have hu₁ := mem_unitaryElts_of hi hφ hr₁ hsr₁ h1 hc1
  have hu₂ := mem_unitaryElts_of hi hφ hr₂ hsr₂ h2 hc2
  have hrne : r₁ ≠ r₂ := by
    rintro rfl
    apply hne
    apply trS_injective φ
    exact LinearEquiv.ext fun y => by rw [hsr₁, hsr₂]
  have hcfg : ∀ {s : S.O} {r : Array ℕ}, s ∈ S.Lbar g → s ≠ 1 → s * θ = θ * s →
      4 ≤ finrank (ZMod 2) (Vt S g s) → r ∈ compOf i →
      (∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y) →
        HasConfig i (Mtr S φ) r := by
    intro s r hs hs1 hcomm h4 hr hsr
    obtain ⟨h, c1, c2, c3, c4, c5a, c5b, c5c, c6, c7⟩ := T.config s hs hs1 hcomm h4
    exact hasConfig_of_data hi hφ H C hw hr hsr h c1 c2 c3 c4 c5a c5b c5c c6 c7
  obtain ⟨g₀, hg₀, h4', hrep⟩ := exists_normalized hi (step4Hyp_Mtr hi hφ H T) hu₁ hu₂ hrne
    (hcfg hs₁ h1 hc1 hd1 hr₁ hsr₁) (hcfg hs₂ h2 hc2 hd2 hr₂ hsr₂)
  have hφ' := hφ.trans hg₀
  rw [← Mtr_trans] at h4' hrep
  exact false_of_model hi h4' hrep (config_Mtr hi hφ' H C hw T)
    (fun m hm => isom_of_mem_Mtr hφ'.isom hm) (canon_Mtr hi hφ' H C hw T) (irred_Mtr hirr _)
    hφ'.frame (hyp_frame hi hφ' H C hw T)

end CFSG.GF2Type.Smith1979.GammaU.Dict
