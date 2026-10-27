module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open CFSG.Fischer
open CFSG.LargeExtraspecial (pointRadical)
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open Sec3Theta Sec3Lift Census
open scoped Pointwise

namespace Sec3Res

@[expose] def resFun (s : MulAction.stabilizer OV N0) (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  epsInv (((s : OV) : V₀ ≃ₗ[F4] V₀) (epsF y))

theorem epsF_resFun (s : MulAction.stabilizer OV N0) (y : Fin 6 → ZMod 2) :
    epsF (resFun s y) = ((s : OV) : V₀ ≃ₗ[F4] V₀) (epsF y) :=
  epsF_epsInv (apply_mem_N0 s.2 (epsF_mem_N0 y))

@[expose] def resLin (s : MulAction.stabilizer OV N0) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := resFun s
  map_add' y y' := epsF_injective (by
    rw [epsF_resFun, epsF_add, epsF_add, epsF_resFun, epsF_resFun, map_add])
  map_smul' c y := epsF_injective (by
    rw [RingHom.id_apply, epsF_resFun, epsF_smul, epsF_smul, epsF_resFun, map_smul])

theorem resLin_apply (s : MulAction.stabilizer OV N0) (y : Fin 6 → ZMod 2) :
    resLin s y = resFun s y := rfl

theorem resLin_mul (s s' : MulAction.stabilizer OV N0) :
    resLin (s * s') = resLin s ∘ₗ resLin s' :=
  LinearMap.ext fun y => epsF_injective (by
    rw [LinearMap.comp_apply, resLin_apply, resLin_apply, resLin_apply, epsF_resFun, epsF_resFun,
      epsF_resFun]
    rfl)

theorem resLin_one : resLin 1 = LinearMap.id :=
  LinearMap.ext fun y => epsF_injective (by rw [resLin_apply, epsF_resFun]; rfl)

@[expose] noncomputable def res :
    MulAction.stabilizer OV N0 →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) where
  toFun s := LinearEquiv.ofLinearMap (resLin s) (resLin s⁻¹)
    (by rw [← resLin_mul, mul_inv_cancel, resLin_one])
    (by rw [← resLin_mul, inv_mul_cancel, resLin_one])
  map_one' := LinearEquiv.ext fun y => by
    change resLin 1 y = y
    rw [resLin_one, LinearMap.id_apply]
  map_mul' s s' := LinearEquiv.ext fun y => by
    change resLin (s * s') y = resLin s (resLin s' y)
    rw [resLin_mul, LinearMap.comp_apply]

theorem epsF_res (s : MulAction.stabilizer OV N0) (y : Fin 6 → ZMod 2) :
    epsF (res s y) = ((s : OV) : V₀ ≃ₗ[F4] V₀) (epsF y) :=
  epsF_resFun s y

theorem qplus_res (s : MulAction.stabilizer OV N0) (y : Fin 6 → ZMod 2) :
    Sec3Coord.qplus (res s y) = Sec3Coord.qplus y := by
  apply toF4_injective
  rw [← Q₀_epsF, ← Q₀_epsF, epsF_res, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup s.1.2]

theorem res_ofArr {M : Array ℕ} (h : isomOK M = true) (hM : f2Mat M = true) :
    res ⟨ofArr M h, mem_stab_of_f2 h hM⟩ = f2Equiv M hM h :=
  LinearEquiv.ext fun _ => rfl

theorem f2Map_tau (hM : f2Mat tauM = true) (y : Fin 6 → ZMod 2) :
    f2Map tauM hM y = y + y 1 • Pi.single 0 1 := by
  have hcols : ∀ k : Fin 6, epsInv (decodeV tauM[k.val]!) =
      ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]] k := by
    intro k
    fin_cases k <;> decide
  rw [f2Map_eq_of_cols hM hcols]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_six]

end Sec3Res

open Sec3Res

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem hN_mem_stab (n : ↥(nSHat Q₀ Q Zs)) (hnN : (n : G) ∈ H.xsub.N) :
    hT.hN n ∈ MulAction.stabilizer OV N0 :=
  hT.smul_N0_of_conj n fun u hu => (mem_normalizer_iff.mp (H.mem_normalizer_U hnN n.2.1) u).mp hu

theorem coord_ρG (n : ↥(nSHat Q₀ Q Zs)) (hnN : (n : G) ∈ H.xsub.N) {v : H.xsub.Qt}
    (hv : polar H.xsub.q (H.xsub.cl e) v = 0) :
    Sec3Coord.coord H.xsub.q b (H.ρG ⟨n, hnN⟩ v) =
      res ⟨hT.hN n, hT.hN_mem_stab n hnN⟩ (Sec3Coord.coord H.xsub.q b v) := by
  obtain ⟨u, huQ, rfl⟩ := H.xsub.exists_cl v
  have huU : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
    rw [H.centralizer_Zs_eq_clPre hT.hZQ hT.he hT.hez]
    refine ⟨huQ, mem_perp.mpr fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, hv, smul_zero]
  have hnU : (n : G) * u * (n : G)⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    (mem_normalizer_iff.mp (H.mem_normalizer_U hnN n.2.1) u).mp huU
  have hcl : H.xsub.cl ((n : G) * u * (n : G)⁻¹) = H.ρG ⟨n, hnN⟩ (H.xsub.cl u) :=
    (H.ρG_cl ⟨n, hnN⟩ huQ).symm
  apply epsF_injective
  rw [epsF_res, ← hcl, ← hT.theta_U hnU, ← hT.theta_U huU]
  exact (hT.hN_theta n (H.U_le_SHat hT.hQF huU)).symm

theorem mem_span_of_coord_eq_zero {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hc : Sec3Coord.coord H.xsub.q b w = 0) : w ∈ (ZMod 2) ∙ H.xsub.cl e := by
  have h1 : w ∈ perp H.xsub.q (perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl e)) := by
    refine mem_perp.mpr fun x hx => ?_
    have hxa : polar H.xsub.q (H.xsub.cl e) x = 0 :=
      (mem_perp.mp hx) _ (Submodule.mem_span_singleton_self _)
    have hwx : polar H.xsub.q (H.xsub.cl e) (w + x) = 0 := by
      rw [polar_add_right, hw, hxa, add_zero]
    have e1 := hT.frame_q _ hwx
    have e2 := hT.frame_q _ hw
    have e3 := hT.frame_q _ hxa
    rw [(Sec3Coord.coord H.xsub.q b).map_add, hc, zero_add] at e1
    rw [hc] at e2
    have hq0 : Sec3Coord.qplus 0 = 0 := by simp [Sec3Coord.qplus]
    rw [polar_comm, polar, e1, e2, e3, hq0]
    ring
  have h2 : w ∈ LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q)
      (LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q) ((ZMod 2) ∙ H.xsub.cl e)) := h1
  rwa [LinearMap.BilinForm.orthogonal_orthogonal H.xsub.q_nondegenerate
    (CFSG.LargeExtraspecial.OrthoF2.isRefl_polarBilin H.xsub.q)] at h2

theorem gam_res_mem_omega (hρΩ : H.ρG.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate)
    (n : ↥(nSHat Q₀ Q Zs)) (hnN : (n : G) ∈ H.xsub.N) :
    Sec3Coord.gam hT.frame (res ⟨hT.hN n, hT.hN_mem_stab n hnN⟩) ∈
      omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  set gs := res ⟨hT.hN n, hT.hN_mem_stab n hnN⟩ with hgs
  set γ := Sec3Coord.gam hT.frame gs with hγ
  set ρn := H.ρG ⟨n, hnN⟩ with hρn
  set a := H.xsub.cl e with ha
  have ha0 : a ≠ 0 := H.cl_ne_zero hT.hZQ hT.he hT.hez
  have hqa : H.xsub.q a = 0 := H.q_cl_eq_zero hT.hZQ hT.he
  have hρO : ρn ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := (H.xsub.ρ _).2
  have hγO : γ ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q :=
    Sec3Coord.gam_mem_orthogonalGroup hT.frame fun y => qplus_res _ y
  have hca : Sec3Coord.coord H.xsub.q b a = 0 := hT.coord_cl_e
  have hγa : γ a = a := Sec3Coord.gam_apply_of_eq hT.frame (by rw [hca, map_zero])
  have hγia : γ⁻¹ a = a := by
    conv_lhs => rw [← hγa]
    exact γ.symm_apply_apply a
  have hρa : ρn a = a := H.ρG_cl_z₂ hT.hZQ hT.he n.2.1
  set tt := ρn * γ⁻¹ with htt
  have htO : tt ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := mul_mem hρO (inv_mem hγO)
  have hta : tt a = a := by rw [htt, LinearEquiv.mul_apply, hγia, hρa]
  have htrad : tt ∈ pointRadical H.xsub.q a := by
    refine ⟨htO, hta, fun w hw => ?_, fun v => ?_⟩
    · set y := γ⁻¹ w with hy
      have hya : polar H.xsub.q a y = 0 := by
        rw [← hγia, hy, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (inv_mem hγO), hw]
      have hγy : γ y = w := γ.apply_symm_apply w
      have hcy : gs (Sec3Coord.coord H.xsub.q b y) = Sec3Coord.coord H.xsub.q b w := by
        rw [← hγy, hγ, Sec3Coord.coord_gam]
      have htw : tt w = ρn y := rfl
      have hcρ := hT.coord_ρG n hnN hya
      have hρya : polar H.xsub.q a (ρn y) = 0 := by
        rw [← hρa, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hρO, hya]
      refine hT.mem_span_of_coord_eq_zero ?_ ?_
      · rw [polar_sub_right, htw, hρya, hw, sub_zero]
      · rw [map_sub, htw, hcρ, ← hgs, hcy, sub_self]
    · have h1 : polar H.xsub.q a (tt v) = polar H.xsub.q a v := by
        calc polar H.xsub.q a (tt v) = polar H.xsub.q (tt a) (tt v) := by rw [hta]
          _ = polar H.xsub.q a v :=
            TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO a v
      rw [polar_sub_right, h1, sub_self]
  have htΩ := CFSG.LargeExtraspecial.S2.pointRadical_le_omegaGroup H.xsub.q_nondegenerate ha0 hqa
    htrad
  have hρΩ' : ρn ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate := hρΩ ⟨_, rfl⟩
  have e1 : γ = tt⁻¹ * ρn := by rw [htt]; group
  rw [e1]
  exact mul_mem (inv_mem htΩ) hρΩ'

noncomputable def psi : MulAction.stabilizer OV N0 →* (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  (Sec3Coord.gam hT.frame).comp res

section Census

theorem psi_mem_omega {s : MulAction.stabilizer OV N0} (hs : (s : OV) ∈ Lc) :
    hT.psi s ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  have hLs : Ls ≤ (omegaGroup H.xsub.q H.xsub.q_nondegenerate).comap hT.psi := by
    rw [Ls, closure_le]
    have hgen : ∀ {M : Array ℕ} (hI : isomOK M = true) (hM : f2Mat M = true) {k : ℕ},
        Odd k → toLin M ^ k = 1 →
          hT.psi ⟨ofArr M hI, mem_stab_of_f2 hI hM⟩ ∈
            omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
      intro M hI hM k hk hpow
      change Sec3Coord.gam hT.frame (res ⟨ofArr M hI, mem_stab_of_f2 hI hM⟩) ∈ _
      rw [res_ofArr hI hM]
      refine mem_omegaGroup_of_pow_eq_one H.xsub.q_nondegenerate
        (Sec3Coord.gam_mem_orthogonalGroup hT.frame fun y => qplus_f2Map hM hI y) hk ?_
      rw [← map_pow, f2Equiv_pow_eq_one hM hI hpow, map_one]
    rintro _ (rfl | rfl)
    · exact hgen isom_g1 f2_g1 (by decide) toLin_g1_pow
    · exact hgen isom_g2 f2_g2 (by decide) toLin_g2_pow
  rw [← map_Ls] at hs
  obtain ⟨s', hs', hss'⟩ := hs
  have e1 : s' = s := Subtype.ext hss'
  exact hLs (e1 ▸ hs')

theorem psi_tau_not_mem :
    hT.psi ⟨Tau, Tau_mem_stab⟩ ∉ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  intro h
  have hτ : hT.psi ⟨Tau, Tau_mem_stab⟩ = Sec3Coord.gam hT.frame (f2Equiv tauM f2_tau isom_tau) :=
    congrArg (Sec3Coord.gam hT.frame) (res_ofArr isom_tau f2_tau)
  have hsub : ∀ v, Sec3Coord.gam hT.frame (f2Equiv tauM f2_tau isom_tau) v - v =
      Sec3Coord.coord H.xsub.q b v 1 • b 0 := by
    intro v
    rw [Sec3Coord.gam_apply, f2Equiv_apply, Sec3Res.f2Map_tau, map_add, map_smul,
      Sec3Coord.vec_apply (b := b) (Pi.single 0 1)]
    simp [Pi.single_apply]
    abel
  have hcomm : commSpace (hT.psi ⟨Tau, Tau_mem_stab⟩) = (ZMod 2) ∙ b 0 := by
    rw [hτ]
    apply le_antisymm
    · intro w hw
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
      rw [hsub]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine mem_commSpace.mpr ⟨b 1, ?_⟩
      rw [hsub, Sec3Coord.coord_apply, hT.frame.polar_eq]
      simp [Sec3Coord.piF]
  have hb0 : b 0 ≠ 0 := by
    intro h0
    have := hT.frame.q_eq 0
    rw [h0, map_zero] at this
    exact absurd this (by decide)
  have h1 := (mem_omegaGroup.mp h).2
  rw [hcomm, finrank_span_singleton hb0] at h1
  exact absurd h1 (by decide)

theorem hN_mem_Lc (hN₁ : nSHat Q₀ Q Zs ≤ H.xsub.N)
    (hρΩ : H.ρG.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate) (n : ↥(nSHat Q₀ Q Zs)) :
    (hT.hN n : OV) ∈ Lc := by
  have hs := hT.hN_mem_stab n (hN₁ n.2)
  rcases mem_or_of_stab hs with h | ⟨l, hl, hlt⟩
  · exact h
  exfalso
  have e1 : (⟨hT.hN n, hs⟩ : MulAction.stabilizer OV N0) =
      ⟨l, Lc_le_stab hl⟩ * ⟨Tau, Tau_mem_stab⟩ := Subtype.ext hlt
  have hΩn := hT.gam_res_mem_omega hρΩ n (hN₁ n.2)
  have hΩl := hT.psi_mem_omega (s := ⟨l, Lc_le_stab hl⟩) hl
  change hT.psi ⟨hT.hN n, hs⟩ ∈ _ at hΩn
  rw [e1, map_mul] at hΩn
  apply hT.psi_tau_not_mem
  have e2 : hT.psi ⟨Tau, Tau_mem_stab⟩ = (hT.psi ⟨l, Lc_le_stab hl⟩)⁻¹ *
      (hT.psi ⟨l, Lc_le_stab hl⟩ * hT.psi ⟨Tau, Tau_mem_stab⟩) := by group
  rw [e2]
  exact mul_mem (inv_mem hΩl) hΩn

end Census

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81
