module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Iface
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Elt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Th

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s11s_ctx_swap [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : Sec11Ctx G t L S z K2 K1 T R :=
  { toSec10Ctx := hctx.toSec10Ctx.swap
    hyp := hctx.hyp
    sylowT := hctx.sylowT
    S_le := hctx.S_le
    sylowR := by rw [sec11_secQ_swap]; exact hctx.sylowR
    T_le := hctx.T_le }

theorem s11s_Q_pow {Ki : Subgroup G} (e : Nonempty (↥Ki ≃* SL23)) :
    ∀ g ∈ Ki, g ^ 4 = 1 → g ∈ twoCoreIn Ki := by
  obtain ⟨e⟩ := e
  intro g hg hg4
  rw [mem_twoCoreIn_iff_pCore hg]
  have h4 : (e ⟨g, hg⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have h : (⟨g, hg⟩ : ↥Ki) ^ 4 = 1 := Subtype.ext (by simpa using hg4)
    rw [h, map_one]
  have hmem : e ⟨g, hg⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [sl23_pCore_eq_Q8, mem_sl23Q8]
    exact h4
  rw [← CFSG.pCore_map_iso 2 e] at hmem
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
  have hy' : y = ⟨g, hg⟩ := e.injective hye
  rwa [hy'] at hy

theorem s11s_orderOf_four_of_isD8 {P : Subgroup G} (h : IsD8 P) : ∃ w ∈ P, orderOf w = 4 := by
  obtain ⟨e⟩ := h
  refine ⟨((e.symm (DihedralGroup.r 1) : ↥P) : G), (e.symm (DihedralGroup.r 1)).2, ?_⟩
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e]
  simp

theorem s11s_a_swap_K {a : G} {K1 K2 : Subgroup G} (ha : a * a = 1)
    (hsw : CFSG.conjugate K1 a = K2) :
    (∀ g ∈ K1, a * g * a⁻¹ ∈ K2) ∧ (∀ g ∈ K2, a * g * a⁻¹ ∈ K1) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hsw' : K1.map (MulAut.conj a⁻¹).toMonoidHom = K2 := hsw
  constructor
  · intro g hg
    have h := Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hg
    rw [hsw'] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv, inv_inv] using h
  · intro g hg
    rw [← hsw'] at hg
    obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp hg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hgg'
    have h : a * g * a⁻¹ = g' := by rw [← hgg']; group
    rw [h]
    exact hg'

theorem s11s_dih_of [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, g ∉ T ⊔ secD K1 K2 R →
      secD K1 K2 R = zpowers t ⊔ zpowers (g * t * g⁻¹) ∧ ∃ w ∈ secCTQ K1 K2 T, orderOf w = 4 := by
  have h112 : Asc82Lemma112 :=
    asc82Lemma112_of hp (asc82Lemma111N_of hp (asc82Step111T_of hp))
  intro g hg hgT
  have hD8 : IsD8 (secCTQ K1 K2 T) := by
    rcases h112 G t L S z K1 K2 T R hctx with ⟨hA6, -⟩ | ⟨-, -, -, -, hD8, -⟩
    · exfalso
      have hRT : R = T := asc82Lemma115b_of hp h112 G t L S z K1 K2 T R hctx hA6
      exact hgT (Subgroup.mem_sup_left (hRT ▸ hg))
    · exact hD8
  have hTR : T ≤ R := hctx.T_le
  have hDR : secD K1 K2 R ≤ R := inf_le_right
  have hSR : S ≤ R := hctx.S_le.trans hTR
  have hRQ : R ≤ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1
  have hRD : ∀ g ∈ R, ∀ d ∈ secD K1 K2 R, g * d * g⁻¹ ∈ secD K1 K2 R := fun g hg d hd =>
    (Subgroup.mem_normalizer_iff.mp (sec11c_normalizer_D hRQ hg) d).mp hd
  have hCT : ∀ c ∈ R, c * t = t * c → c ∈ T := fun c hc hct =>
    hctx.S_le (sec11L114_cent_le hctx.sylow hctx.sylowR.2.1 hSR hc hct)
  have hz : ∀ g : G, g * t * g⁻¹ ≠ z := fun g h =>
    sec10_not_conj_z hp.s3.l37 hctx.toSec10Ctx g (by rw [← h]; group)
  obtain ⟨Y, hCl⟩ := sec11d_cl hp h112 hctx (sec11d_big hp hctx hD8)
  obtain ⟨-, hgen⟩ := sec11d_R_side hDR hRD hCT hz hCl
  exact ⟨hgen g hg hgT, s11s_orderOf_four_of_isD8 hD8⟩

theorem s11s_ctx_of [Finite G] (hp : Asc82Pre11) (hT : Asc82Step1110Type) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∃ (ρ : ↥R →* MulAut ↥(K1 ⊔ K2)) (a x : G), S11sCtx t z K1 K2 T R ρ a x := by
  have hs := sec11d_set hp hctx
  obtain ⟨ρ, hρ⟩ := sec11d_exists_rho hs.split (sec11d_pair_le hp hctx) hs.RN hs.K0_eq
  obtain ⟨a, x, hax⟩ := asc82Lemma113_of hp G t L S z K1 K2 T R hctx
  have hf := hp.facts
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hcomm : ⁅K1, K2⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (sec10Z_comm hf.pockets5 hpsp hctx.toSec10Ctx u hu v hv).symm
  obtain ⟨e1, e2⟩ := sec10KS_equiv hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx
  have hmain : K1 ⊓ K2 = zpowers z :=
    (sec10KS_main hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx).2.2
  obtain ⟨hta, htaa⟩ := sec11_a_T hp hax
  obtain ⟨hasw, hasw'⟩ := s11s_a_swap_K htaa hax.swap
  obtain ⟨-, -, hTK0, -⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  obtain ⟨-, -, -, -, -, -, -, -, hQS⟩ := sec11L114_data hp hctx
  have hWD := sec11d_pair_le hp hctx
  refine ⟨ρ, a, x,
    { rho := hρ
      set := hs
      QKD := sec11d_Q_le_KD hs
      RQ := hctx.sylowR.1
      pair := K5.sl23Pair_of_commuting K1 K2 hcomm e1 e2
      q8 := sec11L1110_q8pair hp hctx.toSec10Ctx
      Q_eq := sec10KS_twoCore_sup hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx
      Q1_pow := s11s_Q_pow e1
      Q2_pow := s11s_Q_pow e2
      inf := fun u h1 h2 => hmain ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩
      t_D := hWD (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      z_D := hWD (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      t_sq := (sec11_invols hctx.toSec10Ctx).1
      R_H := sec11_R_le_H hp hctx
      T_R := hctx.T_le
      Q_T := hQS.trans hctx.S_le
      T_N := hTK0
      D2 := hctx.sylowR.2.1.to_le inf_le_right
      a_T := hta
      a_sq := htaa
      a_swap := hasw
      a_swap' := hasw'
      a_CTQ := hax.a_comm
      x_T := hax.x_mem
      x_out1 := hax.x_out1
      x_out2 := hax.x_out2
      gen := hax.gen
      dih := s11s_dih_of hp hctx
      star := fun h hh h' hh' hc => sec11L1110_comm hp hT hctx hh hh' hc }⟩

end CFSG.OddStandard.SmallF3.Omega
