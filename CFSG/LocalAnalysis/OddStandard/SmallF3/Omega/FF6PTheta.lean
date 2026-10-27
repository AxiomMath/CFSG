module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem ff6p_commute_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    x * (l : G) = (l : G) * x ↔
      ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ (ff6mPhi e l) =
        ffOmegaToSim hQ (ff6mPhi e l) * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  let x' : ProjSim Q := ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩
  have hs : InducesViaP L (Subgroup.center ↥L) hQ e x x' :=
    ffTheta6P_induces hQ hdim hsgn e ⟨x, hxN⟩
  have hiff := ff_phi_mem_fix_iff hQ h5 hz e hs l
  have hphi : ffPhi hz e l = ff6mPhi e l := by rw [ffPhi_apply, ff6mPhi_apply]
  rw [← hiff, hphi, ffFix, mem_fixSub_iff]
  constructor
  · intro h
    have h1 := congrArg (ffOmegaToSim hQ) h
    rw [ff_omegaToSim_act] at h1
    calc x' * ffOmegaToSim hQ (ff6mPhi e l)
        = (x' * ffOmegaToSim hQ (ff6mPhi e l) * x'⁻¹) * x' := by group
      _ = ffOmegaToSim hQ (ff6mPhi e l) * x' := by rw [h1]
  · intro h
    apply ffOmegaToSim_injective hQ
    rw [ff_omegaToSim_act, h, mul_assoc, mul_inv_cancel, mul_one]

theorem ff6p_commute_img_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {B : Subgroup G} (hBL : B ≤ L) :
    (∀ b ∈ B, x * b = b * x) ↔
      ∀ w ∈ ffImg (ff6mPhi e) B,
        ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ w =
          ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
  constructor
  · intro hcomm w hw
    obtain ⟨l, hlB, hlw⟩ := mem_ffImg_iff.mp hw
    have h1 := (ff6p_commute_iff hQ hdim hsgn hz e hxN l).mp (hcomm (l : G) hlB)
    rwa [hlw] at h1
  · intro hcomm b hb
    let l : ↥L := ⟨b, hBL hb⟩
    have hw : ff6mPhi e l ∈ ffImg (ff6mPhi e) B :=
      mem_ffImg_iff.mpr ⟨l, hb, rfl⟩
    exact (ff6p_commute_iff hQ hdim hsgn hz e hxN l).mpr (hcomm _ hw)

theorem ff6p_commute_normalizer_iff (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {B : Subgroup G} (hBL : B ≤ L) :
    (∀ n ∈ L ⊓ Subgroup.normalizer (B : Set G), x * n = n * x) ↔
      ∀ w ∈ Subgroup.normalizer (ffImg (ff6mPhi e) B : Set ↥(omegaProj hQ)),
        ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ w =
          ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
  have hΦ : (ffPhi hz e).toMonoidHom = ff6mPhi e := ff6p_ffPhi_eq hQ hz e
  have hff : ∀ l : ↥L, ffPhi hz e l = ff6mPhi e l := fun l => by
    rw [ffPhi_apply, ff6mPhi_apply]
  constructor
  · intro hcomm w hw
    obtain ⟨l, hl⟩ := ff6mPhi_surjective e w
    have hw' : ffPhi hz e l ∈
        Subgroup.normalizer (ffImg (ffPhi hz e).toMonoidHom B : Set ↥(omegaProj hQ)) := by
      rw [hff l, hΦ, hl]
      exact hw
    have hnorm : (l : G) ∈ Subgroup.normalizer (B : Set G) :=
      (ffIso_mem_normalizer_iff (ffPhi hz e) hBL l).mpr hw'
    have hmem : (l : G) ∈ L ⊓ Subgroup.normalizer (B : Set G) :=
      Subgroup.mem_inf.mpr ⟨l.2, hnorm⟩
    have h1 := (ff6p_commute_iff hQ hdim hsgn hz e hxN l).mp (hcomm _ hmem)
    rwa [hl] at h1
  · intro hcomm n hn
    obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.mp hn
    let l : ↥L := ⟨n, hnL⟩
    have hΦl : ffPhi hz e l ∈
        Subgroup.normalizer (ffImg (ffPhi hz e).toMonoidHom B : Set ↥(omegaProj hQ)) :=
      (ffIso_mem_normalizer_iff (ffPhi hz e) hBL l).mp hnN
    have hw : ff6mPhi e l ∈
        Subgroup.normalizer (ffImg (ff6mPhi e) B : Set ↥(omegaProj hQ)) := by
      rw [← hff l, ← hΦ]
      exact hΦl
    exact (ff6p_commute_iff hQ hdim hsgn hz e hxN l).mpr (hcomm _ hw)

theorem ff6p_theta_eq_one_iff (h : IsOm6P L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ = 1 ↔ x ∈ Subgroup.centralizer (L : Set G) := by
  show ffTheta hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e ⟨x, hxN⟩ = 1 ↔
    x ∈ Subgroup.centralizer (L : Set G)
  exact ffTheta_eq_one_iff hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e
    h.1.1.commutator_eq_top ⟨x, hxN⟩

theorem ff6p_theta_sq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hss : x * x = 1) :
    ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ = 1 := by
  have hss' : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨x, hxN⟩ = 1 :=
    Subtype.ext hss
  rw [← map_mul, hss', map_one]

theorem ff6p_induces_type (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {r : ℕ} {α : ℤˣ}
    (hx : SimHasType (ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩) r α) : InducesTypeSome L x 6 1 r α := by
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
    ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩, hdim, hsgn,
    ffTheta6P_induces hQ hdim hsgn e ⟨x, hxN⟩, hx⟩

theorem ff6p_not_centralizer_of_type (hz : Subgroup.center ↥L = ⊥) {y : G} {r : ℕ} {α : ℤˣ}
    (h : InducesTypeSome L y 6 1 r α) : y ∉ Subgroup.centralizer (L : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ := h
  exact fun hy => ff_simHasType_ne_one hx
    ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mp hy)

theorem ff6p_kind2 (hc : FF6PCls) [Finite G] (h : IsOm6P L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {y : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hty : ∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α) :
    ∃ α : ℤˣ, SimHasType (ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩) 1 α := by
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc h
  have hpow : y ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2] at h1
  have hss : y * y = 1 := by rwa [pow_two] at hpow
  let x' : ProjSim Q := ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩
  have hx'sq : x' * x' = 1 := ff6p_theta_sq hQ hdim hsgn e hyN hss
  have htyKind : KindP L y 2 := hty
  obtain ⟨α, htyα⟩ := hty
  have hynot : y ∉ Subgroup.centralizer (L : Set G) :=
    ff6p_not_centralizer_of_type hz htyα
  have hx'ne : x' ≠ 1 := fun h1 =>
    hynot ((ff6p_theta_eq_one_iff h hQ hdim hsgn e hyN).mp h1)
  rcases ff_model_classify hQ hdim hsgn hx'sq with h1 | h0 | h1k | h2k | h3k | h4k
  · exact absurd h1 hx'ne
  · exfalso
    exact (hc.excl G L h y hy2 hyN 2 0 (by norm_num) (by norm_num) (by norm_num)
      htyKind)
      (show KindP L y 0 from ff6p_induces_type hQ hdim hsgn e hyN h0)
  · exfalso
    exact (hc.excl G L h y hy2 hyN 2 1 (by norm_num) (by norm_num) (by norm_num)
      htyKind)
      (show KindP L y 1 from ff6p_induces_type hQ hdim hsgn e hyN h1k)
  · exact h2k
  · exfalso
    obtain ⟨β, hβ⟩ := h3k
    exact (hc.excl G L h y hy2 hyN 2 3 (by norm_num) (by norm_num) (by norm_num)
      htyKind)
      (show KindP L y 3 from ⟨β, ff6p_induces_type hQ hdim hsgn e hyN hβ⟩)
  · exfalso
    have h4 : KindP L y 4 := by
      show InducesOutsideGStar L 6 1 y
      exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x', hdim, hsgn,
        ffTheta6P_induces hQ hdim hsgn e ⟨y, hyN⟩, hx'sq, h4k⟩
    exact (hc.excl G L h y hy2 hyN 2 4 (by norm_num) (by norm_num) (by norm_num)
      htyKind) h4

theorem ff6p_model_ts (hc : FF6PCls) [Finite G] (h : IsOm6P L) {s : G} (hs2 : orderOf s = 2)
    (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hty : ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
      (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1),
      ffTheta6P hQ hdim hsgn e ⟨s, hsN⟩ = ffTs fr := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus h
  obtain ⟨fr⟩ := exists_pframe_six_plus hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨α, hα⟩ := ff6p_kind2 hc h hQ hdim hsgn e hs2 hsN hty
  obtain ⟨y, hy⟩ := ff6p_exists_conj_ts hQ hdim fr hα
  have hy_eq : y⁻¹ * ffTheta6P hQ hdim hsgn e ⟨s, hsN⟩ * y = ffTs fr := by
    rw [hy]
    group
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, ffAdapt h2 e y, fr,
    hdim, hsgn, ?_⟩
  refine (ffTheta6P_eq_iff hQ hdim hsgn (ffAdapt h2 e y) ⟨s, hsN⟩ (ffTs fr)).mpr ?_
  have hinds := inducesViaP_ffAdapt h2 e y
    (ffTheta6P_induces hQ hdim hsgn e ⟨s, hsN⟩)
  rwa [hy_eq] at hinds

theorem ffThetaImg_cap_six_plus (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (S : Subgroup G) :
    ffThetaImg (ffTheta6P hQ hdim hsgn e) (S ⊓ L) =
      (ffImg (ff6mPhi e) S).map (ffOmegaToSim hQ) := by
  ext q
  rw [mem_ffThetaImg_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hsS, hq⟩
    obtain ⟨hsS', hsL⟩ := Subgroup.mem_inf.mp hsS
    refine ⟨ff6mPhi e ⟨s, hsL⟩, ?_, ?_⟩
    · rw [mem_ffImg_iff]
      exact ⟨⟨s, hsL⟩, hsS', rfl⟩
    · rw [← hq]
      exact (ffTheta6P_of_mem hQ hdim hsgn e ⟨s, hsL⟩).symm.trans
        (congrArg (ffTheta6P hQ hdim hsgn e) (Subtype.ext rfl))
  · rintro ⟨w, hw, hwq⟩
    obtain ⟨l, hlS, hlφ⟩ := mem_ffImg_iff.mp hw
    refine ⟨(l : G), Subgroup.le_normalizer l.2, Subgroup.mem_inf.mpr ⟨hlS, l.2⟩, ?_⟩
    rw [ffTheta6P_of_mem, hlφ, hwq]

theorem ff6p_act_map_eq_of_normalizes (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {P : Subgroup ↥(omegaProj hQ)} {x : ProjSim Q}
    (hx : x ∈ Subgroup.normalizer ((P.map (ffOmegaToSim hQ) : Subgroup (ProjSim Q)) :
      Set (ProjSim Q))) :
    P.map (ffSimOmegaAct hQ h2 x).toMonoidHom = P := by
  apply le_antisymm
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    have hιp : ffOmegaToSim hQ p ∈ P.map (ffOmegaToSim hQ) :=
      Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
    have hconj : x * ffOmegaToSim hQ p * x⁻¹ ∈ P.map (ffOmegaToSim hQ) :=
      (Subgroup.mem_normalizer_iff.mp hx (ffOmegaToSim hQ p)).mp hιp
    obtain ⟨p', hp', hp'e⟩ := Subgroup.mem_map.mp hconj
    have hthis : (ffSimOmegaAct hQ h2 x).toMonoidHom p = p' :=
      ffOmegaToSim_injective hQ ((ff_omegaToSim_act hQ h2 x p).trans hp'e.symm)
    rw [hthis]
    exact hp'
  · intro w hw
    have hιw : ffOmegaToSim hQ w ∈ P.map (ffOmegaToSim hQ) :=
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    have hxi : x⁻¹ ∈ Subgroup.normalizer
        ((P.map (ffOmegaToSim hQ) : Subgroup (ProjSim Q)) : Set (ProjSim Q)) :=
      (Subgroup.normalizer _).inv_mem hx
    have hconj : x⁻¹ * ffOmegaToSim hQ w * x ∈ P.map (ffOmegaToSim hQ) := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hxi (ffOmegaToSim hQ w)).mp hιw
    obtain ⟨p, hp, hp'e⟩ := Subgroup.mem_map.mp hconj
    refine Subgroup.mem_map.mpr ⟨p, hp, ?_⟩
    apply ffOmegaToSim_injective hQ
    change ffOmegaToSim hQ (ffSimOmegaAct hQ h2 x p) = ffOmegaToSim hQ w
    rw [ff_omegaToSim_act hQ h2 x p, hp'e]
    group

theorem ff6p_ts_mem_of_outer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hxG : SimInGStar x) (hxΩ : ¬ SimInOmegaStar hQ x) :
    ∃ n : ↥(omegaProj hQ), ffTs fr = ffOmegaToSim hQ n * x := by
  obtain ⟨g, hgx⟩ := hxG
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hgnot : g ∉ omegaProj hQ := fun hg => hxΩ ⟨g, hg, hgx⟩
  have hgtnot : toProj Q (fr.signChange {none}) ∉ omegaProj hQ := fun hgt =>
    ffTs_not_simInOmegaStar hQ hdim fr
      ⟨toProj Q (fr.signChange {none}), hgt, rfl⟩
  have hginvnot : g⁻¹ ∉ omegaProj hQ := fun h =>
    hgnot ((Subgroup.inv_mem_iff (H := omegaProj hQ)).mp h)
  have hindex : (omegaProj hQ).index = 2 := by
    rw [index_omegaProj hQ h2,
      if_neg (ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn)]
  have hmem : toProj Q (fr.signChange {none}) * g⁻¹ ∈ omegaProj hQ :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr
      ⟨fun h => absurd h hgtnot, fun h => absurd h hginvnot⟩
  refine ⟨⟨toProj Q (fr.signChange {none}) * g⁻¹, hmem⟩, ?_⟩
  rw [ffTs, ffOmegaToSim_apply, ← hgx, map_mul, map_inv]
  group

theorem ff6p_iota_mem_thetaImg (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {H : Subgroup G}
    (hLH : L ≤ H) (w : ↥(omegaProj hQ)) :
    ffOmegaToSim hQ w ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) H := by
  obtain ⟨l, hl⟩ := ff6mPhi_surjective e w
  refine mem_ffThetaImg_iff.mpr ⟨(l : G), Subgroup.le_normalizer l.2, hLH l.2, ?_⟩
  rw [ffTheta6P_of_mem, hl]

end CFSG.OddStandard.SmallF3.Omega
