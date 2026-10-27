module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaAdapt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure FF6PCls : Prop where
  center_triv : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L → centerIn L = ⊥
  nontrivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 s) → s ∉ centralizer (L : Set G)
  excl : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → KindP L s i → ¬ KindP L s j
  layer_i1 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) → IsOmega5 (layerCent L s)
  xout_eq : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private lemma ffOutFF6PModel_act_inv_apply (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (y : ProjSim Q) (w : ↥(omegaProj hQ)) :
    ffSimOmegaAct hQ h2 y (ffSimOmegaAct hQ h2 y⁻¹ w) = w := by
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, coe_ffSimOmegaAct, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, MulAut.one_apply]

private lemma ffOutFF6PModel_img_adapt (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (y : ProjSim Q) (B : Subgroup G) :
    ffImg (ff6mPhi e) B =
      (ffImg (ff6mPhi (ffAdapt h2 e y)) B).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  have hcomp : ff6mPhi e =
      (ffSimOmegaAct hQ h2 y).toMonoidHom.comp (ff6mPhi (ffAdapt h2 e y)) := by
    apply MonoidHom.ext
    intro l
    change ff6mPhi e l = ffSimOmegaAct hQ h2 y (ffSimOmegaAct hQ h2 y⁻¹ (ff6mPhi e l))
    exact (ffOutFF6PModel_act_inv_apply hQ h2 y (ff6mPhi e l)).symm
  rw [hcomp]
  simp only [ffImg]
  exact (Subgroup.map_map _ _ _).symm

private lemma ffOutFF6PModel_map_map_act (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (U : Subgroup ↥(omegaProj hQ)) (y z : ProjSim Q) :
    (U.map (ffSimOmegaAct hQ h2 z).toMonoidHom).map
        (ffSimOmegaAct hQ h2 y).toMonoidHom =
      U.map (ffSimOmegaAct hQ h2 (y * z)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro w
  change ffSimOmegaAct hQ h2 y (ffSimOmegaAct hQ h2 z w) =
    ffSimOmegaAct hQ h2 (y * z) w
  rw [map_mul, MulAut.mul_apply]

private lemma ffOutFF6PModel_map_mul_eq (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {U : Subgroup ↥(omegaProj hQ)} {z : ProjSim Q}
    (hz : U.map (ffSimOmegaAct hQ h2 z).toMonoidHom = U) (y : ProjSim Q) :
    U.map (ffSimOmegaAct hQ h2 (y * z)).toMonoidHom =
      U.map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  rw [← ffOutFF6PModel_map_map_act hQ h2 U y z, hz]

theorem ff6p_center_bot (hc : FF6PCls) [Finite G] (h : IsOm6P L) :
    Subgroup.center ↥L = ⊥ := by
  have h1 : centerIn L = ⊥ := hc.center_triv G L h
  rw [centerIn] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) L.subtype_injective).mp h1

theorem ff6p_odd_center [Finite G] (h : IsOm6P L) : Odd (Nat.card (Subgroup.center ↥L)) := by
  rw [ff_center_eq_oddCore_six_plus h]
  exact ff_odd_card_oddCore ↥L

@[expose] noncomputable def ffTheta6P (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q :=
  ffTheta hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e

theorem ffTheta6P_induces (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (s : ↥(Subgroup.normalizer (L : Set G))) :
    InducesViaP L (Subgroup.center ↥L) hQ e (s : G) (ffTheta6P hQ hdim hsgn e s) :=
  ffTheta_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e s

theorem ffTheta6P_of_mem (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    ffTheta6P hQ hdim hsgn e ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      ffOmegaToSim hQ (ff6mPhi e l) := by
  rw [ffTheta6P, ffTheta_of_mem]
  rfl

theorem ffTheta6P_eq_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (s : ↥(Subgroup.normalizer (L : Set G))) (x : ProjSim Q) :
    ffTheta6P hQ hdim hsgn e s = x ↔
      InducesViaP L (Subgroup.center ↥L) hQ e (s : G) x :=
  ffTheta_eq_iff hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e s x

theorem ff6p_model_of_oddCore [Finite G] (h : IsOm6P L) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ oddCore ↥L ≃* omegaProj hQ) :
    ∃ e' : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ, ∀ (s : G) (x : ProjSim Q),
      InducesViaP L (oddCore ↥L) hQ e s x → InducesViaP L (Subgroup.center ↥L) hQ e' s x := by
  have heq : Subgroup.center ↥L = oddCore ↥L := ff_center_eq_oddCore_six_plus h
  refine ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans e, ?_⟩
  intro s x hs
  refine ⟨hs.1, fun l l' hl => ?_⟩
  have h := hs.2 l l' hl
  simpa only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk] using h

theorem ff6p_ffPhi_eq (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    (ffPhi hz e).toMonoidHom = ff6mPhi e :=
  MonoidHom.ext fun l => (ffPhi_apply hz e l).trans (ff6mPhi_apply e l).symm

theorem ff6p_phi_injective (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : Function.Injective (ff6mPhi e) := by
  rw [← ff6p_ffPhi_eq hQ hz e]
  exact (ffPhi hz e).injective

theorem ff6p_adapt_P [Finite G] (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (fr : PFrame Q (Option (Fin 5)) ffC)
    {P : Subgroup G} (hP : IsSylow2Of P L) :
    ∃ y : ProjSim Q, ffImg (ff6mPhi (ffAdapt h2 e y)) P = ffP1p hQ fr := by
  haveI : Finite ↥(omegaProj hQ) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_plus hQ hdim hsgn]; norm_num)
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hS : IsSylow2Of (ffImg (ff6mPhi e) P) (⊤ : Subgroup ↥(omegaProj hQ)) :=
    ff_cover_isSylow2Of hφ hP
  have hP1 : IsSylow2Of (ffP1p hQ fr) (⊤ : Subgroup ↥(omegaProj hQ)) :=
    ffP1p_sylow hQ hdim hsgn fr
  obtain ⟨a, -, hconj⟩ := hP1.exists_conj_mem hS
  let y : ProjSim Q := ffOmegaToSim hQ a
  have hact : ∀ w : ↥(omegaProj hQ), ffSimOmegaAct hQ h2 y w = a * w * a⁻¹ := fun w =>
    ffOmegaToSim_injective hQ (by
      rw [ff_omegaToSim_act hQ h2 y w, map_mul, map_mul, map_inv])
  refine ⟨y, ffImg_ffAdapt h2 e y P (ffP1p hQ fr) ?_⟩
  ext x
  rw [hconj x]
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨a⁻¹ * x * a, hx, ?_⟩
    change ffSimOmegaAct hQ h2 y (a⁻¹ * x * a) = x
    rw [hact (a⁻¹ * x * a)]
    group
  · rintro ⟨w, hw, hwx⟩
    rw [← hwx]
    change a⁻¹ * ffSimOmegaAct hQ h2 y w * a ∈ ffP1p hQ fr
    rw [hact w]
    have heq : a⁻¹ * (a * w * a⁻¹) * a = w := by group
    rwa [heq]

theorem ff6p_adapt_PB [Finite G] (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (fr : PFrame Q (Option (Fin 5)) ffC)
    {P B : Subgroup G} (hP : IsSylow2Of P L) (hB : IsNormalE16In P B) :
    ∃ y : ProjSim Q, ffImg (ff6mPhi (ffAdapt h2 e y)) P = ffP1p hQ fr ∧
      ffImg (ff6mPhi (ffAdapt h2 e y)) B = ffB1p hQ fr := by
  obtain ⟨y₁, hy₁⟩ := ff6p_adapt_P hQ hdim hsgn h2 e hodd fr hP
  have hφ₁ : OddCentralCover (ff6mPhi (ffAdapt h2 e y₁)) :=
    ff6m_phi_cover (ffAdapt h2 e y₁) hodd
  have hU₁ : IsNormalE16In (ffP1p hQ fr) (ffImg (ff6mPhi (ffAdapt h2 e y₁)) B) := by
    have h := (ff_cover_normalE16_iff hφ₁ hP.1 hP.2.1 hB.1).mp hB
    rwa [hy₁] at h
  obtain ⟨y₀, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
  rcases ff6p_normalE16_cases hQ hdim hsgn h2 fr hy0G hy0 hU₁ with hB1 | hB2
  · exact ⟨y₁, hy₁, hB1⟩
  · refine ⟨y₁ * y₀, ?_, ?_⟩
    · exact ffImg_ffAdapt h2 e (y₁ * y₀) P (ffP1p hQ fr) (by
        rw [ffOutFF6PModel_img_adapt hQ h2 e y₁ P, hy₁]
        exact (ffOutFF6PModel_map_mul_eq hQ h2 hy0 y₁).symm)
    · exact ffImg_ffAdapt h2 e (y₁ * y₀) B (ffB1p hQ fr) (by
        rw [ffOutFF6PModel_img_adapt hQ h2 e y₁ B, hB2]
        exact ffOutFF6PModel_map_map_act hQ h2 (ffB1p hQ fr) y₁ y₀)

theorem ff6p_exists_model_P [Finite G] (h : IsOm6P L) {P : Subgroup G} (hP : IsSylow2Of P L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = 1 ∧ ffImg (ff6mPhi e) P = ffP1p hQ fr := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus h
  obtain ⟨fr⟩ := exists_pframe_six_plus hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center h
  obtain ⟨y, hy⟩ := ff6p_adapt_P hQ hdim hsgn h2 e hodd fr hP
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, ffAdapt h2 e y, fr, hdim, hsgn, hy⟩

theorem ff6p_exists_model_PB [Finite G] (h : IsOm6P L) {P B : Subgroup G} (hP : IsSylow2Of P L)
    (hB : IsNormalE16In P B) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = 1 ∧ ffImg (ff6mPhi e) P = ffP1p hQ fr ∧
        ffImg (ff6mPhi e) B = ffB1p hQ fr := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus h
  obtain ⟨fr⟩ := exists_pframe_six_plus hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center h
  obtain ⟨y, hyP, hyB⟩ := ff6p_adapt_PB hQ hdim hsgn h2 e hodd fr hP hB
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, ffAdapt h2 e y, fr, hdim, hsgn,
    hyP, hyB⟩

theorem ff6p_img_normalE16_cases [Finite G] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (fr : PFrame Q (Option (Fin 5)) ffC)
    {P B : Subgroup G} (hP : IsSylow2Of P L) (hPφ : ffImg (ff6mPhi e) P = ffP1p hQ fr)
    (hB : IsNormalE16In P B) {y : ProjSim Q} (hyG : ¬ SimInGStar y)
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr) :
    ffImg (ff6mPhi e) B = ffB1p hQ fr ∨
      ffImg (ff6mPhi e) B = (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hU : IsNormalE16In (ffP1p hQ fr) (ffImg (ff6mPhi e) B) := by
    have h := (ff_cover_normalE16_iff hφ hP.1 hP.2.1 hB.1).mp hB
    rwa [hPφ] at h
  exact ff6p_normalE16_cases hQ hdim hsgn h2 fr hyG hy hU

end Model

end CFSG.OddStandard.SmallF3.Omega
