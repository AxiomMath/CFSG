module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem ff_isSylow2Of_normalizer {H : Type} [Group H] {P B : Subgroup H}
    (hP : IsSylow2Of P ⊤) (hNB : P ≤ Subgroup.normalizer (B : Set H)) :
    IsSylow2Of P (Subgroup.normalizer (B : Set H)) := by
  refine ⟨hNB, hP.2.1, ?_⟩
  intro hdvd
  apply hP.2.2
  have hrel := Subgroup.relIndex_mul_relIndex (H := P)
    (K := Subgroup.normalizer (B : Set H)) (L := ⊤) hNB le_top
  rw [← hrel]
  exact dvd_mul_of_dvd_left hdvd _

private theorem ff_map_conj_eq_self {H : Type} [Group H] {a : H} {U : Subgroup H}
    (ha : a ∈ Subgroup.normalizer (U : Set H)) :
    U.map (MulAut.conj a).toMonoidHom = U := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp ha u).mp hu
  · intro hx
    refine ⟨a⁻¹ * x * a, (Subgroup.mem_normalizer_iff.mp ha (a⁻¹ * x * a)).mpr ?_, ?_⟩
    · rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]
      exact hx
    · show MulAut.conj a (a⁻¹ * x * a) = x
      rw [MulAut.conj_apply]
      group

private theorem ff_map_conj_eq_of_iff {H : Type} [Group H] {a : H} {U Q : Subgroup H}
    (h : ∀ x : H, x ∈ Q ↔ a⁻¹ * x * a ∈ U) :
    U.map (MulAut.conj a).toMonoidHom = Q := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine (h (a * u * a⁻¹)).mpr ?_
    rwa [show a⁻¹ * (a * u * a⁻¹) * a = u by group]
  · intro hx
    refine ⟨a⁻¹ * x * a, (h x).mp hx, ?_⟩
    show MulAut.conj a (a⁻¹ * x * a) = x
    rw [MulAut.conj_apply]
    group

private theorem ff_mem_normalizer_map {H K : Type} [Group H] [Group K] (f : H →* K)
    {U : Subgroup H} {a : H} (ha : a ∈ Subgroup.normalizer (U : Set H)) :
    f a ∈ Subgroup.normalizer (U.map f : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro β
  constructor
  · intro hβ
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hβ
    have hmem : a * u * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp ha u).mp hu
    have heq : f a * f u * (f a)⁻¹ = f (a * u * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [← hue, heq]
    exact Subgroup.mem_map_of_mem f hmem
  · intro hβ
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hβ
    refine Subgroup.mem_map.mpr ⟨a⁻¹ * u * a, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp ha (a⁻¹ * u * a)).mpr
        (by rw [show a * (a⁻¹ * u * a) * a⁻¹ = u by group]; exact hu)
    · rw [map_mul, map_mul, map_inv, hue]
      group

private theorem ff_ffSimOmegaAct_ffOmegaToSim {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {hQ : Q.Nondegenerate} {h2 : 2 ≤ Module.finrank (ZMod 3) V} (a : ↥(omegaProj hQ)) :
    ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a) = MulAut.conj a := by
  apply MulEquiv.ext; intro w
  apply ffOmegaToSim_injective hQ
  rw [ff_omegaToSim_act, MulAut.conj_apply, map_mul, map_mul, map_inv]

variable {G : Type} [Group G] {L : Subgroup G}

theorem ff_exists_model_P1 [Finite G] (h : IsOm6M L) {P B : Subgroup G} (hP : IsSylow2Of P L)
    (hB : IsNormalE16In P B) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : NFrame Q (Fin 6) 1),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧
        ffImg (ff6mPhi e) B = ffB1 hQ fr ∧ ffImg (ff6mPhi e) P = ffP1 hQ fr := by
  have hBL : B ≤ L := hB.1.trans hP.1
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hBfr⟩ := ff_exists_model_B1 h hBL hB.2.1
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6m_odd_center h)
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hP1 := ffP1_sylow hQ hdim hsgn fr
  have hQ1 := ff_cover_isSylow2Of hφ hP
  have hNE : IsNormalE16In (ffImg (ff6mPhi e) P) (ffB1 hQ fr) := by
    have h := (ff_cover_normalE16_iff hφ hP.1 hP.2.1 hB.1).mp hB
    rwa [hBfr] at h
  have hP1N : IsSylow2Of (ffP1 hQ fr)
      (Subgroup.normalizer (ffB1 hQ fr : Set ↥(omegaProj hQ))) :=
    ff_isSylow2Of_normalizer hP1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (ffB1_le_ffP1 hQ fr)).mp
        (ffB1_normalE16 hQ hdim hsgn fr).2.2)
  have hQ1N : IsSylow2Of (ffImg (ff6mPhi e) P)
      (Subgroup.normalizer (ffB1 hQ fr : Set ↥(omegaProj hQ))) :=
    ff_isSylow2Of_normalizer hQ1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNE.1).mp hNE.2.2)
  obtain ⟨a, haN, hcond⟩ := IsSylow2Of.exists_conj_mem hP1N hQ1N
  have hact : ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a) = MulAut.conj a :=
    ff_ffSimOmegaAct_ffOmegaToSim a
  have hPmap : ffImg (ff6mPhi e) P =
      (ffP1 hQ fr).map (ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a)).toMonoidHom := by
    rw [hact]
    exact (ff_map_conj_eq_of_iff hcond).symm
  have hBmap : ffImg (ff6mPhi e) B =
      (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a)).toMonoidHom := by
    rw [hact, ff_map_conj_eq_self haN, hBfr]
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ,
    ffAdapt h2 e (ffOmegaToSim hQ a), fr, hdim, hsgn, ?_, ?_⟩
  · exact ffImg_ffAdapt h2 e (ffOmegaToSim hQ a) B (ffB1 hQ fr) hBmap
  · exact ffImg_ffAdapt h2 e (ffOmegaToSim hQ a) P (ffP1 hQ fr) hPmap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_thetaImg_cap_eq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (fr : NFrame Q (Fin 6) 1) (hP : ffImg (ff6mPhi e) (S ⊓ L) = ffP1 hQ fr) :
    ffThetaImg (ffTheta6M hQ hdim hsgn e) (S ⊓ L) = ffPS hQ fr := by
  rw [ffThetaImg_cap hQ hdim hsgn e S]
  have hsub : ffImg (ff6mPhi e) S = ffImg (ff6mPhi e) (S ⊓ L) := by
    rw [ffImg, ffImg, Subgroup.inf_subgroupOf_right]
  rw [hsub, hP]
  rfl

theorem ff_transfer_bounds (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (fr : NFrame Q (Fin 6) 1) (hS : S ≤ normalizer (L : Set G))
    (hP : ffImg (ff6mPhi e) (S ⊓ L) = ffP1 hQ fr) :
    ffPS hQ fr ≤ ffThetaImg (ffTheta6M hQ hdim hsgn e) S ∧
      ffThetaImg (ffTheta6M hQ hdim hsgn e) S ≤ normalizer (ffPS hQ fr : Set (ProjSim Q)) := by
  constructor
  · rw [← ff_thetaImg_cap_eq hQ hdim hsgn e fr hP]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left)
  · rw [← ff_thetaImg_cap_eq hQ hdim hsgn e fr hP]
    exact ffThetaImg_le_normalizer _ hS

theorem ff_transfer_i (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (h1 : ∀ y ∈ S, ∀ α : ℤˣ,
      ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α) :
    ∀ q ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) S, ∀ α : ℤˣ,
      ¬ SimHasType q 1 α ∧ ¬ SimHasType q 3 α := by
  intro q hq α
  obtain ⟨s, hsN, hsS, hqs⟩ := mem_ffThetaImg_iff.mp hq
  have hind : InducesViaP L (Subgroup.center ↥L) hQ e s q := by
    have h := ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨s, hsN⟩
    rw [ffTheta6M] at hqs
    rwa [hqs] at h
  have key : ∀ r : ℕ, SimHasType q r α → InducesTypeSome L s 6 (-1) r α := by
    intro r hr
    exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, q, hdim, hsgn, hind, hr⟩
  exact ⟨fun hst => (h1 s hsS α).1 (key 1 hst), fun hst => (h1 s hsS α).2 (key 3 hst)⟩

private theorem ff_transfer_step1 {hQ : Q.Nondegenerate} {hdim : Module.finrank (ZMod 3) V = 6}
    {hsgn : quadSign Q = -1} {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (hφ : OddCentralCover (ff6mPhi e)) {S B : Subgroup G} {fr : NFrame Q (Fin 6) 1}
    (hBfr : ffImg (ff6mPhi e) B = ffB1 hQ fr) (hS2 : IsPGroup 2 ↥(S ⊓ L))
    (hBle : B ≤ S ⊓ L) {s : G} (hsS : s ∈ S) (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hqN : ffTheta6M hQ hdim hsgn e ⟨s, hsN⟩ ∈
      Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q)))
    {b : G} (hb : b ∈ B) : s * b * s⁻¹ ∈ B := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  obtain ⟨hbS, hbL⟩ := Subgroup.mem_inf.mp (hBle hb)
  have hconjL : s * b * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN b).mp hbL
  have hconjS : s * b * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS hbS) (S.inv_mem hsS)
  let l : ↥L := ⟨b, hbL⟩
  let l' : ↥L := ⟨s * b * s⁻¹, hconjL⟩
  have hφeq : ffSimOmegaAct hQ h2 (ffTheta6M hQ hdim hsgn e ⟨s, hsN⟩) (ff6mPhi e l) =
      ff6mPhi e l' :=
    ff6m_phi_conj hQ h2 e
      (ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨s, hsN⟩) l l' rfl
  have hmemB1 : ffOmegaToSim hQ (ff6mPhi e l') ∈ ffBS hQ fr := by
    rw [← hφeq, ff_omegaToSim_act]
    refine (Subgroup.mem_normalizer_iff.mp hqN _).mp (Subgroup.mem_map_of_mem _ ?_)
    rw [← hBfr]
    exact mem_ffImg_iff.mpr ⟨l, hb, rfl⟩
  obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hmemB1
  have hul' : u = ff6mPhi e l' := ffOmegaToSim_injective hQ hue
  have hmem : ff6mPhi e l' ∈ ffImg (ff6mPhi e) B := by
    rw [hBfr]
    exact hul' ▸ hu
  obtain ⟨b₁, hb₁B, hb₁φ⟩ := mem_ffImg_iff.mp hmem
  have heq : l' = b₁ :=
    ff_cover_eq_of_pGroup (B := S ⊓ L) hφ hS2
      (Subgroup.mem_inf.mpr ⟨hconjS, hconjL⟩) (hBle hb₁B) hb₁φ.symm
  rw [show s * b * s⁻¹ = (b₁ : G) from congrArg Subtype.val heq]
  exact hb₁B

private theorem ff_transfer_step2 {hQ : Q.Nondegenerate} {hdim : Module.finrank (ZMod 3) V = 6}
    {hsgn : quadSign Q = -1} {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (hφ : OddCentralCover (ff6mPhi e)) {S B : Subgroup G} {fr : NFrame Q (Fin 6) 1}
    (hBfr : ffImg (ff6mPhi e) B = ffB1 hQ fr) (hS2 : IsPGroup 2 ↥(S ⊓ L))
    (hBle : B ≤ S ⊓ L) {s : G} (hsS : s ∈ S) (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hqN : ffTheta6M hQ hdim hsgn e ⟨s, hsN⟩ ∈
      Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q))) :
    s ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => ff_transfer_step1 hφ hBfr hS2 hBle hsS hsN hqN hx
  · intro hx
    have hsinv : s⁻¹ ∈ S := S.inv_mem hsS
    have hsinvN : s⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem hsN
    have hqinv : ffTheta6M hQ hdim hsgn e ⟨s⁻¹, hsinvN⟩ ∈
        Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q)) := by
      have he : ffTheta6M hQ hdim hsgn e ⟨s⁻¹, hsinvN⟩ =
          (ffTheta6M hQ hdim hsgn e ⟨s, hsN⟩)⁻¹ := by
        rw [← map_inv]
        exact (congrArg _ (Subtype.ext rfl)).symm
      rw [he]
      exact (Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q))).inv_mem hqN
    have h := ff_transfer_step1 hφ hBfr hS2 hBle hsinv hsinvN hqinv hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at h

theorem ff_transfer_ii [Finite G] (hL : IsOm6M L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S B : Subgroup G} (fr : NFrame Q (Fin 6) 1)
    (hS : IsSylow2Of S (normalizer (L : Set G))) (hB : IsNormalE16In (S ⊓ L) B)
    (hAut : autIn S B ≤ autIn L B) (hBfr : ffImg (ff6mPhi e) B = ffB1 hQ fr) :
    ∀ q ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) S,
      q ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) →
        ∃ w ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)), SimInOmegaStar hQ w ∧
          ∀ β ∈ ffBS hQ fr, q * β * q⁻¹ = w * β * w⁻¹ := by
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6m_odd_center hL)
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hS2 : IsPGroup 2 ↥(S ⊓ L) :=
    hS.2.1.to_le (show S ⊓ L ≤ S from inf_le_left)
  have hBle : B ≤ S ⊓ L := hB.1
  have hBL : B ≤ L := hBle.trans inf_le_right
  have hB2 : IsPGroup 2 B := hS2.to_le (H := B) hBle
  intro q hq hqN
  obtain ⟨s, hsN, hsS, hqs⟩ := mem_ffThetaImg_iff.mp hq
  have hqN' : ffTheta6M hQ hdim hsgn e ⟨s, hsN⟩ ∈
      Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q)) := by
    rw [hqs]
    exact hqN
  have hsB : s ∈ Subgroup.normalizer (B : Set G) :=
    ff_transfer_step2 hφ hBfr hS2 hBle hsS hsN hqN'
  have hmemAut : B.normalizerMonoidHom ⟨s, hsB⟩ ∈ autIn S B := by
    rw [autIn, Subgroup.mem_map]
    exact ⟨⟨s, hsB⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hmemAutL := hAut hmemAut
  rw [autIn, Subgroup.mem_map] at hmemAutL
  obtain ⟨y, hy, hyEq⟩ := hmemAutL
  have hlL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
  have hlB : (y : G) ∈ Subgroup.normalizer (B : Set G) := y.2
  have hconj_eq : ∀ b ∈ B, (y : G) * b * (y : G)⁻¹ = s * b * s⁻¹ := by
    intro b hb
    have h1 := congrArg (fun f : MulAut ↥B => ((f ⟨b, hb⟩ : ↥B) : G)) hyEq
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  let ll : ↥L := ⟨(y : G), hlL⟩
  have hφN : ff6mPhi e ll ∈ Subgroup.normalizer (ffB1 hQ fr : Set ↥(omegaProj hQ)) := by
    have h := (ff_cover_mem_normalizer_iff hφ hBL hB2 ll).mp
      (show (ll : G) ∈ Subgroup.normalizer (B : Set G) from hlB)
    rwa [hBfr] at h
  set w : ProjSim Q := ffOmegaToSim hQ (ff6mPhi e ll) with hwdef
  have hwN : w ∈ Subgroup.normalizer (ffBS hQ fr : Set (ProjSim Q)) := by
    rw [hwdef]
    exact ff_mem_normalizer_map (ffOmegaToSim hQ) hφN
  have hwΩ : SimInOmegaStar hQ w := by
    refine ⟨((ff6mPhi e ll : omegaProj hQ) : ProjOrth Q), (ff6mPhi e ll).2, ?_⟩
    rw [hwdef, ffOmegaToSim_apply]
  refine ⟨w, hwN, hwΩ, ?_⟩
  intro β hβ
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hβ
  have hu' : u ∈ ffImg (ff6mPhi e) B := by rw [hBfr]; exact hu
  obtain ⟨bl, hblB, hblφ⟩ := mem_ffImg_iff.mp hu'
  rw [← hblφ]
  have hblL : (bl : G) ∈ L := bl.2
  have hslL : s * (bl : G) * s⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hsN (bl : G)).mp hblL
  let sl' : ↥L := ⟨s * (bl : G) * s⁻¹, hslL⟩
  have hind : InducesViaP L (Subgroup.center ↥L) hQ e s q := by
    have h := ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨s, hsN⟩
    rw [ffTheta6M] at hqs
    rwa [hqs] at h
  have hqside : q * ffOmegaToSim hQ (ff6mPhi e bl) * q⁻¹ =
      ffOmegaToSim hQ (ff6mPhi e sl') := by
    rw [← ff_omegaToSim_act (hQ := hQ) (h2 := h2)]
    rw [ff6m_phi_conj hQ h2 e hind bl sl' rfl]
  have hwside : w * ffOmegaToSim hQ (ff6mPhi e bl) * w⁻¹ =
      ffOmegaToSim hQ (ff6mPhi e (ll * bl * ll⁻¹)) := by
    rw [hwdef]
    have hstep : ffOmegaToSim hQ (ff6mPhi e ll) * ffOmegaToSim hQ (ff6mPhi e bl) *
        (ffOmegaToSim hQ (ff6mPhi e ll))⁻¹ =
        ffOmegaToSim hQ (ff6mPhi e ll * ff6mPhi e bl * (ff6mPhi e ll)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hstep, show ff6mPhi e ll * ff6mPhi e bl * (ff6mPhi e ll)⁻¹ =
      ff6mPhi e (ll * bl * ll⁻¹) by rw [map_mul, map_mul, map_inv]]
  have hll_eq : ll * bl * ll⁻¹ = sl' := by
    apply Subtype.ext
    show (y : G) * (bl : G) * (y : G)⁻¹ = s * (bl : G) * s⁻¹
    exact hconj_eq (bl : G) hblB
  calc q * ffOmegaToSim hQ (ff6mPhi e bl) * q⁻¹
      = ffOmegaToSim hQ (ff6mPhi e sl') := hqside
    _ = ffOmegaToSim hQ (ff6mPhi e (ll * bl * ll⁻¹)) := by rw [hll_eq]
    _ = w * ffOmegaToSim hQ (ff6mPhi e bl) * w⁻¹ := hwside.symm

end CFSG.OddStandard.SmallF3.Omega
