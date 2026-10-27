module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4SylA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def ffOmegaToSim (hQ : Q.Nondegenerate) :
    ↥(omegaProj hQ) →* ProjSim Q :=
  (projOrthToProjSim Q).comp (omegaProj hQ).subtype

theorem ffOmegaToSim_apply (hQ : Q.Nondegenerate) (w : ↥(omegaProj hQ)) :
    ffOmegaToSim hQ w = projOrthToProjSim Q (w : ProjOrth Q) :=
  rfl

theorem ffOmegaToSim_injective (hQ : Q.Nondegenerate) : Function.Injective (ffOmegaToSim hQ) := by
  intro a b h
  apply Subtype.ext
  apply projOrthToProjSim_injective
  show ffOmegaToSim hQ a = ffOmegaToSim hQ b
  exact h

@[expose] noncomputable def ffTheta6M (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q :=
  ffTheta hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e

theorem ffTheta6M_of_mem (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    ffTheta6M hQ hdim hsgn e ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      ffOmegaToSim hQ (ff6mPhi e l) := by
  rw [ffTheta6M, ffTheta_of_mem]
  rfl

@[expose] noncomputable def ffThetaImg (θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q)
    (S : Subgroup G) :
    Subgroup (ProjSim Q) :=
  (S.subgroupOf (Subgroup.normalizer (L : Set G))).map θ

theorem mem_ffThetaImg_iff {θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q} {S : Subgroup G}
    {q : ProjSim Q} :
    q ∈ ffThetaImg θ S ↔ ∃ (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G)),
      s ∈ S ∧ θ ⟨s, hs⟩ = q := by
  unfold ffThetaImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s : G), s.2, Subgroup.mem_subgroupOf.mp hs, rfl⟩
  · rintro ⟨s, hs, hsS, rfl⟩
    exact ⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩

theorem ff_sylow_inf_normalizer [Finite G] {S : Subgroup G}
    (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G))) : IsSylow2Of (S ⊓ L) L := by
  refine sec8t84_sylow_inf_normal hS Subgroup.le_normalizer ?_
  intro h hh n hn
  exact (Subgroup.mem_normalizer_iff.mp hh n).mp hn

theorem ffThetaImg_cap (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (S : Subgroup G) :
    ffThetaImg (ffTheta6M hQ hdim hsgn e) (S ⊓ L) =
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
      exact (ffTheta6M_of_mem hQ hdim hsgn e ⟨s, hsL⟩).symm.trans
        (congrArg (ffTheta6M hQ hdim hsgn e) (Subtype.ext rfl))
  · rintro ⟨w, hw, hwq⟩
    obtain ⟨l, hlS, hlφ⟩ := mem_ffImg_iff.mp hw
    refine ⟨(l : G), Subgroup.le_normalizer l.2, Subgroup.mem_inf.mpr ⟨hlS, l.2⟩, ?_⟩
    rw [ffTheta6M_of_mem, hlφ, hwq]

theorem ffThetaImg_sylow [Finite G] (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {S : Subgroup G} (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G))) :
    IsSylow2Of (ffImg (ff6mPhi e) S) (⊤ : Subgroup ↥(omegaProj hQ)) := by
  have hsub : ffImg (ff6mPhi e) (S ⊓ L) = ffImg (ff6mPhi e) S := by
    rw [ffImg, ffImg, Subgroup.inf_subgroupOf_right]
  rw [← hsub]
  exact ff_cover_isSylow2Of (ff6m_phi_cover e hodd) (ff_sylow_inf_normalizer hS)

theorem ffThetaImg_isPGroup (θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q) {S : Subgroup G}
    (hS : IsPGroup 2 S) : IsPGroup 2 (ffThetaImg θ S) := by
  unfold ffThetaImg
  rw [← Subgroup.comap_subtype]
  exact (hS.comap_subtype (K := Subgroup.normalizer (L : Set G))).map θ

private theorem ffThetaImg_conj_mem (θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q)
    {S : Subgroup G} {s : G} (hsS : s ∈ S) (hs : s ∈ Subgroup.normalizer (L : Set G))
    {p : ProjSim Q} (hp : p ∈ ffThetaImg θ (S ⊓ L)) :
    θ ⟨s, hs⟩ * p * (θ ⟨s, hs⟩)⁻¹ ∈ ffThetaImg θ (S ⊓ L) := by
  obtain ⟨t, ht, htS, rfl⟩ := mem_ffThetaImg_iff.mp hp
  obtain ⟨htS', htL⟩ := Subgroup.mem_inf.mp htS
  refine mem_ffThetaImg_iff.mpr ⟨s * t * s⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem hs (Subgroup.le_normalizer htL))
      ((Subgroup.normalizer (L : Set G)).inv_mem hs)
  · exact Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hsS htS') (S.inv_mem hsS),
      (Subgroup.mem_normalizer_iff.mp hs t).mp htL⟩
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext rfl)

theorem ffThetaImg_le_normalizer (θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q)
    {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G)) :
    ffThetaImg θ S ≤ Subgroup.normalizer (ffThetaImg θ (S ⊓ L) : Set (ProjSim Q)) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro p
  obtain ⟨s, hs, hsS, rfl⟩ := mem_ffThetaImg_iff.mp hq
  constructor
  · exact ffThetaImg_conj_mem θ hsS hs
  · intro hp
    have hsinvS : s⁻¹ ∈ S := S.inv_mem hsS
    have hsinv : s⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem hs
    have hconj := ffThetaImg_conj_mem θ hsinvS hsinv hp
    have heq : θ ⟨s⁻¹, hsinv⟩ * (θ ⟨s, hs⟩ * p * (θ ⟨s, hs⟩)⁻¹) *
        (θ ⟨s⁻¹, hsinv⟩)⁻¹ = p := by
      have h1 : θ ⟨s⁻¹, hsinv⟩ = (θ ⟨s, hs⟩)⁻¹ := by
        rw [← map_inv]
        exact congrArg θ (Subtype.ext rfl)
      rw [h1]
      group
    rwa [heq] at hconj

theorem ff_theta_back_left [Finite G] (hq : CFSG.IsQuasisimple ↥L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {S : Subgroup G} (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G)))
    (hΩ : ∀ q ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) S, SimInOmegaStar hQ q) :
    S ≤ (S ⊓ L) ⊔ Subgroup.centralizer (L : Set G) := by
  let θ := ffTheta6M hQ hdim hsgn e
  let P : Subgroup ↥(omegaProj hQ) := ffImg (ff6mPhi e) S
  let T : Subgroup ↥(omegaProj hQ) := (ffThetaImg θ S).comap (ffOmegaToSim hQ)
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 3] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (OGroup Q) := Subtype.finite
  haveI : Finite ↥(omegaProj hQ) := inferInstance
  have hP : IsSylow2Of P ⊤ := ffThetaImg_sylow hQ e hodd hS
  have hPleT : P ≤ T := by
    intro w hw
    change ffOmegaToSim hQ w ∈ ffThetaImg θ S
    have hw' : ffOmegaToSim hQ w ∈ ffThetaImg θ (S ⊓ L) := by
      rw [ffThetaImg_cap hQ hdim hsgn e S]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left) hw'
  have hT2 : IsPGroup 2 T := by
    change IsPGroup 2 ((ffThetaImg θ S).comap (ffOmegaToSim hQ))
    exact (ffThetaImg_isPGroup θ hS.2.1).comap_of_injective (ffOmegaToSim hQ)
      (ffOmegaToSim_injective hQ)
  have hTeq : T = P := IsSylow2Of.eq_of_le hP le_top hT2 hPleT
  intro s hsS
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hS.1 hsS
  have hθsΩ : SimInOmegaStar hQ (θ ⟨s, hsN⟩) :=
    hΩ (θ ⟨s, hsN⟩) (mem_ffThetaImg_iff.mpr ⟨s, hsN, hsS, rfl⟩)
  obtain ⟨w, hw, hwx⟩ := hθsΩ
  have hwT : (⟨w, hw⟩ : ↥(omegaProj hQ)) ∈ T := by
    change ffOmegaToSim hQ ⟨w, hw⟩ ∈ ffThetaImg θ S
    rw [ffOmegaToSim_apply, hwx]
    exact mem_ffThetaImg_iff.mpr ⟨s, hsN, hsS, rfl⟩
  have hwP : (⟨w, hw⟩ : ↥(omegaProj hQ)) ∈ P := hTeq ▸ hwT
  obtain ⟨l, hlS, hlφ⟩ := mem_ffImg_iff.mp hwP
  have hθl : θ ⟨(l : G), Subgroup.le_normalizer l.2⟩ = θ ⟨s, hsN⟩ := by
    have h1 : θ ⟨(l : G), Subgroup.le_normalizer l.2⟩ = ffOmegaToSim hQ (ff6mPhi e l) :=
      ffTheta6M_of_mem hQ hdim hsgn e l
    rw [h1, hlφ]
    exact hwx
  have hker : θ ((⟨(l : G), Subgroup.le_normalizer l.2⟩ :
      ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨s, hsN⟩) = 1 := by
    rw [map_mul, map_inv, hθl, inv_mul_cancel]
  have hcent : (((⟨(l : G), Subgroup.le_normalizer l.2⟩ :
      ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨s, hsN⟩ :
        ↥(Subgroup.normalizer (L : Set G))) : G) ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : ffTheta hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e
        ((⟨(l : G), Subgroup.le_normalizer l.2⟩ :
          ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨s, hsN⟩) = 1 := hker
    exact (ffTheta_eq_one_iff hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e
      hq.1.commutator_eq_top _).mp h1
  have hcent' : (l : G)⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
    simpa using hcent
  have hlSL : (l : G) ∈ S ⊓ L := Subgroup.mem_inf.mpr ⟨hlS, l.2⟩
  have hs_eq : s = (l : G) * ((l : G)⁻¹ * s) := by group
  rw [hs_eq]
  exact Subgroup.mul_mem_sup hlSL hcent'

theorem ff_theta_back_right [Finite G] (hq : CFSG.IsQuasisimple ↥L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (L : Set G)) {γ : G} (hγS : γ ∈ S) {x : ProjSim Q}
    (hγx : ∀ hγ : γ ∈ Subgroup.normalizer (L : Set G),
      ffTheta6M hQ hdim hsgn e ⟨γ, hγ⟩ = x)
    (hcl : ∀ q ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) S, ∃ (n : ℤ) (p : ProjSim Q),
      p ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) (S ⊓ L) ∧ q = x ^ n * p) :
    S ≤ Subgroup.zpowers γ ⊔ (S ⊓ L) ⊔ Subgroup.centralizer (L : Set G) := by
  let θ := ffTheta6M hQ hdim hsgn e
  intro s hsS
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hS hsS
  have hqmem : θ ⟨s, hsN⟩ ∈ ffThetaImg θ S :=
    mem_ffThetaImg_iff.mpr ⟨s, hsN, hsS, rfl⟩
  obtain ⟨n, p, hp, hqp⟩ := hcl (θ ⟨s, hsN⟩) hqmem
  obtain ⟨t, htN, htS, htθ⟩ := mem_ffThetaImg_iff.mp hp
  obtain ⟨htS', htL⟩ := Subgroup.mem_inf.mp htS
  have hγN : γ ∈ Subgroup.normalizer (L : Set G) := hS hγS
  have hγx' : θ ⟨γ, hγN⟩ = x := hγx hγN
  have hker : θ (((⟨γ, hγN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n * ⟨t, htN⟩)⁻¹
      * ⟨s, hsN⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, map_zpow, hγx', htθ, ← hqp, inv_mul_cancel]
  have hcent : ((((⟨γ, hγN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n * ⟨t, htN⟩)⁻¹
      * ⟨s, hsN⟩ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈
        Subgroup.centralizer (L : Set G) := by
    have h1 : ffTheta hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e
        (((⟨γ, hγN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n * ⟨t, htN⟩)⁻¹
          * ⟨s, hsN⟩) = 1 := hker
    exact (ffTheta_eq_one_iff hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e
      hq.1.commutator_eq_top _).mp h1
  have hcent' : (γ ^ n * t)⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
    simpa using hcent
  have hmem : γ ^ n * t ∈ Subgroup.zpowers γ ⊔ (S ⊓ L) :=
    Subgroup.mul_mem_sup (Subgroup.zpow_mem (Subgroup.zpowers γ) (Subgroup.mem_zpowers γ) n)
      (Subgroup.mem_inf.mpr ⟨htS', htL⟩)
  have hs_eq : s = (γ ^ n * t) * ((γ ^ n * t)⁻¹ * s) := by group
  rw [hs_eq]
  exact Subgroup.mul_mem_sup hmem hcent'

end CFSG.OddStandard.SmallF3.Omega
