module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PIsoX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PI1X

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem ff6p_img_centralizer_eq_fix (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) :
    ffImg (ff6mPhi e) (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      ffFix hQ h2 (ffTheta6P hQ hdim hsgn e ⟨s, hsN⟩) := by
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  let x : ProjSim Q := ffTheta6P hQ hdim hsgn e ⟨s, hsN⟩
  have hs : InducesViaP L (Subgroup.center ↥L) hQ e s x :=
    ffTheta6P_induces hQ hdim hsgn e ⟨s, hsN⟩
  have hphi : ∀ l : ↥L, ffPhi hz e l = ff6mPhi e l := fun l => by
    rw [ffPhi_apply, ff6mPhi_apply]
  ext w
  rw [ffFix, mem_fixSub_iff, mem_ffImg_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hcomm : s * (l : G) = (l : G) * s :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hl).2).symm
    have h := (ff_phi_mem_fix_iff hQ h5 hz e hs l).mpr hcomm
    rw [ffFix, mem_fixSub_iff, hphi l] at h
    exact h
  · intro hw
    obtain ⟨l, hl⟩ := ff6mPhi_surjective e w
    refine ⟨l, Subgroup.mem_inf.mpr ⟨l.2, ?_⟩, hl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : ffPhi hz e l ∈ ffFix hQ h2 x := by
      rw [ffFix, mem_fixSub_iff, hphi l, hl]
      exact hw
    exact ((ff_phi_mem_fix_iff hQ h5 hz e hs l).mp hfix).symm

theorem ff6p_aut_cent_i1 (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) →
        ∀ R : Subgroup G,
          R ≤ normalizer (L : Set G) ⊓ centralizer ((layerCent L s : Subgroup G) : Set G) →
          (centralizer (L : Set G)).relIndex R ≤ 2 := by
  intro G _ _ L hL s hs2 hsN hty R hR
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hθs⟩ := ff6p_model_ts hc hL hs2 hsN hty
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  have hne : layerCent L s ≠ ⊥ :=
    ff_isOmega5_ne_bot (hc.layer_i1 G L hL s hs2 hsN hty)
  have hXeq : XOut L s = layerCent L s := hc.xout_eq G L hL s hs2 hsN hne
  have hC : ffImg (ff6mPhi e) (L ⊓ centralizer ({s} : Set G)) =
      ffFix hQ h2 (ffTheta6P hQ hdim hsgn e ⟨s, hsN⟩) :=
    ff6p_img_centralizer_eq_fix hQ hdim hsgn h2 hz e hsN
  have hX : ffImg (ff6mPhi e) (XOut L s) = twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr))) := by
    have h := ffIso_img_X (ffPhi hz e) (B := L ⊓ centralizer ({s} : Set G)) inf_le_left
    rw [ff6p_ffPhi_eq hQ hz e] at h
    rw [XOut, h, hC, hθs]
  have hCL : L ⊓ centralizer ({s} : Set G) ≤ L := inf_le_left
  have htwoRes : twoRes (L ⊓ centralizer ({s} : Set G)) ≤ L :=
    (Subgroup.closure_le L).mpr fun g hg => hCL hg.1
  have hBL : XOut L s ≤ L := by
    rw [XOut]
    exact (Subgroup.closure_le L).mpr fun g hg => htwoRes hg.1
  let ρ : ↥R →* ProjSim Q :=
    (ffTheta6P hQ hdim hsgn e).comp (Subgroup.inclusion (hR.trans inf_le_left))
  have hρapply : ∀ r : ↥R, ρ r = ffTheta6P hQ hdim hsgn e ⟨(r : G), (hR r.2).1⟩ :=
    fun _ => rfl
  have hrange : ∀ x ∈ ρ.range, x = 1 ∨ x = ffTs fr := by
    rintro x ⟨r, rfl⟩
    rw [hρapply r]
    have hrN : (r : G) ∈ Subgroup.normalizer (L : Set G) := (hR r.2).1
    have hrC : (r : G) ∈ Subgroup.centralizer ((layerCent L s : Subgroup G) : Set G) :=
      (hR r.2).2
    have hcommX : ∀ b ∈ XOut L s, (r : G) * b = b * (r : G) := by
      intro b hb
      rw [hXeq] at hb
      exact (Subgroup.mem_centralizer_iff.mp hrC b hb).symm
    have hcommθ : ∀ w ∈ ffImg (ff6mPhi e) (XOut L s),
        ffTheta6P hQ hdim hsgn e ⟨(r : G), hrN⟩ * ffOmegaToSim hQ w =
          ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨(r : G), hrN⟩ :=
      (ff6p_commute_img_iff hQ hdim hsgn hz e hrN hBL).mp hcommX
    refine ff6p_cent_X hQ hdim hsgn h2 fr ?_ ?_
    · intro b hb
      have hb' : b ∈ ffImg (ff6mPhi e) (XOut L s) := by
        rw [hX]
        exact ff6p_B1p_mem_X hQ hdim hsgn h2 fr hb
      exact hcommθ b hb'
    · intro τ hτ hsτ
      have hτ' : omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩ ∈
          ffImg (ff6mPhi e) (XOut L s) := by
        rw [hX]
        exact ff6p_hat_mem_X hQ hdim hsgn h2 fr hτ hsτ
      exact hcommθ _ hτ'
  have hker : ρ.ker = (Subgroup.centralizer (L : Set G)).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ff6p_theta_eq_one_iff hL hQ hdim hsgn e (hR r.2).1
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hts_ne : ffTs fr ≠ 1 := ff_simHasType_ne_one (ffTs_hasType hQ fr)
  have hsub : (ρ.range : Set (ProjSim Q)) ⊆ ({1, ffTs fr} : Set (ProjSim Q)) := by
    intro x hx
    rcases hrange x hx with h | h <;> simp [h]
  have hbound : (ρ.range : Set (ProjSim Q)).ncard ≤ 2 := by
    calc (ρ.range : Set (ProjSim Q)).ncard ≤ ({1, ffTs fr} : Set (ProjSim Q)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 := Set.ncard_pair hts_ne.symm
  exact hbound

end CFSG.OddStandard.SmallF3.Omega
