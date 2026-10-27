module

public import CFSG.ClassicalInvolution.Asc77.AscT7FC
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
public import CFSG.ClassicalInvolution.Asc77.AscT8S26ULift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8S2

theorem s26_perm4_partner : ∀ a : Equiv.Perm (Fin 4), s26IsTransp a →
    ∃ b : Equiv.Perm (Fin 4), s26IsTransp b ∧ b ≠ a ∧ a * b = b * a := by decide

theorem s26_perm4_eq_of_comm {a b c : Equiv.Perm (Fin 4)} (ha : s26IsTransp a)
    (hb : s26IsTransp b) (hc : s26IsTransp c) (hba : b ≠ a) (hab : a * b = b * a) (hca : c ≠ a)
    (hac : a * c = c * a) : c = b := by
  by_contra hcb
  exact (s26_perm4_comm a b c ha hb (Ne.symm hba) hab hc hca hcb).1 hac.symm

section Key

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_unique_member (hs : Std8 p f Ω K J S R T W z t)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) :
    ∃ J₂ ∈ omegaNbr Ω K, ∀ L ∈ Ω, L ≤ omegaNbrGen Ω K →
      2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → L = J₂ := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp p f Ω := T8.partIHyp_of_std8 hs
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨η₂, hη₂, hinv₂⟩ := exists_invariant_mem_etaSet hp hq hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Ctx p f Ω W₂ := MuTab.muTabCtx hP hW₂
  let φ₂ : ↥(muGroup Ω W₂) ≃* Equiv.Perm (Fin 4) :=
    ((l7_5_2_proved p f hp hq G Ω hΩ W₂ hW₂ W hs.hW.1).some).trans φ
  have hTT : Star3T.IsTT (muDelta Ω W₂) :=
    isTT_muDelta hp hq hΩ hW₂ (thompsonCube G Ω hP W₂ hW₂)
  have hTT' := T7A.isTT_map_equiv hTT φ₂
  have hmem : ∀ ρ : Rep Ω W₂, s26IsTransp (φ₂ (MuTab.muTabElt ρ)) := fun ρ =>
    (s26_tt_iff hTT' _).mp ⟨_, MuTab.muTabElt_mem ρ, rfl⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  have hρKK : ρK.K = K := rfl
  have hρKR : ρK.R = R := rfl
  obtain ⟨b, hbT, hba, hab⟩ := s26_perm4_partner _ (hmem ρK)
  obtain ⟨d, hd, hdb⟩ : b ∈ φ₂ '' muDelta Ω W₂ := (s26_tt_iff hTT' b).mpr hbT
  obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
  have hne : ρK.K ≠ σ.K := fun h =>
    hba (by rw [← hdb, (MuTab.muTabElt_eq_iff hP hW₂ σ ρK).mpr h.symm])
  have hcomm : MuTab.muTabElt ρK * MuTab.muTabElt σ = MuTab.muTabElt σ * MuTab.muTabElt ρK := by
    apply φ₂.injective
    rw [map_mul, map_mul, hdb]
    exact hab
  have hnbr : σ.K ∈ omegaNbr Ω ρK.K :=
    c₂.omega_of_comm ρK σ hne (by have := congrArg Subtype.val hcomm; exact this)
  refine ⟨σ.K, hnbr, fun L hL hLX hcard => ?_⟩
  have h611 : L ⊓ W₂ ∈ η₂ := l6_11_proved p f hp hq G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hp hq hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := hΩ.isPGroup_of_mem_USet hp hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := c₂.exists_rep_of_involution_mem hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  have hrLX : ρL.r ∈ X := by
    have h1 : ρL.r ∈ ρL.K := ρL.hRK.1 ρL.hr
    rw [hρLL] at h1
    exact hLX h1
  have hRXc : conjSub ρK.r X = X :=
    s26_conjSub_omegaNbrGen hΩ (conjSub_eq_self_of_mem (hs.hR.2.1 ρK.hr))
  by_cases hcm : MuTab.muTabElt ρK * MuTab.muTabElt ρL = MuTab.muTabElt ρL * MuTab.muTabElt ρK
  · by_cases hKL : ρL.K = ρK.K
    ·
      exfalso
      have hLK : L = K := by rw [← hρL, hKL]
      exact hKX (hLK ▸ hLX)
    ·
      have hc : φ₂ (MuTab.muTabElt ρL) = b := by
        refine s26_perm4_eq_of_comm (hmem ρK) hbT (hmem ρL) hba hab ?_ ?_
        · intro h
          exact hKL ((MuTab.muTabElt_eq_iff hP hW₂ ρL ρK).mp (φ₂.injective h))
        · rw [← map_mul, ← map_mul, hcm]
      have hLσ : MuTab.muTabElt ρL = MuTab.muTabElt σ := φ₂.injective (hc.trans hdb.symm)
      rw [← hρL]
      exact (MuTab.muTabElt_eq_iff hP hW₂ ρL σ).mp hLσ
  ·
    exfalso
    have hnc : ρK.img * ρL.img ≠ ρL.img * ρK.img := fun h => hcm (Subtype.ext h)
    have hnc' : ρL.img * ρK.img ≠ ρK.img * ρL.img := fun h => hnc h.symm
    have hconj : ρK.r * zL * ρK.r⁻¹ = z * zL :=
      c₂.conj_involution_of_noncomm ρK ρL hnc hs.hz (by rw [hρL]; exact hzL)
    have hconj' : ρL.r * z * ρL.r⁻¹ = zL * z :=
      c₂.conj_involution_of_noncomm ρL ρK hnc' (by rw [hρL]; exact hzL) hs.hz
    have hsq : (z * zL) * (z * zL) = 1 := by
      rw [← hconj]
      calc ρK.r * zL * ρK.r⁻¹ * (ρK.r * zL * ρK.r⁻¹) = ρK.r * (zL * zL) * ρK.r⁻¹ := by group
        _ = 1 := by rw [hzL.sq]; group
    have hcz : zL * z = z * zL := by
      have h5 : (z * zL)⁻¹ = z * zL := inv_eq_of_mul_eq_one_right hsq
      rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hs.hz.sq,
        inv_eq_of_mul_eq_one_right hzL.sq] at h5
    have hM1 : IsUniqueInvolution (conjSub ρL.r K) (z * zL) := by
      have := hs.hz.conj ρL.r
      rwa [hconj', hcz] at this
    have hM2 : IsUniqueInvolution (conjSub ρK.r L) (z * zL) := by
      have := hzL.conj ρK.r
      rwa [hconj] at this
    have hnt := T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins
      (hΩ.conjInvariant ρL.r K hK)
    have hM : conjSub ρK.r L = conjSub ρL.r K :=
      hnt _ ⟨hΩ.conjInvariant ρK.r L hL, z * zL, hM1, hM2⟩
    have h6 : conjSub ρL.r K ≤ X := by
      rw [← hM]
      have := conjSub_mono (n := ρK.r) hLX
      rwa [hRXc] at this
    apply hKX
    have h7 := conjSub_mono (n := ρL.r⁻¹) h6
    rw [conjSub_inv_conjSub, conjSub_eq_self_of_mem (X.inv_mem hrLX)] at h7
    exact h7

end Key

end T8S2

end CFSG.ClassicalInvolution.Asc77
