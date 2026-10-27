module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu
public import CFSG.ClassicalInvolution.Q3.Q3MTBig
public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)

section Reps

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem no_three_reps_E4_gen (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h12 : ρ₁.K ≠ ρ₂.K) (h13 : ρ₁.K ≠ ρ₃.K) (h23 : ρ₂.K ≠ ρ₃.K) :
    False := by
  obtain ⟨φ⟩ := hE
  have hcomm : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hsq : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1 := fun ρ =>
    Q3T6.Mu.muDelta_mul_self hP.hyp hW (MuTab.muTabElt_mem ρ)
  have hne1 : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ ≠ 1 := fun ρ =>
    muDelta_ne_one hW (MuTab.muTabElt_mem ρ)
  have hdne : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → MuTab.muTabElt ρ ≠ MuTab.muTabElt σ :=
    fun ρ σ h e => h ((Q3T6.Mu.muTabElt_eq_iff hP hW ρ σ).mp e)
  have hnbr : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → σ.K ∈ omegaNbr Ω ρ.K := fun ρ σ h =>
    (Q3T6.Mu.muTab_commute_iff hP hW ρ σ h).mp (hcomm _ _)
  have h13' := hnbr ρ₁ ρ₃ h13
  have h23' := hnbr ρ₂ ρ₃ h23
  exact MuTab.not_indep3_klein φ (a := MuTab.muTabElt ρ₁) (b := MuTab.muTabElt ρ₂)
    (c := MuTab.muTabElt ρ₃) ⟨hsq ρ₁, hsq ρ₂, hsq ρ₃, hne1 ρ₁, hne1 ρ₂, hne1 ρ₃,
      hcomm _ _, hcomm _ _, hcomm _ _, hdne ρ₁ ρ₂ h12, (hdne ρ₁ ρ₃ h13).symm,
      (hdne ρ₂ ρ₃ h23).symm, Q3MT.muTabElt_ne_mul hP hW ρ₁ ρ₂ ρ₃ h13' h23'⟩

theorem exists_rep_ne_E4_gen (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ : Rep Ω W) : ∃ σ : Rep Ω W, σ.K ≠ ρ.K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨φ⟩ := hE
  have h2 : MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1 :=
    Q3T6.Mu.muDelta_mul_self hP.hyp hW (MuTab.muTabElt_mem ρ)
  have hall : ∀ d ∈ muDelta Ω W, d = MuTab.muTabElt ρ := by
    intro d hd
    obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
    rw [Q3T6.Mu.muTabElt_eq_iff hP hW, hcon σ]
  have hcl : (Subgroup.closure (muDelta Ω W) : Subgroup ↥(muGroup Ω W)) = ⊤ :=
    closure_muDelta_eq_top Ω W
  have hsub : (Subgroup.closure (muDelta Ω W) : Subgroup ↥(muGroup Ω W)) ≤
      Subgroup.zpowers (MuTab.muTabElt ρ) := by
    rw [Subgroup.closure_le]
    intro d hd
    rw [hall d hd]
    exact Subgroup.mem_zpowers _
  rw [hcl] at hsub
  have hcard : Nat.card (Subgroup.zpowers (MuTab.muTabElt ρ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2))
  have h4 : Nat.card ↥(muGroup Ω W) = 4 := by
    rw [Nat.card_congr φ.toEquiv]
    simp
  have : Nat.card ↥(muGroup Ω W) ≤ Nat.card (Subgroup.zpowers (MuTab.muTabElt ρ)) := by
    have := Subgroup.card_le_of_le hsub
    simpa using this
  omega

theorem exists_conj_eta (hcl : ConjInvariant Ω) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω)
    (S : Sylow 2 G) :
    ∃ (g : G) (η : Set (Subgroup G)), η ∈ etaSet Ω (S : Subgroup G) ∧
      (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
        conjSub g W₀ = ⨆ U ∈ η, U := by
  obtain ⟨η₀, ⟨S₀, hη₀, hinv⟩, rfl⟩ := hW₀
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S
  refine ⟨g, conjSub g '' η₀, ?_, ?_, ?_⟩
  · have := conjSub_image_mem_etaSet hcl hη₀ g
    rwa [hg] at this
  · rintro s hs _ ⟨U, hU, rfl⟩
    rw [← hg, mem_conjSub_iff] at hs
    refine ⟨conjSub (g⁻¹ * s * g) U, hinv _ hs U hU, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  · rw [conjSub_iSup₂, iSup_image]

end Reps

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.exists_unique_member_E4 (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y))
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    ∃ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
        L ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) →
          2 < Nat.card ↥(L ⊓ (S₂ : Subgroup Y)) → L = J₂ := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hP : Q3CL.PartIHypG Ω := hs.partIHypG
  obtain ⟨g, η₂, hη₂, hinv₂, hgW⟩ := exists_conj_eta hΩ.conjInvariant hs.hW.1 S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup Y := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup Y), s ∈ Subgroup.normalizer (W₂ : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup Y) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := Q3CL.T8.ctxOf hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    rw [← hgW]
    exact ⟨(muGroupConjEquivGen hΩ g W).symm.trans φ⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  have hρKK : ρK.K = K := rfl
  obtain ⟨σ, hσ⟩ := exists_rep_ne_E4_gen hP hW₂ hE₂ ρK
  have hcomm : ∀ x y : ↥(muGroup Ω W₂), x * y = y * x := by
    obtain ⟨φ⟩ := hE₂
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hnbr : σ.K ∈ omegaNbr Ω K :=
    (Q3T6.Mu.muTab_commute_iff hP hW₂ ρK σ (Ne.symm hσ)).mp (hcomm _ _)
  refine ⟨σ.K, hnbr, fun L hL hLX hcard => ?_⟩
  have h611 : L ⊓ W₂ ∈ η₂ := Sec6Gen.l6_11Gen Y Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := Sec6Gen.isPGroup_of_mem_USet hΩ hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := exists_rep_of_involution_mem_gen c₂ hP.cls hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_cases hLK : L = K
  · exact absurd (hLK ▸ hLX) hKX
  by_contra hLσ
  exact no_three_reps_E4_gen hP hW₂ hE₂ ρK σ ρL (Ne.symm hσ)
    (by rw [hρKK, hρLL]; exact Ne.symm hLK) (by rw [hρLL]; exact Ne.symm hLσ)

theorem TightStd8R.exists_sylow_meeting_X (hs : TightStd8R r n Rd Sd z J S R T W t) :
    ∃ S₂ : Sylow 2 Y, R ≤ (S₂ : Subgroup Y) ∧
      IsSylow2In ((S₂ : Subgroup Y) ⊓
        omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
        (omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  set X : Subgroup Y := omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
    with hXdef
  have hΩ := hs.hyp
  have hRsyl : IsSylow2In R (tightCore Rd) :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hs.hR.1 hs.hR.2.1
  have hRN : ∀ r ∈ R, conjSub r X = X := fun r hr =>
    conjSub_omegaNbrGen_of_conjSub_eq hΩ.conjInvariant (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
  have hYN : X ⊔ R ≤ Subgroup.normalizer (X : Set Y) :=
    sup_le Subgroup.le_normalizer (fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRN r hr))
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hRsyl.2.1 (le_sup_right : R ≤ X ⊔ R)
  have hVX : IsSylow2In (V ⊓ X) X := AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hYN
  obtain ⟨S₂, hS₂⟩ := hV.2.1.exists_le_sylow
  have heq : (S₂ : Subgroup Y) ⊓ X = V ⊓ X :=
    hVX.2.2 _ inf_le_right S₂.isPGroup'.to_inf_left (inf_le_inf_right X hS₂)
  exact ⟨S₂, hRV.trans hS₂, heq ▸ hVX⟩

theorem TightStd8R.exists_muIsoZ2_xFam_E4_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    ∃ W' ∈ WSet (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)),
      MuIsoZ2 (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) W' := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set X : Subgroup Y := omegaNbrGen Ω (tightCore Rd) with hXdef
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨S₂, hRS₂, hS₂X⟩ := hs.exists_sylow_meeting_X
  obtain ⟨J₂, hJ₂, hK1⟩ := hs.exists_unique_member_E4 hE hRS₂ hKX
  have hJ₂X : J₂ ≤ X := le_omegaNbrGen hJ₂
  refine exists_muIsoZ2_of_sylow_gen (Λ := restrictFamily Ω X) (h.restrict X).hyp
    ⟨h.xFam.hyp, h.xFam.cls, aEmpty_xFam h⟩ (AscP1Nine3.sylowOfIsSylow2In₉ hS₂X)
    (J₀ := J₂.subgroupOf X) ⟨J₂, hJ₂.1, hJ₂X, rfl⟩ ?_
  rintro _ ⟨L, hL, hLX, rfl⟩ hcard
  have hSH : ((AscP1Nine3.sylowOfIsSylow2In₉ hS₂X : Sylow 2 ↥X) : Subgroup ↥X) =
      ((S₂ : Subgroup Y) ⊓ X).subgroupOf X := rfl
  have hLS : L ⊓ (S₂ : Subgroup Y) ≤ X := inf_le_left.trans hLX
  have hinf : L.subgroupOf X ⊓ ((S₂ : Subgroup Y) ⊓ X).subgroupOf X =
      (L ⊓ (S₂ : Subgroup Y)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hSH, hinf] at hcard
  have hc2 : Nat.card ↥((L ⊓ (S₂ : Subgroup Y)).subgroupOf X) =
      Nat.card ↥(L ⊓ (S₂ : Subgroup Y)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
  rw [hc2] at hcard
  rw [hK1 L hL hLX hcard]

theorem TightStd8R.dEdgeless_xFam_E4_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    DEdgeless (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨W', hW', hZ2⟩ := hs.exists_muIsoZ2_xFam_E4_of_not_le hKX hE
  exact dEdgeless_of_muIsoZ2_gen ⟨h.xFam.hyp, h.xFam.cls, aEmpty_xFam h⟩ hW' hZ2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
