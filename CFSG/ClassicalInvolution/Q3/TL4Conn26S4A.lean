module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4X

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)

theorem perm4_partner_transp : ∀ a : Equiv.Perm (Fin 4), s26IsTransp a →
    ∃ b : Equiv.Perm (Fin 4), s26IsTransp b ∧ b ≠ a ∧ a * b = b * a := by decide

theorem perm4_eq_of_comm_transp {a b c : Equiv.Perm (Fin 4)} (ha : s26IsTransp a)
    (hb : s26IsTransp b) (hc : s26IsTransp c) (hba : b ≠ a) (hab : a * b = b * a) (hca : c ≠ a)
    (hac : a * c = c * a) : c = b := by
  by_contra hcb
  exact (s26_perm4_comm a b c ha hb (Ne.symm hba) hab hc hca hcb).1 hac.symm

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem s26Elt_eq_iff_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) :
    s26Elt ρ = s26Elt σ ↔ ρ.K = σ.K :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem conj_involution_of_noncomm_gen (c : Q3CL.Thompson.Ctx Ω W) (σ ρ : Rep Ω W)
    (hnc : σ.img * ρ.img ≠ ρ.img * σ.img) {zσ j : G} (hz : IsUniqueInvolution σ.K zσ)
    (hj : IsUniqueInvolution ρ.K j) : σ.r * j * σ.r⁻¹ = zσ * j := by
  have hne : σ.K ≠ ρ.K := fun h => hnc (by rw [c.img_eq_of_K_eq σ ρ h])
  have hnot : ρ.K ∉ omegaNbr Ω σ.K := fun h => hnc (c.comm_of_omega σ ρ h)
  exact c.conj_involution σ ρ hne hnot hz hj

end Gen

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.exists_third_S4 (hs : TightStd8R r n Rd Sd z J S R T W t)
    (φ : ↥(muGroup (CoreAssembly.conjClass (tightCore Rd)) W) ≃* Equiv.Perm (Fin 4)) :
    ∃ P ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W,
      ∃ M ∈ CoreAssembly.conjClass (tightCore Rd), IsSylow2In P M ∧ M ≠ tightCore Rd ∧
        M ≠ J ∧ M ∉ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J := by
  revert φ
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  intro φ
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hP := hs.partIHypG
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup Y), s ∈ Subgroup.normalizer (W : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  obtain ⟨r₀, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hRD
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  let ρ : Rep Ω W := ⟨K, R, r₀, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hTT' := T7A.isTT_map_equiv hTT φ
  have hρσ : s26Elt ρ ≠ s26Elt σ := fun h => hs.hJ.2.1 ((s26Elt_eq_iff_gen c ρ σ).mp h).symm
  have hcomm : s26Elt ρ * s26Elt σ = s26Elt σ * s26Elt ρ :=
    Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  have hex : ∃ P ∈ DSet Ω W, ∃ M ∈ Ω, IsSylow2In P M ∧ M ≠ K ∧ M ≠ J := by
    by_contra hno
    push Not at hno
    have hsub : ∀ d ∈ muDelta Ω W, d = s26Elt ρ ∨ d = s26Elt σ := by
      rintro d ⟨R', hR', r', hr', hr'W, hd⟩
      obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'.1
      let ρ' : Rep Ω W := ⟨M, R', r', hM, hR', hR'M, hr', hr'W⟩
      have hdρ' : d = s26Elt ρ' := Subtype.ext hd
      by_cases hMK : M = K
      · left
        rw [hdρ']
        exact (s26Elt_eq_iff_gen c ρ' ρ).mpr hMK
      · right
        have hMJ : M = J := hno R' hR' M hM hR'M hMK
        rw [hdρ']
        exact (s26Elt_eq_iff_gen c ρ' σ).mpr hMJ
    obtain ⟨τ, hτT, hτ1, hτ2⟩ := s26_perm4_third (φ (s26Elt ρ)) (φ (s26Elt σ))
    have hτΔ : τ ∈ φ '' muDelta Ω W := (s26_tt_iff hTT' τ).mpr hτT
    obtain ⟨d, hd, rfl⟩ := hτΔ
    rcases hsub d hd with rfl | rfl
    · exact hτ1 rfl
    · exact hτ2 rfl
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ⟩ := hex
  refine ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, fun hnbr => ?_⟩
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hcommP : s26Elt σ * s26Elt ρP = s26Elt ρP * s26Elt σ :=
    Subtype.ext (c.comm_of_omega σ ρP hnbr)
  have hPρ : s26Elt ρP ≠ s26Elt ρ := fun h => hMK ((s26Elt_eq_iff_gen c ρP ρ).mp h)
  have hPσ : s26Elt ρP ≠ s26Elt σ := fun h => hMJ ((s26Elt_eq_iff_gen c ρP σ).mp h)
  have hmem : ∀ ρ' : Rep Ω W, s26IsTransp (φ (s26Elt ρ')) := fun ρ' =>
    (s26_tt_iff hTT' (φ (s26Elt ρ'))).mp ⟨s26Elt ρ', s26Elt_mem ρ', rfl⟩
  have hρσ' : φ (s26Elt ρ) ≠ φ (s26Elt σ) := fun h => hρσ (φ.injective h)
  have hc' : φ (s26Elt ρ) * φ (s26Elt σ) = φ (s26Elt σ) * φ (s26Elt ρ) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hPρ' : φ (s26Elt ρP) ≠ φ (s26Elt ρ) := fun h => hPρ (φ.injective h)
  have hPσ' : φ (s26Elt ρP) ≠ φ (s26Elt σ) := fun h => hPσ (φ.injective h)
  have := (s26_perm4_comm _ _ _ (hmem ρ) (hmem σ) hρσ' hc' (hmem ρP) hPρ' hPσ').2
  apply this
  rw [← map_mul, ← map_mul, ← hcommP]

theorem TightStd8R.exists_unique_member_S4 (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y))
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    ∃ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
        L ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) →
          2 < Nat.card ↥(L ⊓ (S₂ : Subgroup Y)) → L = J₂ := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  set X : Subgroup Y := omegaNbrGen Ω K with hXdef
  have h := TightLargeHypR.typeRFam hs.large
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
  have hS4₂ : MuIsoS4 Ω W₂ := by
    obtain ⟨φ⟩ := hS4
    rw [← hgW]
    exact ⟨(muGroupConjEquivGen hΩ g W).symm.trans φ⟩
  obtain ⟨φ₂⟩ := hS4₂
  have hTT : Star3T.IsTT (muDelta Ω W₂) := Q3T6.Mu.isTT_muDelta hP hW₂
  have hTT' := T7A.isTT_map_equiv hTT φ₂
  have hmem : ∀ ρ : Rep Ω W₂, s26IsTransp (φ₂ (MuTab.muTabElt ρ)) := fun ρ =>
    (s26_tt_iff hTT' _).mp ⟨_, MuTab.muTabElt_mem ρ, rfl⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  obtain ⟨b, hbT, hba, hab⟩ := perm4_partner_transp _ (hmem ρK)
  obtain ⟨d, hd, hdb⟩ : b ∈ φ₂ '' muDelta Ω W₂ := (s26_tt_iff hTT' b).mpr hbT
  obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
  have hne : ρK.K ≠ σ.K := fun e =>
    hba (by rw [← hdb, (Q3T6.Mu.muTabElt_eq_iff hP hW₂ σ ρK).mpr e.symm])
  have hcomm : MuTab.muTabElt ρK * MuTab.muTabElt σ = MuTab.muTabElt σ * MuTab.muTabElt ρK := by
    apply φ₂.injective
    rw [map_mul, map_mul, hdb]
    exact hab
  have hnbr : σ.K ∈ omegaNbr Ω ρK.K := (Q3T6.Mu.muTab_commute_iff hP hW₂ ρK σ hne).mp hcomm
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
  have hrLX : ρL.r ∈ X := by
    have h1 : ρL.r ∈ ρL.K := ρL.hRK.1 ρL.hr
    rw [hρLL] at h1
    exact hLX h1
  have hRXc : conjSub ρK.r X = X :=
    conjSub_omegaNbrGen_of_conjSub_eq hΩ.conjInvariant (conjSub_eq_self_of_mem (hs.hR.2.1 hr₀R))
  by_cases hcm : MuTab.muTabElt ρK * MuTab.muTabElt ρL = MuTab.muTabElt ρL * MuTab.muTabElt ρK
  · by_cases hKL : ρL.K = ρK.K
    · exfalso
      have hLK : L = K := by rw [← hρLL, hKL]
      exact hKX (hLK ▸ hLX)
    · have hc : φ₂ (MuTab.muTabElt ρL) = b := by
        refine perm4_eq_of_comm_transp (hmem ρK) hbT (hmem ρL) hba hab ?_ ?_
        · intro e
          exact hKL ((Q3T6.Mu.muTabElt_eq_iff hP hW₂ ρL ρK).mp (φ₂.injective e))
        · rw [← map_mul, ← map_mul, hcm]
      have hLσ : MuTab.muTabElt ρL = MuTab.muTabElt σ := φ₂.injective (hc.trans hdb.symm)
      rw [← hρLL]
      exact (Q3T6.Mu.muTabElt_eq_iff hP hW₂ ρL σ).mp hLσ
  · exfalso
    have hnc : ρK.img * ρL.img ≠ ρL.img * ρK.img := fun e => hcm (Subtype.ext e)
    have hnc' : ρL.img * ρK.img ≠ ρK.img * ρL.img := fun e => hnc e.symm
    have hzL' : IsUniqueInvolution ρL.K zL := by rw [hρLL]; exact hzL
    have hconj : ρK.r * zL * ρK.r⁻¹ = z * zL :=
      conj_involution_of_noncomm_gen c₂ ρK ρL hnc hs.hz hzL'
    have hconj' : ρL.r * z * ρL.r⁻¹ = zL * z :=
      conj_involution_of_noncomm_gen c₂ ρL ρK hnc' hzL' hs.hz
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
    have hKr : conjSub ρL.r K ∈ Ω := hΩ.conjInvariant ρL.r K hK
    have hM : conjSub ρK.r L = conjSub ρL.r K :=
      h.noTwins _ hKr _ ⟨hΩ.conjInvariant ρK.r L hL, z * zL, hM1, hM2⟩
    have h6 : conjSub ρL.r K ≤ X := by
      rw [← hM]
      have := conjSub_mono (n := ρK.r) hLX
      rwa [hRXc] at this
    apply hKX
    have h7 := conjSub_mono (n := ρL.r⁻¹) h6
    rw [conjSub_inv_conjSub, conjSub_eq_self_of_mem (X.inv_mem hrLX)] at h7
    exact h7

theorem TightStd8R.exists_muIsoZ2_xFam_S4_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    ∃ W' ∈ WSet (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)),
      MuIsoZ2 (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) W' := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set X : Subgroup Y := omegaNbrGen Ω (tightCore Rd) with hXdef
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨S₂, hRS₂, hS₂X⟩ := hs.exists_sylow_meeting_X
  obtain ⟨J₂, hJ₂, hK1⟩ := hs.exists_unique_member_S4 hS4 hRS₂ hKX
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

theorem TightStd8R.dEdgeless_xFam_S4_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    DEdgeless (xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨W', hW', hZ2⟩ := hs.exists_muIsoZ2_xFam_S4_of_not_le hKX hS4
  exact dEdgeless_of_muIsoZ2_gen ⟨h.xFam.hyp, h.xFam.cls, aEmpty_xFam h⟩ hW' hZ2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
