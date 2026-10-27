module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Pkg
public import CFSG.ClassicalInvolution.Sp62Rec.I1.ActionData
import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot
import CFSG.ClassicalInvolution.Sp62Rec.I1.TwinCentralizer
import CFSG.ClassicalInvolution.Sp62Rec.I1.AutConj
import CFSG.ClassicalInvolution.Sp62Rec.I1.HatOfData
import CFSG.ClassicalInvolution.Sp62Rec.I1.WeightFour
import CFSG.ClassicalInvolution.Sp62Rec.I1.WIsoHhat
import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
import CFSG.ClassicalInvolution.Q3.TL4AECoverD
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z6M

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23


variable {Y : Type} [Group Y] [Finite Y]

section Core


theorem i1_action_lab {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) {Z : Subgroup Y}
    (hAE : SecAE R e 6) (hI : I1In R t e Z) {J J' : Subgroup Y}
    (hJ : J ∈ tqMembers3 (Om R) e) (hJ' : J' ∈ tqMembers3 (Om R) e) (hne : J' ≠ J)
    (hzJ : IsUniqueInvolution J t) (hzJ' : IsUniqueInvolution J' t)
    (hcomm : ∀ x ∈ Z, ∀ l ∈ J ⊔ J',
      x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)))
    (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
    (hΘ : Θ ⟨allOnes 6, Sp62Rec.I1.allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat⟩) :
    ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (φ : ↥(Z ⊔ rLayer (Om R) e) →* ↥Hhat),
      I1Action t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) f Θ φ ∧
      ∃ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool),
        ((TwinADescent.coreAt e J).subgroupOf (rLayer (Om R) e)).map f = memAt β hβ b ∧
        ((TwinADescent.coreAt e J').subgroupOf (rLayer (Om R) e)).map f = memAt β hβ (!b) := by
  classical
  have hsq : e * e = 1 := (hI.Z_elem e hI.e_mem e hI.e_mem).2
  have SD : SecData R e := SecData.of_perp hP hsq
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer SD.hΩ hc2 SD.two
  set E := rLayer (Om R) e with hE
  set B := Z ⊔ E with hB
  have hZC : Z ≤ Subgroup.centralizer ({e} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hI.Z_elem x hx e hI.e_mem).1
  have hEC : E ≤ Subgroup.centralizer ({e} : Set Y) := TwinPerpV3.rLayer_le_centralizer _ _
  have hBC : B ≤ Subgroup.centralizer ({e} : Set Y) := sup_le hZC hEC
  have hEB : E ≤ B := le_sup_right
  have hEn := rLayer_map_conj_eq R e
  rw [← hE] at hEn
  have hEn' : ∀ g ∈ B, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    have h1 := hEn g (hBC hg)
    have h2 : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h1] at h2
  have heE : e ∈ E := mem_rLayer_self hI
  set Φ := TwinDisc.secFam (Om R) e with hΦ
  obtain ⟨I⟩ := hAE
  have hH := aeCoverHyp_of_I1 SD I hJ hJ' hne hzJ hzJ'
  have hker : I.φ.ker ≠ ⊥ :=
    ker_ne_bot_of_central SD.q8 I (c := secOf hmap ⟨e, heE⟩) (secOf_central hmap heE)
      (secOf_ne_one hmap heE hsq hI.e_ne_one)
  obtain ⟨-, hbot | ⟨ψ, hψ, hψm⟩⟩ := Sec13.aeCover_ker hH (by norm_num : 5 ≤ 6)
  · exact absurd hbot hker
  have hgen : pSpan Φ = ⊤ := TwinDisc.AE5.hgen_of SD.q8
  have hperfP : Group.IsPerfect ↥(pSpan Φ) :=
    TL4.AECov.isPerfect_pSpan I (by norm_num) hH.card hH.conj_mem hH.label_inj
  haveI := hperfP
  have hperfA : Group.IsPerfect ↥(aeSub 6) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  let eqTop : ↥(pSpan Φ) ≃* SecQ R e := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hperfX : Group.IsPerfect (SecQ R e) :=
    Group.IsPerfect.ofSurjective (f := eqTop.toMonoidHom) eqTop.surjective
  let q0 : ↥E →* ↥(pSpan Φ) := eqTop.symm.toMonoidHom.comp (secOf hmap)
  have hq0 : Function.Surjective q0 := eqTop.symm.surjective.comp (secOf_surjective hmap)
  have hq0coe : ∀ y : ↥E, ((q0 y : ↥(pSpan Φ)) : SecQ R e) = secOf hmap y := fun y => rfl
  let f : ↥E →* Wr 6 := ((aeSub 6).subtype.comp ψ.toMonoidHom).comp q0
  have hfr : f.range = aeSub 6 := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ (q0 x)).2
    · intro ha
      obtain ⟨y, hy⟩ := ψ.surjective ⟨a, ha⟩
      obtain ⟨x, rfl⟩ := hq0 y
      exact ⟨x, congrArg Subtype.val hy⟩
  have hfk : f.ker = (oddCoreIn E).subgroupOf E := by
    rw [← secOf_ker hmap]
    ext x
    show ((ψ (q0 x) : ↥(aeSub 6)) : Wr 6) = 1 ↔ _
    constructor
    · intro h
      have h1 : ψ (q0 x) = 1 := Subtype.ext h
      have h2 : q0 x = 1 := ψ.injective (h1.trans (map_one ψ).symm)
      have h3 : secOf hmap x = 1 := by
        have := congrArg (fun y : ↥(pSpan Φ) => (y : SecQ R e)) h2
        exact this
      exact h3
    · intro h
      have h3 : secOf hmap x = 1 := h
      have h2 : q0 x = 1 := Subtype.ext h3
      rw [h2, map_one]; rfl
  have hcbarcen : ∀ y : ↥(pSpan Φ), y * q0 ⟨e, heE⟩ = q0 ⟨e, heE⟩ * y := by
    intro y
    apply eqTop.injective
    rw [map_mul, map_mul]
    have h0 : eqTop (q0 ⟨e, heE⟩) = secOf hmap ⟨e, heE⟩ := rfl
    rw [h0]
    exact (secOf_central hmap heE (eqTop y)).symm
  have hcbarker : q0 ⟨e, heE⟩ ∈ I.φ.ker :=
    AEIdent.center_le_ker (by norm_num : 5 ≤ 6) I (Subgroup.mem_center_iff.mpr hcbarcen)
  have hcbar1 : q0 ⟨e, heE⟩ ≠ 1 := fun h =>
    secOf_ne_one hmap heE hsq hI.e_ne_one (congrArg (fun y : ↥(pSpan Φ) => (y : SecQ R e)) h)
  have hfe : f ⟨e, heE⟩ = allOnes 6 := Sp62Rec.I1.psi_eq_allOnes I ψ hψ hcbarker hcbar1
  have hκ : ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∃ w : Wr 6, ActsOnE f h w := by
    intro h hh
    let g' : ↥(Subgroup.centralizer ({e} : Set Y)) := ⟨h, hh⟩
    let α' : SecQ R e ≃* SecQ R e := TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g'
    have hα'Φ : ∀ L ∈ Φ, L.map α'.toMonoidHom ∈ Φ := fun L hL =>
      TwinExitPf10.secAut_map_secFam SD.hΩ hc2 g' hL
    obtain ⟨αP', hαP', hαPΦ'⟩ := Sp62Rec.I1.exists_restrict_aut hgen α' hα'Φ
    obtain ⟨w, hw⟩ := Sp62Rec.I1.exists_conj_of_aut I hperfP ψ hψ αP' hαPΦ'
    refine ⟨w, fun x hx hx' => ?_⟩
    have h1 : q0 ⟨h * x * h⁻¹, hx'⟩ = αP' (q0 ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [hq0coe, hαP', hq0coe]
      exact secOf_conj SD.hΩ hc2 hmap g' ⟨x, hx⟩ _
    show ((ψ (q0 ⟨h * x * h⁻¹, hx'⟩) : ↥(aeSub 6)) : Wr 6) =
      w * ((ψ (q0 ⟨x, hx⟩) : ↥(aeSub 6)) : Wr 6) * w⁻¹
    rw [h1, hw]
  obtain ⟨ρ, hρ, hρker⟩ := hI.S6
  set N : Subgroup ↥B := E.subgroupOf B with hNdef
  haveI hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff hEB]
    intro h g hh hg
    exact hEn' g hg h hh
  let eEN : ↥N ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEB
  let Zs : Subgroup ↥B := Z.subgroupOf B
  have hZs : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext
      (hI.Z_elem _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)).1
  have hsup : Zs ⊔ N = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := Z) (A' := E) (B := B) le_sup_left le_sup_right
    have h2 : ((Z ⊔ E).subgroupOf B) = ⊤ := Subgroup.subgroupOf_self B
    rw [h2] at h1
    exact h1.symm
  have hunit : ∀ u : ℤˣ, Odd (orderOf u) → u = 1 := by
    intro u hu
    rcases Int.units_eq_one_or u with h | h
    · exact h
    · exfalso
      rw [h] at hu
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : orderOf (-1 : ℤˣ) = 2 := orderOf_eq_prime (by decide) (by decide)
      rw [h2] at hu
      exact absurd hu (by decide)
  have hsign : ∀ x ∈ N, Equiv.Perm.sign (ρ x) = 1 := by
    let q : ↥N →* SecQ R e := (secOf hmap).comp eEN.toMonoidHom
    have hq : Function.Surjective q := (secOf_surjective hmap).comp eEN.surjective
    let s : ↥N →* ℤˣ := Equiv.Perm.sign.comp (ρ.comp N.subtype)
    have hs : q.ker ≤ s.ker := by
      intro x hx
      have h1 : eEN x ∈ (secOf hmap).ker := hx
      rw [secOf_ker, Subgroup.mem_subgroupOf] at h1
      have h2 : Odd (orderOf (((x : ↥B) : Y))) :=
        Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.orderOf_dvd_natCard _ h1)
      have h3 : orderOf x = orderOf (((x : ↥B) : Y)) := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      have h4 : Odd (orderOf (s x)) := Odd.of_dvd_nat (h3 ▸ h2) (orderOf_map_dvd s x)
      exact hunit _ h4
    have := Sp62Rec.I1.hom_eq_one_of_perfect_quotient q hq hperfX s hs
    intro x hx
    exact DFunLike.congr_fun this ⟨x, hx⟩
  obtain ⟨τ', hτ'Zs, hτ'N, hτ'sign, hΓ⟩ :=
    Sp62Rec.I1.exists_odd_mem_of_perm_quotient N Zs hZs hsup ρ hρ hρker hsign
  have hτ'Z : (τ' : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hτ'Zs
  have hτC : (τ' : Y) ∈ Subgroup.centralizer ({e} : Set Y) := hZC hτ'Z
  have hτ2 : (τ' : Y) * (τ' : Y) = 1 := (hI.Z_elem _ hτ'Z _ hτ'Z).2
  let g : ↥(Subgroup.centralizer ({e} : Set Y)) := ⟨(τ' : Y), hτC⟩
  have hg2 : g * g = 1 := Subtype.ext hτ2
  let αX : SecQ R e ≃* SecQ R e := TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g
  have hαΦ : ∀ L ∈ Φ, L.map αX.toMonoidHom ∈ Φ := fun L hL =>
    TwinExitPf10.secAut_map_secFam SD.hΩ hc2 g hL
  have hK := TwinDisc.secImg_mem_secFam hJ
  have hK' := TwinDisc.secImg_mem_secFam hJ'
  obtain ⟨htC, htY, hU⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ hzJ
  obtain ⟨htC', htY', hU'⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ' hzJ'
  have hneK : TwinDisc.secImg (Om R) e J' ≠ TwinDisc.secImg (Om R) e J :=
    (TwinPerpV3.secImg_ne_of_twin SD.hΩ hc2 hJ hJ' hne.symm hzJ hzJ').symm
  have hτt : (τ' : Y) * t = t * (τ' : Y) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hI.Z_le hτ'Z)
  have hαz : αX (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e))) =
      QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    refine TwinExitPf6.secAut_mk SD.hΩ hc2 g _ _ (Subtype.ext ?_)
    show t = (τ' : Y) * t * (τ' : Y)⁻¹
    rw [hτt]; group
  have hodd := secAut_odd_of_twin SD g hJ
    (fun l hl => hcomm (τ' : Y) hτ'Z l (Subgroup.mem_sup_left hl))
  have hodd' := secAut_odd_of_twin SD g hJ'
    (fun l hl => hcomm (τ' : Y) hτ'Z l (Subgroup.mem_sup_right hl))
  have hfix := Sp62Rec.I1.aut_fixes_twins hH hK hK' hneK hU hU' αX hαΦ hαz hodd hodd'
  obtain ⟨αP, hαP, hαPΦ⟩ := Sp62Rec.I1.exists_restrict_aut hgen αX hαΦ
  obtain ⟨w, hw⟩ := Sp62Rec.I1.exists_conj_of_aut I hperfP ψ hψ αP hαPΦ
  have hαX2 : ∀ y : SecQ R e, αX (αX y) = y := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
    haveI hHn := TwinExitPf6.normal_coreHull SD.hΩ hc2
    let h1 : ↥(coreHull (Om R) e) :=
      ⟨g * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) * g⁻¹,
        hHn.conj_mem _ h.2 g⟩
    have e1 := TwinExitPf6.secAut_mk SD.hΩ hc2 g h h1 rfl
    have e2 := TwinExitPf6.secAut_mk SD.hΩ hc2 g h1 h (by
      show ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) =
        g * (g * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) * g⁻¹) * g⁻¹
      calc ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y)))
          = (g * g) * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) *
              (g * g)⁻¹ := by rw [hg2]; simp
        _ = _ := by group)
    show αX (αX (QuotientGroup.mk' _ h)) = QuotientGroup.mk' _ h
    rw [e1, e2]
  have hαsq : ∀ x : ↥(pSpan Φ), αP (αP x) = x := fun x =>
    Subtype.ext (by rw [hαP, hαP]; exact hαX2 _)
  have hτf : ∀ (x : Y) (hx : x ∈ E),
      f ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩ = w * f ⟨x, hx⟩ * w⁻¹ := by
    intro x hx
    have h1 : q0 ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩ = αP (q0 ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [hq0coe, hαP, hq0coe]
      exact secOf_conj SD.hΩ hc2 hmap g ⟨x, hx⟩ _
    show ((ψ (q0 ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩) : ↥(aeSub 6)) : Wr 6) =
      w * ((ψ (q0 ⟨x, hx⟩) : ↥(aeSub 6)) : Wr 6) * w⁻¹
    rw [h1, hw]
  obtain ⟨β, hβ, b, hlab, hlab'⟩ := Sp62Rec.I1.twin_labels_abs hH hK hK' hneK hU hU'
  have hcommL : ∀ (L : Subgroup (SecQ R e)) (hL : L ∈ Φ), L ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' → ∀ (b' : Bool),
      (L.subgroupOf (pSpan Φ)).map I.φ = memBar β hβ b' → ∀ x ∈ memAt β hβ b', w * x = x * w := by
    intro L hL hLle b' hlabL x hx
    have hx' := hψm L hL β hβ b' hlabL
    rw [← hx'] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := ha
    have hyL : (y : SecQ R e) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hαy : αP y = y := Subtype.ext (by rw [hαP]; exact hfix _ (hLle hyL))
    have h1 := hw y
    rw [hαy] at h1
    show w * (ψ y : Wr 6) = (ψ y : Wr 6) * w
    calc w * (ψ y : Wr 6) = (w * (ψ y : Wr 6) * w⁻¹) * w := by group
      _ = (ψ y : Wr 6) * w := by rw [← h1]
  have hKle : TwinDisc.secImg (Om R) e J ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' := le_sup_left
  have hK'le : TwinDisc.secImg (Om R) e J' ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' := le_sup_right
  have h1 : ∀ x ∈ memAt β hβ true, w * x = x * w := by
    cases b
    · exact hcommL _ hK' hK'le true (by simpa using hlab')
    · exact hcommL _ hK hKle true hlab
  have h2 : ∀ x ∈ memAt β hβ false, w * x = x * w := by
    cases b
    · exact hcommL _ hK hKle false hlab
    · exact hcommL _ hK' hK'le false (by simpa using hlab')
  let f' : ↥N →* Wr 6 := f.comp eEN.toMonoidHom
  have hρN : N.subtype.range.map ρ = alternatingGroup (Fin 6) := by
    rw [Subgroup.range_subtype]
    exact Sp62Rec.I1.map_perm_eq_alternating N Zs hZs hsup ρ hρ hsign
  have hfalt : ∀ s ∈ alternatingGroup (Fin 6), ∃ x : ↥N, (f' x).perm = s := by
    intro s hs
    have hmem : (⟨0, s⟩ : Wr 6) ∈ aeSub 6 :=
      mem_aeSub.2 ⟨by simp [wsum], Equiv.Perm.mem_alternatingGroup.mp hs⟩
    rw [← hfr] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨eEN.symm y, by
      show (f (eEN (eEN.symm y))).perm = s
      rw [MulEquiv.apply_symm_apply, hy]⟩
  have hoddK : ∀ x : ↥N, f' x = 1 → Odd (orderOf x) := by
    intro x hx
    have h1 : eEN x ∈ f.ker := hx
    rw [hfk, Subgroup.mem_subgroupOf] at h1
    have h2 : Odd (orderOf (((x : ↥B) : Y))) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.orderOf_dvd_natCard _ h1)
    have h3 : orderOf x = orderOf (((x : ↥B) : Y)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h3]; exact h2
  have hkerρ := Sp62Rec.I1.rho_eq_one_of_perm_eq_one N.subtype ρ hρN f' hoddK
  have hwodd : Equiv.Perm.sign w.perm = -1 :=
    Sp62Rec.I1.sign_perm_eq_neg_one N.subtype ρ hρN f' hfalt hkerρ τ' hτ'sign w
      (fun x => ⟨⟨τ' * (x : ↥B) * τ'⁻¹, hNn.conj_mem x x.2 τ'⟩, rfl⟩)
      (fun x y hxy => by
        have hxy' : ((y : ↥B) : Y) = (τ' : Y) * ((x : ↥B) : Y) * (τ' : Y)⁻¹ :=
          congrArg Subtype.val hxy
        have := hτf ((x : ↥B) : Y) (Subgroup.mem_subgroupOf.mp x.2)
        have e : eEN y = ⟨(τ' : Y) * ((x : ↥B) : Y) * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 _
            (Subgroup.mem_subgroupOf.mp x.2)⟩ := Subtype.ext hxy'
        show f (eEN y) = w * f (eEN x) * w⁻¹
        rw [e]; exact this)
  have hsq' : ∀ x ∈ aeSub 6, (w * w) * x = x * (w * w) := by
    intro x hx
    obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
    have h3 := hw (αP y)
    rw [hαsq, hw y, hy] at h3
    have h4 : x = w * (w * x * w⁻¹) * w⁻¹ := h3
    have h7 : (w * (w * x * w⁻¹) * w⁻¹) * (w * w) = (w * w) * x := by group
    rw [← h4] at h7
    exact h7.symm
  obtain ⟨hw2, hws⟩ := Sp62Rec.I1.eq_of_centralizes_twins hβ h1 h2 hwodd hsq'
  have hτE : (τ' : Y) ∉ E := fun h => hτ'N (Subgroup.mem_subgroupOf.mpr h)
  have hB' : ∀ g ∈ B, g ∈ E ∨ g * (τ' : Y)⁻¹ ∈ E := by
    intro g' hg'
    rcases hΓ ⟨g', hg'⟩ with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.mp h)
    · exact Or.inr (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨φ, hφs, hφk, hφE, hφe, hφf⟩ := Sp62Rec.I1.hat_of_data' Θ hΘ hEB hEn' heE f hfr hfk hfe
    τ'.2 hτ2 hτE hB' hw2 hws hwodd hτf hperfA
  have htE : t ∈ E := hmap ▸ ⟨⟨t, htC⟩, htY, rfl⟩
  have hhull : (TwinPerpV3.hullEquiv hmap).symm ⟨t, htE⟩ =
      (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    apply Subtype.ext
    apply Subtype.ext
    have := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm ⟨t, htE⟩)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have htq : ((q0 ⟨t, htE⟩ : ↥(pSpan Φ)) : SecQ R e) =
      QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    rw [hq0coe, secOf_apply, hhull]
  have htmem : q0 ⟨t, htE⟩ ∈ (TwinDisc.secImg (Om R) e J).subgroupOf (pSpan Φ) :=
    Subgroup.mem_subgroupOf.mpr (htq ▸ hU.mem)
  have htψ : (f ⟨t, htE⟩ : Wr 6) ∈ memAt β hβ b := by
    have h1 : (f ⟨t, htE⟩ : Wr 6) ∈
        (((TwinDisc.secImg (Om R) e J).subgroupOf (pSpan Φ)).map ψ.toMonoidHom).map
          (aeSub 6).subtype :=
      ⟨ψ (q0 ⟨t, htE⟩), ⟨q0 ⟨t, htE⟩, htmem, rfl⟩, rfl⟩
    rw [hψm _ hK β hβ b hlab] at h1
    exact h1
  have htsq : f ⟨t, htE⟩ * f ⟨t, htE⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htE⟩ : ↥E) * ⟨t, htE⟩ = 1 := Subtype.ext hzJ.sq
    rw [this, map_one]
  have htf : f ⟨t, htE⟩ = zOf (emb β hβ) := by
    rcases eq_of_mem_memAt_mul_self htψ htsq with h1 | h1
    · exfalso
      have h2 : q0 ⟨t, htE⟩ = 1 := by
        have h2' : ψ (q0 ⟨t, htE⟩) = 1 := Subtype.ext h1
        exact ψ.injective (h2'.trans (map_one ψ).symm)
      have h3 : ((q0 ⟨t, htE⟩ : ↥(pSpan Φ)) : SecQ R e) = 1 := by rw [h2]; rfl
      rw [htq] at h3
      exact hU.ne_one h3
    · exact h1
  obtain ⟨hm, hφt⟩ := hφf t htE
  have hmz : zOf (emb β hβ) ∈ Sp62Rec.I1.Wsub := htf ▸ hm
  have hxe : (⟨f ⟨t, htE⟩, hm⟩ : ↥Sp62Rec.I1.Wsub) = ⟨zOf (emb β hβ), hmz⟩ := Subtype.ext htf
  have hodd : Odd (Subgroup.centralizer ({φ ⟨t, hEB htE⟩} : Set ↥Hhat)).index := by
    rw [hφt, hxe]
    have hcent : Subgroup.centralizer ({Θ ⟨zOf (emb β hβ), hmz⟩} : Set ↥Hhat) =
        (Subgroup.centralizer ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} :
          Set ↥Sp62Rec.I1.Wsub)).map Θ.toMonoidHom := by
      ext y
      constructor
      · intro hy
        refine ⟨Θ.symm y, SetLike.mem_coe.mpr ?_, by simp⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        apply Θ.injective
        rw [map_mul, map_mul]
        simpa using hy
      · rintro ⟨y', hy', rfl⟩
        have hy'' := SetLike.mem_coe.mp hy'
        rw [Subgroup.mem_centralizer_singleton_iff] at hy'' ⊢
        show Θ y' * Θ ⟨zOf (emb β hβ), hmz⟩ = Θ ⟨zOf (emb β hβ), hmz⟩ * Θ y'
        rw [← map_mul, ← map_mul, hy'']
    have hidx : (Subgroup.map Θ.toMonoidHom (Subgroup.centralizer
        ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} : Set ↥Sp62Rec.I1.Wsub))).index =
        (Subgroup.centralizer ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} :
          Set ↥Sp62Rec.I1.Wsub)).index := Subgroup.index_map_equiv _ Θ
    rw [hcent, hidx]
    exact Sp62Rec.I1.odd_index_centralizer_zOf (emb β hβ) hmz
  have hlabE : ∀ (L : Subgroup Y) (hL : L ∈ tqMembers3 (Om R) e) (b' : Bool),
      ((TwinDisc.secImg (Om R) e L).subgroupOf (pSpan Φ)).map I.φ = memBar β hβ b' →
      ((TwinADescent.coreAt e L).subgroupOf E).map f = memAt β hβ b' := by
    intro L hL b' hlabL
    rw [← hψm _ (TwinDisc.secImg_mem_secFam hL) β hβ b' hlabL]
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ψ (q0 x), ⟨q0 x, ?_, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hq0coe, secOf_apply]
      refine ⟨(TwinPerpV3.hullEquiv hmap).symm x, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hxc := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm x)
      rw [MulEquiv.apply_symm_apply] at hxc
      rw [← hxc]
      exact Subgroup.mem_subgroupOf.mp hx
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
      obtain ⟨h, hh, hhp⟩ := hp
      refine ⟨TwinPerpV3.hullEquiv hmap h, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, TwinPerpV3.hullEquiv_coe]
        exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
      · have hq : q0 (TwinPerpV3.hullEquiv hmap h) = p := by
          apply Subtype.ext
          rw [hq0coe, secOf_apply, MulEquiv.symm_apply_apply]
          exact hhp
        show ((ψ (q0 (TwinPerpV3.hullEquiv hmap h)) : ↥(aeSub 6)) : Wr 6) = _
        rw [hq]
        rfl
  refine ⟨f, φ,
    { E_le_B := hEB, B_le := hBC, E_normal := hEn, e_mem := heE, z_mem := hEB htE,
      f_range := hfr, f_ker := hfk, Θ_pi := hΘ, φ_surj := hφs, φ_ker := hφk, φ_E := hφE,
      φ_e := hφe, φ_odd := hodd, φ_f := hφf, kappa := hκ }, β, hβ, b, ?_, ?_⟩
  · exact hlabE J hJ b hlab
  · exact hlabE J' hJ' (!b) hlab'

end Core

section Final


theorem i1_action_lab_final {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) {Z : Subgroup Y} (hAE : SecAE R e 6) (hI : I1In R t e Z)
    {J J' : Subgroup Y} (hJ : J ∈ tqMembers3 (Om R) e) (hJ' : J' ∈ tqMembers3 (Om R) e)
    (hne : J' ≠ J) (hzJ : IsUniqueInvolution J t) (hzJ' : IsUniqueInvolution J' t)
    (hcomm : ∀ x ∈ Z, ∀ l ∈ J ⊔ J',
      x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) :
    ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
      (φ : ↥(Z ⊔ rLayer (Om R) e) →* ↥Hhat),
      I1Action t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) f Θ φ ∧
      ∃ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool),
        ((TwinADescent.coreAt e J).subgroupOf (rLayer (Om R) e)).map f = memAt β hβ b ∧
        ((TwinADescent.coreAt e J').subgroupOf (rLayer (Om R) e)).map f = memAt β hβ (!b) := by
  obtain ⟨Θ, hΘ⟩ := Sp62Rec.I1.exists_iso_Wsub_Hhat
  obtain ⟨f, φ, D, hlab⟩ := i1_action_lab hP hAE hI hJ hJ' hne hzJ hzJ' hcomm Θ hΘ
  exact ⟨f, Θ, φ, D, hlab⟩

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z6M
