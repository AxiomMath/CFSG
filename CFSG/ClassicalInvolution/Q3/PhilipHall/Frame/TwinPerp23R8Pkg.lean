module

public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Sp62Rec.PkgNoHat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge
import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE



variable {Y : Type} [Group Y] [Finite Y]

structure I1In {G : Type} [Group G] [Finite G] (R : Subgroup G) (t e : G) (Z : Subgroup G) :
    Prop where
  Z_le : Z ≤ Subgroup.centralizer ({t} : Set G)
  e_mem : e ∈ Z
  e_ne_one : e ≠ 1
  Z_elem : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x ∧ x * x = 1
  S6 : ∃ ρ : ↥(Z ⊔ rLayer (Om R) e) →* Equiv.Perm (Fin 6), Function.Surjective ρ ∧
    ρ.ker ≤ (rLayer (Om R) e).subgroupOf (Z ⊔ rLayer (Om R) e)
  twin : ∃ J J' : Subgroup G, J ∈ tqMembers3 (Om R) e ∧ J' ∈ tqMembers3 (Om R) e ∧ J' ≠ J ∧
    IsUniqueInvolution J t ∧ IsUniqueInvolution J' t ∧
    ∀ x ∈ Z, ∀ l ∈ J ⊔ J', x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G))

@[expose] def P23E8ZPkg (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∃ (Z : Subgroup Y) (T : Sylow 2 Y) (A X : Subgroup Y),
          I1In R t e Z ∧ E8ZPkgNoHat t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) T A X

structure SecData (R : Subgroup Y) (e : Y) : Prop where
  sq : e * e = 1
  hΩ : HypOmegaGen (Om R)
  two : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)
  q8 : Q8Section (SecQ R e) (secFam (Om R) e)

theorem SecData.of_perp {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (h : PerpHypS n Y R S t) {e : Y} (he : e * e = 1) : SecData R e :=
  ⟨he, (CoreData.of_S h.core).hyp,
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) (CoreData.of_S h.core).datum.twoGroup),
    TwinPerpV3.layer_q8Section h he⟩

theorem rLayer_map_conj_eq (R : Subgroup Y) (e : Y) :
    ∀ g ∈ Subgroup.centralizer ({e} : Set Y),
      (rLayer (Om R) e).map (MulAut.conj g).toMonoidHom = rLayer (Om R) e :=
  fun _ hg => T8.rLayer_conjSub_eq (conjInvariant_conjClass (tightCore R)) hg

theorem mem_rLayer_self {R : Subgroup Y} {t e : Y} {Z : Subgroup Y} (hI : I1In R t e Z) :
    e ∈ rLayer (Om R) e := by
  obtain ⟨ρ, hρ, hker⟩ := hI.S6
  have hZC : Z ≤ Subgroup.centralizer ({e} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hI.Z_elem x hx e hI.e_mem).1
  have hEC : rLayer (Om R) e ≤ Subgroup.centralizer ({e} : Set Y) :=
    TwinPerpV3.rLayer_le_centralizer _ _
  have hBC : Z ⊔ rLayer (Om R) e ≤ Subgroup.centralizer ({e} : Set Y) := sup_le hZC hEC
  have heB : e ∈ Z ⊔ rLayer (Om R) e := Subgroup.mem_sup_left hI.e_mem
  have := Sp62Rec.I1.mem_of_central_of_perm_quotient
    ((rLayer (Om R) e).subgroupOf (Z ⊔ rLayer (Om R) e)) ρ hρ hker (c := ⟨e, heB⟩)
    (fun g => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hBC g.2)))
  exact Subgroup.mem_subgroupOf.mp this

section Bridge

variable {Ω : Set (Subgroup Y)} {c : Y}

noncomputable def secOf
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c) :
    ↥(rLayer Ω c) →* ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c) :=
  (QuotientGroup.mk' _).comp (TwinPerpV3.hullEquiv hmap).symm.toMonoidHom

theorem secOf_apply
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (y : ↥(rLayer Ω c)) :
    secOf hmap y = (QuotientGroup.mk ((TwinPerpV3.hullEquiv hmap).symm y) :
      ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
  unfold secOf
  rfl

theorem secOf_surjective
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c) :
    Function.Surjective (secOf hmap) :=
  (QuotientGroup.mk'_surjective _).comp (TwinPerpV3.hullEquiv hmap).symm.surjective

theorem secOf_ker
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c) :
    (secOf hmap).ker = (oddCoreIn (rLayer Ω c)).subgroupOf (rLayer Ω c) := by
  ext x
  have hiso : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      (TwinPerpV3.hullEquiv hmap).toMonoidHom = classicalInvolutionOddCore ↥(rLayer Ω c) :=
    TwinPerpV3.classicalInvolutionOddCore_map_equiv (TwinPerpV3.hullEquiv hmap)
  have h1 : x ∈ (secOf hmap).ker ↔ (TwinPerpV3.hullEquiv hmap).symm x ∈
      classicalInvolutionOddCore ↥(coreHull Ω c) :=
    QuotientGroup.eq_one_iff _
  rw [h1, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have : x ∈ classicalInvolutionOddCore ↥(rLayer Ω c) := by
      rw [← hiso]
      exact ⟨_, h, by simp⟩
    exact ⟨x, this, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    have hy' : y ∈ classicalInvolutionOddCore ↥(rLayer Ω c) := hy
    rw [← hiso] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have : z = (TwinPerpV3.hullEquiv hmap).symm y := by
      rw [← hzy]; simp
    rwa [← this]

theorem secOf_conj (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (g : ↥(Subgroup.centralizer ({c} : Set Y))) (x : ↥(rLayer Ω c))
    (hx : (g : Y) * (x : Y) * (g : Y)⁻¹ ∈ rLayer Ω c) :
    secOf hmap ⟨(g : Y) * (x : Y) * (g : Y)⁻¹, hx⟩ =
      TwinExitPf6.secAut Ω c hΩ hc2 g (secOf hmap x) := by
  have hcoe : ∀ z : ↥(rLayer Ω c),
      ((((TwinPerpV3.hullEquiv hmap).symm z : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set Y))) : Y) = (z : Y) := fun z => by
    have := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm z)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  symm
  refine TwinExitPf6.secAut_mk hΩ hc2 g _ _ (Subtype.ext ?_)
  show ((((TwinPerpV3.hullEquiv hmap).symm ⟨(g : Y) * (x : Y) * (g : Y)⁻¹, hx⟩ :
      ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) =
    (g : Y) * ((((TwinPerpV3.hullEquiv hmap).symm x : ↥(coreHull Ω c)) :
      ↥(Subgroup.centralizer ({c} : Set Y))) : Y) * (g : Y)⁻¹
  rw [hcoe, hcoe]

end Bridge

theorem aeCoverHyp_of_I1 {R : Subgroup Y} {t e : Y} (SD : SecData R e)
    (I : AEIdent (TwinDisc.secFam (Om R) e) 6) {J J' : Subgroup Y} (hJ : J ∈ tqMembers3 (Om R) e)
    (hJ' : J' ∈ tqMembers3 (Om R) e) (hne : J' ≠ J) (hzJ : IsUniqueInvolution J t)
    (hzJ' : IsUniqueInvolution J' t) : TL4.AECoverHyp I := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one SD.sq
  obtain ⟨_, _, hU⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ hzJ
  obtain ⟨_, _, hU'⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ' hzJ'
  exact TwinPerpV3.A6b.aeCoverHyp_of_twins (by norm_num) (by norm_num) SD.q8 I
    (TwinDisc.secImg_mem_secFam hJ) (TwinDisc.secImg_mem_secFam hJ')
    (TwinPerpV3.secImg_ne_of_twin SD.hΩ hc2 hJ hJ' hne.symm hzJ hzJ').symm hU hU'

theorem secOf_central {Ω : Set (Subgroup Y)} {c : Y}
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hc : c ∈ rLayer Ω c) (y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    secOf hmap ⟨c, hc⟩ * y = y * secOf hmap ⟨c, hc⟩ := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
  show (QuotientGroup.mk' _ ((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩)) * QuotientGroup.mk' _ h =
    QuotientGroup.mk' _ h * (QuotientGroup.mk' _ ((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  have hcoe : ((((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩ : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set Y))) : Y) = c := by
    have := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  show ((((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩ : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set Y))) : Y) * (((h : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set Y))) : Y) =
    (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) *
      ((((TwinPerpV3.hullEquiv hmap).symm ⟨c, hc⟩ : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set Y))) : Y)
  rw [hcoe]
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set Y))).2)).symm

theorem secOf_ne_one {Ω : Set (Subgroup Y)} {c : Y}
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hc : c ∈ rLayer Ω c) (hc2 : c * c = 1) (hc1 : c ≠ 1) : secOf hmap ⟨c, hc⟩ ≠ 1 := by
  intro h
  have hk : (⟨c, hc⟩ : ↥(rLayer Ω c)) ∈ (secOf hmap).ker := h
  rw [secOf_ker, Subgroup.mem_subgroupOf] at hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have h3 : 2 ∣ Nat.card (oddCoreIn (rLayer Ω c)) := h2 ▸ Subgroup.orderOf_dvd_natCard _ hk
  exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn _)) (even_iff_two_dvd.mpr h3)

theorem ker_ne_bot_of_central {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hS : Q8Section X Φ) (I : AEIdent Φ 6) {c : X} (hc : ∀ y : X, c * y = y * c) (hc1 : c ≠ 1) :
    I.φ.ker ≠ ⊥ := by
  have hgen : pSpan Φ = ⊤ := TwinDisc.AE5.hgen_of hS
  have hcP : c ∈ pSpan Φ := hgen ▸ Subgroup.mem_top c
  have hcen : (⟨c, hcP⟩ : ↥(pSpan Φ)) ∈ Subgroup.center ↥(pSpan Φ) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g).symm
  have hk := AEIdent.center_le_ker (by norm_num : 5 ≤ 6) I hcen
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hk
  exact hc1 (congrArg Subtype.val hk)

theorem secAut_odd_of_twin {R : Subgroup Y} {t e : Y} (SD : SecData R e)
    (g : ↥(Subgroup.centralizer ({e} : Set Y))) {J : Subgroup Y} (hJ : J ∈ tqMembers3 (Om R) e)
    (hcomm : ∀ l ∈ J, (g : Y) * l * (g : Y)⁻¹ * l⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({t} : Set Y))) :
    ∀ y ∈ TwinDisc.secImg (Om R) e J,
      Odd (orderOf (TwinExitPf6.secAut (Om R) e SD.hΩ
        (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one SD.sq) g y *
          y⁻¹)) := by
  intro y hy
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one SD.sq
  haveI hHn := TwinExitPf6.normal_coreHull SD.hΩ hc2
  obtain ⟨h, hh, rfl⟩ := hy
  have hh' : (((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ J :=
    TwinADescent.coreAt_le_left e J (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh))
  let h' : ↥(coreHull (Om R) e) :=
    ⟨g * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) * g⁻¹,
      hHn.conj_mem _ h.2 g⟩
  have e1 : TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h' :=
    TwinExitPf6.secAut_mk SD.hΩ hc2 g h h' rfl
  show Odd (orderOf (TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h) *
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h)⁻¹))
  rw [e1, ← map_inv, ← map_mul]
  refine Odd.of_dvd_nat ?_ (orderOf_map_dvd _ _)
  have hmem : (g : Y) * (((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
      (g : Y)⁻¹ * ((((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y))⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := hcomm _ hh'
  have hcoe : (((h' * h⁻¹ : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
      (g : Y) * (((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
      (g : Y)⁻¹ *
        ((((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y))⁻¹ := rfl
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hcoe]
  exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hmem)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
