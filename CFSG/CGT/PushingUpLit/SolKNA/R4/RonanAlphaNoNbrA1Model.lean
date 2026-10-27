module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrA1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Final
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrVtx

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2)
open scoped commutatorElement Pointwise

section Cert



variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkDichSyl_of_linkZ2L2 (hr : 4 ≤ r) (hL : TightLargeHypR r n Y R S t)
    (hbad : LinkAlphaBad R t) (hZ2 : LinkZ2 R t)
    (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hmodel : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
      CFSG.Blueprint.LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) : LinkDichSyl R t := by
  classical
  obtain ⟨p, f, hp, hp2, -, -, hmod⟩ := hmodel
  have hΦ : TypeRFam r (linkFam R t) := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hO := oddCore_linkGrp_eq_bot hL
  have hgen : omegaGen (linkFam R t) = ⊤ := omegaGen_linkRestrict
  have htr := hZ2.1
  obtain ⟨J, hJ, -⟩ := hbad
  have hK := subgroupOf_mem_linkRestrict (t := t) hJ
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hK
  have htr' : ∀ L ∈ linkFam R t, ∃ g ∈ omegaGen (linkFam R t),
      conjSub g ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) = L :=
    fun L hL' => by
      obtain ⟨g, hg⟩ := htr _ hK L hL'
      exact ⟨g, by rw [hgen]; exact Subgroup.mem_top g, hg⟩
  obtain ⟨S', hd, hc', hfam⟩ := exists_datumR_of_omegaTransitive (by omega) hΦ hO hgen hK htr' hz'
  haveI := hsimp
  have hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel
      hmod).2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hZF : Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(genFittingFStar ↥(linkGrp R t))) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hCF : Subgroup.centralizer ((genFittingFStar ↥(linkGrp R t) : Subgroup ↥(linkGrp R t)) :
      Set ↥(linkGrp R t)) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  have eF : ↥(genFittingFStar ↥(linkGrp R t)) ≃* FStarQuot ↥(linkGrp R t) :=
    (QuotientGroup.quotientBot (G := ↥(genFittingFStar ↥(linkGrp R t)))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZF.symm)
  have hLM : CFSG.Blueprint.LieModel ↥(genFittingFStar ↥(linkGrp R t)) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv eF.symm hmod
  have hSCM := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLM
  have hSmall : SmallL2 ↥(genFittingFStar ↥(linkGrp R t)) := ⟨p, f, hp, hp2, hSCM.1.2.1, hSCM⟩
  have hnO : ¬ TightInO2 z' := by
    rintro ⟨P, hPn, hP2, hzP⟩
    have h0 := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg.normalTwo_eq_bot_of_fstar_simple hsimp hnab hPn hP2
    rw [h0, Subgroup.mem_bot] at hzP
    exact (hz'.ne_one) hzP
  have hE : TightEdgeless
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) := by
    unfold TightEdgeless
    rw [hfam]
    exact hZ2.2.2.1
  haveI hFN : (genFittingFStar ↥(linkGrp R t)).Normal := genFittingFStar_normal _
  have hM := model163R_holds r hr ↥(linkGrp R t) (genFittingFStar ↥(linkGrp R t))
    hsimp hnab hCF (Or.inl hSmall) _ S' z' hd hc' hnO hE
  have hcore : tightCore
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) =
      (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t) :=
    hΦ.closure_twoElts hK
  haveI : (⊤ : Subgroup ↥(linkGrp R t)).Normal := inferInstance
  have hdich : ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ s ∈ sylowSet S', β s = s) →
      (∀ y ∈ (⊤ : Subgroup ↥(linkGrp R t)), β y = y) ∨
        (∀ y ∈ (⊤ : Subgroup ↥(linkGrp R t)), β y = z' * y * z'⁻¹) := by
    intro β hβ2 hβS
    have hinv : ∀ x, β (β x) = x := fun x => by
      have h := congrArg (fun γ : MulAut ↥(linkGrp R t) => γ x) hβ2
      simpa [MulAut.mul_apply, MulAut.one_apply] using h
    rcases hM β hinv hβS with h | h
    · exact Or.inl fun y _ => h y
    · exact Or.inr fun y _ => h y
  intro M hM' a ha P hP β hβ2 hβP
  rcases exitLU_dich_all hd hcore hdich hfam M hM' a ha P hP β hβ2 hβP with h | h
  · left
    exact MulEquiv.ext fun x => h x (Subgroup.mem_top x)
  · right
    exact MulEquiv.ext fun x => h x (Subgroup.mem_top x)

theorem false_of_caseA1_of_linkZ2L2 (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hbad : LinkAlphaBad R t) (hZ2 : LinkZ2 R t)
    (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hmodel : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
      CFSG.Blueprint.LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {R₀ : Subgroup Y} (hR₀ : IsSylow2In R₀ (tightCore R))
    (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) {w : Y}
    (hw2 : w * w = 1) (hwt : w * t = t * w) (hwu : w * u = u * w)
    (hwE : w ∉ Subgroup.closure ({t, u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) : False :=
  false_of_caseA1_r hr hNo h4 hL hc hbad hZ2.1 (linkDichSyl_of_linkZ2L2 hr hL hbad hZ2 hsimp hmodel)
    hJ hu hR₀ hR₀u hT₀ hT₀N hw2 hwt hwu hwE hR₀w hT₀w

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
