module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovHSLoc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverMain
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.HS
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovGen
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

public section

namespace CFSG.ComponentClassification.GSThmB.CovHS

open Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial

theorem ordA_one_ne_44352000 (m : ℕ) : Open.ordA 1 m ≠ 44352000 :=
  Cov.ordA_one_ne_of_lt (B := 446) (by norm_num) (by decide +kernel) m

theorem smallQ_of_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : Cov.SmallQ Y) :
    Cov.SmallQ Y' := by
  rcases h with ⟨p, f, hp, hp2, hf, hq, hm⟩ | ⟨⟨e7⟩⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, hq, OddQuot.lieModel_of_equiv e hm⟩
  · exact Or.inr ⟨e.symm.trans e7⟩

@[expose] noncomputable def quotCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)

theorem t2_facts :
    hsT2 ∈ hsP ∧ orderOf hsT2 = 2 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, ho, hout, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at ho hout
  simp only [Bool.false_eq_true, false_iff, not_not] at hout
  exact ⟨hout, ho⟩

theorem t2_mem :
    hsT2 ∈ hsP := t2_facts.1

theorem t2_mul_self :
    hsT2 * hsT2 = 1 := by
  have h1 : hsT2 ^ orderOf hsT2 = 1 := pow_orderOf_eq_one _
  rw [t2_facts.2, sq] at h1
  exact h1

theorem yPerm_mem_P :
    yPerm ∈ hsP :=
  (mem_inf.mp yPerm_mem).1

theorem t2_mul_y :
    hsT2 * yPerm = yPerm * hsT2 := by
  have h := (mem_inf.mp yPerm_mem).2
  rw [mem_centralizer_singleton_iff] at h
  exact h.symm

theorem conj_t2_of_sq
    {w : Equiv.Perm (Fin 3850)} (hw : w ∈ hsP) (hw2 : w * w = 1) (hf : nfix w = 30) :
    ∃ g ∈ hsP, w = g * hsT2 * g⁻¹ := by
  refine conj_t2_of_nfix hw (orderOf_eq_prime (by rw [sq]; exact hw2) fun h1 => ?_) hf
  rw [h1] at hf
  have : nfix 1 = 3850 := by
    simp only [nfix, Equiv.Perm.one_apply]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_true, Fintype.card_fin]
  rw [this] at hf
  exact absurd hf (by norm_num)

theorem sq_lift
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (ρ : L →* hsP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = zpowers t) {W : L} {g : Equiv.Perm (Fin 3850)}
    (hg : g ∈ hsP) (hW : ((ρ W : hsP) : Equiv.Perm (Fin 3850)) = g * hsT2 * g⁻¹) :
    W * W = t := by
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hPP : CFSG.QuasithinUnique.Id2519.UHS.PP = hsP := hsP_eq_original.symm
  have hWW : W * W ∈ zpowers t := by
    rw [← hker, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hW, Subgroup.coe_one]
    calc g * hsT2 * g⁻¹ * (g * hsT2 * g⁻¹) = g * (hsT2 * hsT2) * g⁻¹ := by group
      _ = 1 := by rw [t2_mul_self]; group
  rcases Cov.eq_one_or_eq_of_mem_zpowers ht2 hWW with h | h
  · exfalso
    have hker' : ∀ e, ((ρ e : hsP) : Equiv.Perm (Fin 3850)) = 1 → e = 1 ∨ e = t := by
      intro e he
      have h2 : e ∈ zpowers t := by
        rw [← hker, MonoidHom.mem_ker]
        exact Subtype.ext he
      exact Cov.eq_one_or_eq_of_mem_zpowers ht2 h2
    have hιt : ((ρ t : hsP) : Equiv.Perm (Fin 3850)) = 1 := by
      have : t ∈ ρ.ker := hker ▸ mem_zpowers t
      rw [MonoidHom.mem_ker.mp this, Subgroup.coe_one]
    let X : CFSG.QuasithinUnique.Ch1.M22Cover.CentralExt L (Equiv.Perm (Fin 3850)) :=
      { φ := hsP.subtype.comp ρ, ζ := t, φ_ζ := hιt, ne_one := ht1, sq := ht2,
        central := fun e => (mem_center_iff.mp htc e).symm, ker := hker' }
    have hφ : ∀ e, X.φ e = ((ρ e : hsP) : Equiv.Perm (Fin 3850)) := fun e => rfl
    have hrange : ∀ y ∈ CFSG.QuasithinUnique.Id2519.UHS.PP, ∃ e, X.φ e = y := by
      intro y hy
      rw [hPP] at hy
      obtain ⟨e, he⟩ := hρ ⟨y, hy⟩
      exact ⟨e, by rw [hφ, he]⟩
    have hφmem : ∀ e, X.φ e ∈ CFSG.QuasithinUnique.Id2519.UHS.PP := fun e => by
      rw [hPP, hφ]
      exact (ρ e).2
    obtain ⟨-, hDcard, hDC2, -, -⟩ := hs_D_facts
    have hDPP : genGroup 3850 hsDGens hsDPerm ≤ CFSG.QuasithinUnique.Id2519.UHS.PP := by
      rw [hPP]
      exact hDC2.trans inf_le_left
    have hK : Nat.card ((genGroup 3850 hsDGens hsDPerm).subgroupOf
        CFSG.QuasithinUnique.Id2519.UHS.PP) = 360 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hDPP).toEquiv, hDcard]
    have hT2PP : hsT2 ∈ CFSG.QuasithinUnique.Id2519.UHS.PP := hPP ▸ t2_mem
    have hT2ne : hsT2 ≠ 1 := fun h1 => by
      have h0 := t2_facts.2
      rw [h1, orderOf_one] at h0
      exact absurd h0 (by norm_num)
    obtain ⟨d, hd, hdc⟩ := CFSG.QuasithinUnique.Ch1.HSCover.exists_conj_hsC ⟨hsT2, hT2PP⟩
      (Subtype.ext t2_mul_self) (fun h1 => hT2ne (congrArg Subtype.val h1))
      ((genGroup 3850 hsDGens hsDPerm).subgroupOf CFSG.QuasithinUnique.Id2519.UHS.PP) hK
      (fun k hk => by
        apply Subtype.ext
        have hkD : (k : Equiv.Perm (Fin 3850)) ∈ genGroup 3850 hsDGens hsDPerm :=
          mem_subgroupOf.mp hk
        have h2 := (mem_inf.mp (hDC2 hkD)).2
        rw [mem_centralizer_singleton_iff] at h2
        exact h2)
    have hcc : CFSG.QuasithinUnique.Id2519.UHS.hsC = CFSG.QuasithinUnique.Ch1.HSCover.cElt := by
      rw [CFSG.QuasithinUnique.Ch1.HSCover.cElt_eq]
      rfl
    have hdc' : CFSG.QuasithinUnique.Ch1.HSCover.cElt = d⁻¹ * hsT2 * d := by
      rw [← hcc]
      have h1 : hsT2 = d * CFSG.QuasithinUnique.Id2519.UHS.hsC * d⁻¹ := hdc
      rw [h1]
      group
    obtain ⟨G, hG⟩ := hrange (g * d) (CFSG.QuasithinUnique.Id2519.UHS.PP.mul_mem (hPP ▸ hg) hd)
    refine CFSG.QuasithinUnique.Ch1.HSCover.hs_no_involution_over_c X hrange hφmem
      (G⁻¹ * W * G) ?_ ?_
    · calc G⁻¹ * W * G * (G⁻¹ * W * G) = G⁻¹ * (W * W) * G := by group
        _ = 1 := by rw [h]; group
    · rw [map_mul, map_mul, map_inv, hG, hφ W, hW, hdc']
      group
  · exact h

theorem disp_t2_y
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (ρ : L →* hsP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = zpowers t) (U V : L)
    (hU : ρ U = ⟨hsT2, t2_mem⟩) (hV : ρ V = ⟨yPerm, yPerm_mem_P⟩) :
    U⁻¹ * V⁻¹ * U * V = t := by
  have htc : ∀ y : L, t * y = y * t := fun y =>
    (mem_center_iff.mp (hZ ▸ mem_zpowers t : t ∈ center L) y).symm
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨-, -, hyy, -, hfy, hfty⟩ := klein_parts
  have hU2 : U * U = t := sq_lift hLq ht hZ ρ hρ hker (g := 1) (one_mem _) (by
    rw [hU]
    group)
  obtain ⟨gy, hgy, hygy⟩ := conj_t2_of_sq yPerm_mem_P hyy hfy
  have hV2 : V * V = t := sq_lift hLq ht hZ ρ hρ hker hgy (by rw [hV]; exact hygy)
  have hty : (hsT2 * yPerm) * (hsT2 * yPerm) = 1 := by
    calc (hsT2 * yPerm) * (hsT2 * yPerm) = hsT2 * (yPerm * hsT2) * yPerm := by group
      _ = (hsT2 * hsT2) * (yPerm * yPerm) := by rw [← t2_mul_y]; group
      _ = 1 := by rw [t2_mul_self, hyy, one_mul]
  obtain ⟨gu, hgu, hugu⟩ := conj_t2_of_sq (hsP.mul_mem t2_mem yPerm_mem_P) hty hfty
  have hUV2 : (U * V) * (U * V) = t := sq_lift hLq ht hZ ρ hρ hker hgu (by
    rw [map_mul, Subgroup.coe_mul, hU, hV]
    exact hugu)
  have hUi : U⁻¹ = U * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hU2, ht2])
  have hVi : V⁻¹ = V * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hV2, ht2])
  calc U⁻¹ * V⁻¹ * U * V = U * (t * V) * t * U * V := by rw [hUi, hVi]; group
    _ = U * (V * t) * t * U * V := by rw [htc V]
    _ = (U * V) * (t * t) * U * V := by group
    _ = (U * V) * (U * V) := by rw [ht2]; group
    _ = t := hUV2

theorem twist
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (ρ : L →* hsP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut hsP) (hβ : ∀ x, ρ (α x) = β (ρ x))
    {M : Subgroup hsP} (hM : CFSG.Assembly.IsComponentOf M (fixSub β))
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : ∃ h : L, α h = h * t := by
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hperf : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have hι : Function.Injective hsP.subtype := Subtype.val_injective
  have hrange : hsP.subtype.range = hsP := range_subtype hsP
  obtain ⟨eAut, heAut, -⟩ := hs_full_automorphism_model
  obtain ⟨x, hx⟩ := eAut.surjective β
  have hxι : ∀ z : hsP, ((β z : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * z * (x : Equiv.Perm (Fin 3850))⁻¹ := fun z => by
    rw [← hx, heAut x z, Subgroup.coe_inv]
  have hfix : (fixSub β).map hsP.subtype =
      hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850))) := by
    ext w
    simp only [mem_map, mem_inf, mem_fixSub, coe_subtype, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have h1 := hxι z
      rw [hz] at h1
      calc (z : Equiv.Perm (Fin 3850)) * x = (x * z * (x : Equiv.Perm (Fin 3850))⁻¹) * x := by
            rw [← h1]
        _ = x * z := by group
    · rintro ⟨hw, hwc⟩
      refine ⟨⟨w, hw⟩, Subtype.ext ?_, rfl⟩
      rw [hxι]
      calc (x : Equiv.Perm (Fin 3850)) * w * (x : Equiv.Perm (Fin 3850))⁻¹ =
          (w * x) * (x : Equiv.Perm (Fin 3850))⁻¹ := by rw [hwc]
        _ = w := by group
  have hM' : CFSG.Assembly.IsComponentOf (M.map hsP.subtype)
      (hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850)))) := by
    rw [← hfix]
    exact (isComponentOf_map_iff hι).2 hM
  have hMt' : Cov.SmallQ (↥(M.map hsP.subtype) ⧸ center ↥(M.map hsP.subtype)) :=
    smallQ_of_equiv (quotCenterEquiv (M.equivMapOfInjective _ hι)) hMt
  have hββ : β * β = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨y, rfl⟩ := hρ z
    rw [MulAut.mul_apply, ← hβ, ← hβ, ← MulAut.mul_apply, hα, MulAut.one_apply,
      MulAut.one_apply]
  have hxx : x * x = 1 := eAut.injective (by rw [map_mul, hx, hββ, map_one])
  by_cases hx1 : x = 1
  · exfalso
    have hβ1 : ∀ z, β z = z := fun z => Subtype.ext (by
      rw [hxι, hx1, Subgroup.coe_one, one_mul, inv_one, mul_one])
    have hfix1 : fixSub β = ⊤ := eq_top_iff.mpr fun z _ => mem_fixSub.mpr (hβ1 z)
    rw [hfix1] at hM
    exact Cov.false_of_top' hLq ρ hρ (hker.trans hZ.symm) hM hMt
      (fun q => by rw [card_hsP]; exact ordA_one_ne_44352000 q) (by rw [card_hsP]; norm_num)
  have hxo : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin 3850)) x.2 hxo
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hfx : (MulAut.conj g⁻¹).toMonoidHom (x : Equiv.Perm (Fin 3850)) = tp 3850 r.rep := by
    rw [hxg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB : CFSG.Assembly.IsComponentOf ((M.map hsP.subtype).map (MulAut.conj g⁻¹).toMonoidHom)
      (hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) := by
    have h := (isComponentOf_map_iff hfinj).2 hM'
    rwa [map_conj_inf_centralizer hsP (hsP.inv_mem hg), Set.image_singleton, hfx] at h
  have hBt := smallQ_of_equiv
    (quotCenterEquiv ((M.map hsP.subtype).equivMapOfInjective _ hfinj)) hMt'
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · dsimp only at hB
    exact (hsC1_no_component hB).elim
  · dsimp only at hxg
    have hxP : (x : Equiv.Perm (Fin 3850)) ∈ hsP := by
      rw [hxg]
      exact hsP.mul_mem (hsP.mul_mem hg t2_mem) (hsP.inv_mem hg)
    have hβc : ∀ z, β z = ⟨x, hxP⟩ * z * (⟨x, hxP⟩ : hsP)⁻¹ := fun z =>
      Subtype.ext (by rw [hxι, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])
    obtain ⟨X, hX⟩ := hρ ⟨x, hxP⟩
    have hαX : α = MulAut.conj X :=
      Cov.eq_conj_of_comp hperf ρ (by rw [hker, hZ]) α X fun y => by rw [hβ, hβc, hX]
    have hX2 := Cov.mul_self_mem_center_of_inner α hα X fun y => by
      rw [hαX, MulAut.conj_apply]
    obtain ⟨h, hh⟩ := Cov.twist_of_disp ρ hρ htc ht2 X hX2 (u := ⟨hsT2, t2_mem⟩)
      (v := ⟨yPerm, yPerm_mem_P⟩) (g := ⟨g, hg⟩) (Subtype.ext (by
        rw [hX, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hxg.symm)) (fun U V hU hV => disp_t2_y hLq ht hZ ρ hρ hker U V hU hV)
    exact ⟨h, by rw [hαX, MulAut.conj_apply]; exact hh⟩
  · dsimp only at hB
    have hC : CFSG.QuasithinUnique.Id2519.HSAut.outerC =
        hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) := rfl
    rw [← hC] at hB
    exact (outerC_no_small hB hBt).elim
  · dsimp only at hB
    exact (c4_no_component hB).elim

end CFSG.ComponentClassification.GSThmB.CovHS
