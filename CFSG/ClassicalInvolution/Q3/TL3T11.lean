module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Conj

variable {G : Type} [Group G]

theorem pSpan_image_conjSub (g : G) (P : Set (Subgroup G)) :
    pSpan (conjSub g '' P) = (pSpan P).map (MulAut.conj g : G →* G) := by
  apply le_antisymm
  · refine pSpan_le ?_
    rintro _ ⟨L, hL, rfl⟩
    exact Subgroup.map_mono (le_pSpan hL)
  · rw [Subgroup.map_le_iff_le_comap]
    refine pSpan_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_pSpan (P := conjSub g '' P) ⟨L, hL, rfl⟩

@[expose] noncomputable def pSpanConj (g : G) (P : Set (Subgroup G)) :
    ↥(pSpan P) ≃* ↥(pSpan (conjSub g '' P)) :=
  ((MulAut.conj g).subgroupMap (pSpan P)).trans
    (MulEquiv.subgroupCongr (pSpan_image_conjSub g P).symm)

theorem pSpanConj_apply (g : G) (P : Set (Subgroup G)) (x : ↥(pSpan P)) :
    ((pSpanConj g P x : ↥(pSpan (conjSub g '' P))) : G) = g * x * g⁻¹ := by
  simp only [pSpanConj, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

theorem pSpanConj_symm_apply (g : G) (P : Set (Subgroup G)) (y : ↥(pSpan (conjSub g '' P))) :
    (((pSpanConj g P).symm y : ↥(pSpan P)) : G) = g⁻¹ * y * g := by
  have h : (y : G) = g * (((pSpanConj g P).symm y : ↥(pSpan P)) : G) * g⁻¹ := by
    rw [← pSpanConj_apply, MulEquiv.apply_symm_apply]
  rw [h]
  group

noncomputable def AEIdent.ofEq {P P' : Set (Subgroup G)} (h : P = P') {n : ℕ}
    (I : AEIdent P n) : AEIdent P' n :=
  h ▸ I

noncomputable def AEIdent.conjHom {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G) :
    ↥(pSpan (conjSub g '' P)) →* AE.AEQ n :=
  I.φ.comp (pSpanConj g P).symm.toMonoidHom

theorem AEIdent.conjHom_apply {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (y : ↥(pSpan (conjSub g '' P))) : I.conjHom g y = I.φ ((pSpanConj g P).symm y) := by
  rw [AEIdent.conjHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem AEIdent.conjHom_apply_conj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (x : ↥(pSpan P)) : I.conjHom g (pSpanConj g P x) = I.φ x := by
  rw [AEIdent.conjHom_apply, MulEquiv.symm_apply_apply]

theorem AEIdent.map_conj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    {L : Subgroup G} :
    ((conjSub g L).subgroupOf (pSpan (conjSub g '' P))).map (I.conjHom g) =
      (L.subgroupOf (pSpan P)).map I.φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(pSpanConj g P).symm y, ?_, (I.conjHom_apply g y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_symm_apply]
    exact mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨pSpanConj g P w, ?_, I.conjHom_apply_conj g w⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_apply]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hw)

noncomputable def AEIdent.conj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G) :
    AEIdent (conjSub g '' P) n where
  φ := I.conjHom g
  range_eq := by
    rw [← I.range_eq]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(pSpanConj g P).symm y, (I.conjHom_apply g y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨pSpanConj g P y, I.conjHom_apply_conj g y⟩
  ker_le := by
    intro x hx
    have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, ← I.conjHom_apply]
      exact hx
    have hc := Subgroup.mem_center_iff.mp (I.ker_le hx')
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (pSpanConj g P) (hc ((pSpanConj g P).symm y))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  label := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, (I.map_conj g).trans hlab⟩
  label_surj := by
    intro α h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α h b
    exact ⟨conjSub g L, ⟨L, hL, rfl⟩, (I.map_conj g).trans hlab⟩

end Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  (hS : ThinStd Ω K)
include hS

theorem ThinStd.maxAdjSet_conj (A : Subgroup G) (g : G) :
    {L : Subgroup G | MaxAdj (nbrAdj Ω) (conjSub g A) L} =
      conjSub g '' {L : Subgroup G | MaxAdj (nbrAdj Ω) A L} := by
  ext L
  constructor
  · intro h
    refine ⟨conjSub g⁻¹ L, ?_, conjSub_conjSub_inv g L⟩
    have h1 := maxAdj_conj hS.graphFam (show MaxAdj (nbrAdj Ω) (conjSub g A) L from h) g⁻¹
    rwa [conjSub_inv_conjSub] at h1
  · rintro ⟨L₀, hL₀, rfl⟩
    exact maxAdj_conj hS.graphFam (show MaxAdj (nbrAdj Ω) A L₀ from hL₀) g

theorem ThinStd.oddCore_pSpan_conj {A : Subgroup G}
    (h : classicalInvolutionOddCore ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) A L}) = ⊥)
    (g : G) :
    classicalInvolutionOddCore
      ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) (conjSub g A) L}) = ⊥ := by
  rw [hS.maxAdjSet_conj A g]
  exact classicalInvolutionOddCore_eq_bot_of_mulEquiv (pSpanConj g _) h

noncomputable def ThinStd.aeIdent_conj {A : Subgroup G} {n : ℕ}
    (I : AEIdent {L : Subgroup G | MaxAdj (nbrAdj Ω) A L} n) (g : G) :
    AEIdent {L : Subgroup G | MaxAdj (nbrAdj Ω) (conjSub g A) L} n :=
  AEIdent.ofEq (hS.maxAdjSet_conj A g).symm (I.conj g)

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


@[expose] def TightCaseBNonAE (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      ∀ M N N' : Subgroup Y,
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N' → N ≠ N' →
        ∀ u u' : Y, IsUniqueInvolution N u → IsUniqueInvolution N' u' →
        TC.Thin.CentX (CoreAssembly.conjClass (tightCore R)) M (u * u') →
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) N N' →
        (¬ ∃ m : ℕ, 5 ≤ m ∧ m ≠ 8 ∧ Nonempty (TC.Thin.AEIdent
          {L : Subgroup Y | MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M L} m)) →
          False

variable {n : ℕ}

theorem tightCaseBLeaf_of_nonAE (h : TightCaseBNonAE n) : TightCaseBLeaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall M N N' hN hN' hne u u' hu hu' hc hNN'
  by_cases hAE : ∃ m : ℕ, 5 ≤ m ∧ m ≠ 8 ∧ Nonempty (TC.Thin.AEIdent
      {L : Subgroup Y | MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M L} m)
  · exfalso
    obtain ⟨m, hm, hm8, ⟨IM⟩⟩ := hAE
    have hS := hL.thinStd hO hconn hsep
    have huniq := hL.datum.isUniqueInvolution_core
    have hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := ⟨x, hx, rfl⟩
      unfold TightOddCent at hO
      rw [hO, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    have hOK := hS.oddCore_pSpan_eq_bot huniq hOC
    obtain ⟨a, rfl⟩ := hS.trans M hN.1.1
    obtain ⟨b, rfl⟩ := hS.trans N hN.1.2.1
    have hOM := hS.oddCore_pSpan_conj hOK a
    have hON := hS.oddCore_pSpan_conj hOK b
    have hab : conjSub (b * a⁻¹) (conjSub a (tightCore R)) = conjSub b (tightCore R) := by
      rw [← conjSub_mul, inv_mul_cancel_right]
    have IN := TC.Thin.AEIdent.ofEq (by rw [hab]) (hS.aeIdent_conj IM (b * a⁻¹))
    exact hS.false_of_triangle_of_aeIdent hall hm hm8 hm hm8 IM IN hOM hON hN hN' hne hu hu' hc
      hNN'
  · exact h Y R S t hL hO hconn hsep hall M N N' hN hN' hne u u' hu hu' hc hNN' hAE

end Cit3

end CFSG.ClassicalInvolution.Q3
