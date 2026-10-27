module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OCompLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGOddLayerInndiagGlue
public import CFSG.HardMathSupport.Timmesfeld.Proving.ComponentCentralizer
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.RankThree.PartOne.K159H.O3Norm
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.StandardType.TwE6RootKill CFSG.HardMathSupport.Timmesfeld.CrossChar

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


private theorem isComponentOf_centralizer_inf_of_le_normalizer {G : Type} [Group G]
    {C₀ P : Subgroup G} (hCP : P ≤ Subgroup.normalizer (C₀ : Set G)) {d : G} {K : Subgroup G}
    (hK : IsComponentOf K (C₀ ⊓ Subgroup.centralizer ({d} : Set G))) (hKP : K ≤ P) :
    IsComponentOf K (Subgroup.centralizer ({d} : Set G) ⊓ P) := by
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G) with hCdef
  have hK1 : IsComponentOf K ((C₀ ⊓ C) ⊓ P) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le hK hKP
  have hEq : (C₀ ⊓ C) ⊓ P = (C₀ ⊓ P) ⊓ C := by
    rw [inf_assoc, inf_comm C P, ← inf_assoc]
  have hK2 : IsComponentOf K ((C₀ ⊓ P) ⊓ C) := hEq ▸ hK1
  have hMN : (C₀ ⊓ P) ⊓ C ≤ P ⊓ C := inf_le_inf_right C inf_le_right
  have hconj : ∀ n ∈ P ⊓ C, ∀ m ∈ (C₀ ⊓ P) ⊓ C, n * m * n⁻¹ ∈ (C₀ ⊓ P) ⊓ C := by
    intro n hn m hm
    obtain ⟨hnP, hnC⟩ := Subgroup.mem_inf.1 hn
    obtain ⟨hmCP, hmC⟩ := Subgroup.mem_inf.1 hm
    obtain ⟨hmC0, hmP⟩ := Subgroup.mem_inf.1 hmCP
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hCP hnP) m).1 hmC0
    · exact P.mul_mem (P.mul_mem hnP hmP) (P.inv_mem hnP)
    · exact C.mul_mem (C.mul_mem hnC hmC) (C.inv_mem hnC)
  have hNorm : (((C₀ ⊓ P) ⊓ C).subgroupOf (P ⊓ C)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMN]
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact hconj n hn m
    · intro hm
      have hinv : n⁻¹ ∈ P ⊓ C := Subgroup.mem_inf.2 ⟨P.inv_mem (Subgroup.mem_inf.1 hn).1,
        C.inv_mem (Subgroup.mem_inf.1 hn).2⟩
      have h := hconj n⁻¹ hinv (n * m * n⁻¹) hm
      have he : n⁻¹ * (n * m * n⁻¹) * (n⁻¹)⁻¹ = m := by group
      rw [he] at h
      exact h
  have hMsub : IsSubnormal ((C₀ ⊓ P) ⊓ C) (P ⊓ C) :=
    IsSubnormal.step hMN hNorm (IsSubnormal.refl (P ⊓ C))
  have hMsub' : IsSubnormal ((C₀ ⊓ P) ⊓ C) (C ⊓ P) := by
    rw [inf_comm C P]
    exact hMsub
  refine ⟨le_inf (hK2.1.trans inf_le_right) (hK2.1.trans (inf_le_left.trans inf_le_right)),
    hK2.2.1.trans hMsub', hK2.2.2⟩

private theorem twistedE6DiagGL_le_normalizer_graphFixedParabolicLevi
    {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    twistedE6DiagGL F σ ≤ Subgroup.normalizer
      (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J : Set (Γ₂ F)) := by
  intro t ht
  have hrange : t ∈ (rootDiagUnitHom TwistTag.E6.tag F).range := by
    obtain ⟨b, -, rfl⟩ := (mem_twistedE6DiagGL_iff F σ).1 ht
    exact MonoidHom.mem_range.2 ⟨b, rfl⟩
  have h1 : t ∈ Subgroup.normalizer
      (parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion J) : Set (Γ₂ F)) :=
    (CFSG.StandardType.OddLayerCentre.parabolic_inndiag_Levi TwistTag.E6.tag F
      (TwistTag.E6.orbitUnion J)).2.1 hrange
  have h2 : t ∈ Subgroup.normalizer (twistedE6RootGroup F σ : Set (Γ₂ F)) :=
    twistedE6DiagGL_le_normalizer_C0 F σ ht
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩

private theorem exists_conj_parabolic_sup_diag_of_layer
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ2 : σ ^ TwistTag.E6.order = 1)
    {R : Subgroup (Γ₂ F)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRG : R ≤ twistedE6RootGroup F σ)
    {A : Subgroup (Γ₂ F)} (hAG : A ≤ twistedE6InndiagGL F σ)
    (hAN : A ≤ Subgroup.normalizer (R : Set (Γ₂ F)))
    {d : Γ₂ F} {L : Subgroup (Γ₂ F)}
    (hLN : L ≤ Subgroup.normalizer (R : Set (Γ₂ F)))
    (hdK : stdLayerD (twistedE6RootGroup F σ) d ≤ L) :
    ∃ g ∈ twistedE6RootGroup F σ, ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
      A.map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
      (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀C, J, hJ, hg₀P⟩ :=
    exists_conj_mem_parabolic_sup_torus F σ hσ2 (by rw [ringChar.eq F 2]; exact Nat.prime_two)
      R hRG (by rw [ringChar.eq F 2]; exact hR2) hR
  let g₀e : Γ₂ F := g₀
  have hg₀eC : g₀e ∈ twistedE6RootGroup F σ := hg₀C
  have hg₀Pe : ∀ x ∈ twistedE6InndiagGL F σ, x ∈ Subgroup.normalizer (R : Set (Γ₂ F)) →
      g₀e⁻¹ * x * g₀e ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔
        twistedE6DiagGL F σ := by
    intro x hx hxN
    exact hg₀P x hx hxN
  let g : Γ₂ F := g₀e⁻¹
  have hgC : g ∈ twistedE6RootGroup F σ := (twistedE6RootGroup F σ).inv_mem hg₀eC
  have hKle : stdLayerD (twistedE6RootGroup F σ) d ≤ twistedE6RootGroup F σ :=
    (Y10F.glaLayer_le (twistedE6RootGroup F σ ⊓
      Subgroup.centralizer ({d} : Set (Γ₂ F)))).trans inf_le_left
  refine ⟨g, hgC, J, hJ, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    change (MulAut.conj g) a ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ
    rw [MulAut.conj_apply]
    have he : g * a * g⁻¹ = g₀e⁻¹ * a * g₀e := by
      simp only [g]
      group
    rw [he]
    exact hg₀Pe a (hAG ha) (hAN ha)
  · rintro _ ⟨k, hk, rfl⟩
    change (MulAut.conj g) k ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ
    rw [MulAut.conj_apply]
    have he : g * k * g⁻¹ = g₀e⁻¹ * k * g₀e := by
      simp only [g]
      group
    rw [he]
    refine hg₀Pe k ?_ (hLN (hdK hk))
    rw [twistedE6InndiagGL]
    exact Subgroup.mem_sup_left (hKle hk)

private theorem exists_conj_levi_sup_diag_twE6
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ2 : σ ^ TwistTag.E6.order = 1)
    {R : Subgroup (Γ₂ F)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRG : R ≤ twistedE6RootGroup F σ)
    {A : Subgroup (Γ₂ F)} (hAodd : Odd (Nat.card A))
    (hAG : A ≤ twistedE6InndiagGL F σ)
    (hAN : A ≤ Subgroup.normalizer (R : Set (Γ₂ F)))
    {d : Γ₂ F} {L : Subgroup (Γ₂ F)}
    (hLN : L ≤ Subgroup.normalizer (R : Set (Γ₂ F)))
    (hdK : stdLayerD (twistedE6RootGroup F σ) d ≤ L) :
    ∃ g ∈ twistedE6RootGroup F σ, ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
      A.map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
      (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
  classical
  obtain ⟨g₀, hg₀C, J, hJ, hAg₀, hKg₀⟩ :=
    exists_conj_parabolic_sup_diag_of_layer σ hσ2 hR hR2 hRG hAG hAN hLN hdK
  have hoddA' : Odd (Nat.card (A.map (MulAut.conj g₀).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
    exact hAodd
  obtain ⟨y, hyQ, hyL⟩ := exists_conj_le_levi_sup_torus F σ J hoddA' hAg₀
  have hyC : y ∈ twistedE6RootGroup F σ :=
    graphFixedParabolicRadical_le_graphFixedRootGroup (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom) J hyQ
  have hyPP : y ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
    refine Subgroup.mem_sup_left ?_
    exact ((graphFixedParabolicRadical_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) J).trans
      (graphFixedPosUnipotent_le_graphFixedRootBorel (t := TwistTag.E6) (K := F)
        (σ := σ.toRingHom))).trans
      (graphFixedRootBorel_le_graphFixedParabolic TwistTag.E6 F σ.toRingHom J) hyQ
  let g : Γ₂ F := y * g₀
  have hgC : g ∈ twistedE6RootGroup F σ :=
    (twistedE6RootGroup F σ).mul_mem hyC hg₀C
  have hconj : ∀ x : Γ₂ F, (MulAut.conj g) x = y * (MulAut.conj g₀) x * y⁻¹ := by
    intro x
    simp only [g, MulAut.conj_apply]
    group
  refine ⟨g, hgC, J, hJ, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    change (MulAut.conj g) a ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ
    rw [hconj]
    exact hyL _ ⟨a, ha, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    change (MulAut.conj g) k ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ
    rw [hconj]
    exact (graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ).mul_mem
      ((graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ).mul_mem hyPP
        (hKg₀ ⟨k, hk, rfl⟩))
      ((graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ).inv_mem hyPP)

private theorem exists_unique_graphFixedParabolic_sup_diag
    {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    ∀ x ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ,
      ∃! ql : (Γ₂ F) × (Γ₂ F),
        ql.1 ∈ graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J ∧
        ql.2 ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
        x = ql.1 * ql.2 := by
  classical
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, -, hQP0, hQn0, hLP0, -, -, -, -, -, -, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors (t := TwistTag.E6) (K := F) σ J
  have hPPL : graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ =
      graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J ⊔
        (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) := by
    rw [graphFixedParabolic_eq_radical_sup_levi F σ J, sup_assoc]
  have hPN : graphFixedParabolic TwistTag.E6 F σ.toRingHom J ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J :
        Set (Γ₂ F)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP0).1 hQn0
  have hLLN : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J :
        Set (Γ₂ F)) :=
    sup_le (hLP0.trans hPN) (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical F σ J)
  have hx' : x ∈ ((graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J ⊔
      (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) :
        Subgroup (Γ₂ F)) : Set (Γ₂ F)) := hPPL ▸ hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLLN] at hx'
  obtain ⟨q, hq, l, hl, rfl⟩ := hx'
  refine ⟨(q, l), ⟨hq, hl, rfl⟩, ?_⟩
  rintro ⟨q', l'⟩ ⟨hq', hl', hql'⟩
  have hql'' : q * l = q' * l' := hql'
  have he : q'⁻¹ * q = l' * l⁻¹ := by
    calc q'⁻¹ * q = q'⁻¹ * (q * l) * l⁻¹ := by group
      _ = q'⁻¹ * (q' * l') * l⁻¹ := by rw [hql'']
      _ = l' * l⁻¹ := by group
  have h1 : q'⁻¹ * q ∈ graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J :=
    (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J).mul_mem
      ((graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J).inv_mem hq') hq
  have h2 : l' * l⁻¹ ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ :=
    (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ).mul_mem hl'
      ((graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ).inv_mem hl)
  have hbot : q'⁻¹ * q = 1 := by
    have hmem : q'⁻¹ * q ∈ graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J ⊓
        (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) :=
      ⟨h1, he ▸ h2⟩
    rw [graphFixedParabolicRadical_inf_levi_sup_torus F σ J] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hbot2 : l' * l⁻¹ = 1 := by rw [← he, hbot]
  rw [inv_mul_eq_one.mp hbot, mul_inv_eq_one.mp hbot2]

private theorem le_graphFixedParabolicLevi_sup_diag_of_isComponentOf
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank))
    {d : Γ₂ F}
    (hd : d ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)
    {Kb : Subgroup (Γ₂ F)}
    (hK : IsComponentOf Kb (Subgroup.centralizer ({d} : Set (Γ₂ F)) ⊓
      (graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ))) :
    Kb ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Γ₂ F) := finite_modGL
  obtain ⟨-, -, -, -, -, -, -, -, hQP0, hQn0, hLP0, -, -, -, -, -, hQgrp, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors (t := TwistTag.E6) (K := F) σ J
  have hQP : graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J ≤
      graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ :=
    hQP0.trans le_sup_left
  have hLP : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ≤
      graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ :=
    sup_le (hLP0.trans le_sup_left) le_sup_right
  have hPPNQ : graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J :
        Set (Γ₂ F)) :=
    sup_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hQP0).1 hQn0)
      (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical F σ J)
  have hQn : ((graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J).subgroupOf
      (graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2 hPPNQ
  have hQ2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J) := hQgrp 2
  have hQs : Group.IsSolvable ↥(graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J) := by
    haveI := hQ2.isNilpotent
    infer_instance
  exact le_of_isComponentOf_centralizer_inf hQP hLP hQn
    (exists_unique_graphFixedParabolic_sup_diag σ J) hQs hd hK

private theorem isComponentOf_map_conj_of_mem_rootGroup
    {F : Type} [Field F] [Finite F] (σ : F ≃+* F) {g d : Γ₂ F}
    (hg : g ∈ twistedE6RootGroup F σ) {Kb : Subgroup (Γ₂ F)}
    (hK : IsComponentOf Kb (twistedE6RootGroup F σ ⊓
      Subgroup.centralizer ({d} : Set (Γ₂ F)))) :
    IsComponentOf (Kb.map (MulAut.conj g).toMonoidHom)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({(MulAut.conj g) d} :
        Set (Γ₂ F))) := by
  have hmap : (twistedE6RootGroup F σ).map (MulAut.conj g).toMonoidHom =
      twistedE6RootGroup F σ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact (twistedE6RootGroup F σ).mul_mem
        ((twistedE6RootGroup F σ).mul_mem hg hc)
        ((twistedE6RootGroup F σ).inv_mem hg)
    · intro c hc
      refine ⟨g⁻¹ * c * g, (twistedE6RootGroup F σ).mul_mem
        ((twistedE6RootGroup F σ).mul_mem ((twistedE6RootGroup F σ).inv_mem hg) hc)
        hg, ?_⟩
      change g * (g⁻¹ * c * g) * g⁻¹ = c
      group
  have h := (Y10F.isComponentOf_map_iff (ι := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).2 hK
  rwa [CFSG.centralizer_inter_map (MulAut.conj g) (twistedE6RootGroup F σ) d, hmap] at h

private theorem le_graphFixedParabolicLevi_of_perfect
    {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {Kb : Subgroup (Γ₂ F)}
    (hK : Kb ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)
    (hperf : ⁅Kb, Kb⁆ = Kb) :
    Kb ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  have hTDN : twistedE6DiagGL F σ ≤ Subgroup.normalizer
      (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J : Set (Γ₂ F)) :=
    twistedE6DiagGL_le_normalizer_graphFixedParabolicLevi σ J
  have hTDcomm : ∀ a ∈ twistedE6DiagGL F σ, ∀ b ∈ twistedE6DiagGL F σ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ba, -, rfl⟩ := (mem_twistedE6DiagGL_iff F σ).1 ha
    obtain ⟨bb, -, rfl⟩ := (mem_twistedE6DiagGL_iff F σ).1 hb
    calc rootDiagUnit TwistTag.E6.tag ba * rootDiagUnit TwistTag.E6.tag bb
        = rootDiagUnit TwistTag.E6.tag (ba * bb) := (rootDiagUnit_mul ba bb).symm
      _ = rootDiagUnit TwistTag.E6.tag (bb * ba) := by rw [mul_comm]
      _ = rootDiagUnit TwistTag.E6.tag bb * rootDiagUnit TwistTag.E6.tag ba :=
          rootDiagUnit_mul bb ba
  have hcommle : ⁅graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ,
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ⁆ ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J :=
    CFSG.RankThree.PartOne.K159H.commutator_sup_le hTDN hTDcomm
  calc Kb = ⁅Kb, Kb⁆ := hperf.symm
    _ ≤ ⁅graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ,
          graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ⁆ :=
        Subgroup.commutator_mono hK hK
    _ ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := hcommle

private theorem le_graphFixedParabolicLevi_map_of_isComponentOf
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {g d : Γ₂ F}
    (hg : g ∈ twistedE6RootGroup F σ) {K : Subgroup (Γ₂ F)}
    (hcomp : IsComponentOf K (twistedE6RootGroup F σ ⊓
      Subgroup.centralizer ({d} : Set (Γ₂ F))))
    (hKP : K.map (MulAut.conj g).toMonoidHom ≤
      graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)
    (hdg : (MulAut.conj g) d ∈
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) :
    K.map (MulAut.conj g).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
  have hcompg := isComponentOf_map_conj_of_mem_rootGroup σ hg hcomp
  have hPPN : graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ≤
      Subgroup.normalizer (twistedE6RootGroup F σ : Set (Γ₂ F)) :=
    sup_le ((graphFixedParabolic_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) J).trans
      Subgroup.le_normalizer) (twistedE6DiagGL_le_normalizer_C0 F σ)
  have hcompP : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({(MulAut.conj g) d} : Set (Γ₂ F)) ⊓
        (graphFixedParabolic TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)) :=
    isComponentOf_centralizer_inf_of_le_normalizer hPPN hcompg hKP
  exact le_graphFixedParabolicLevi_sup_diag_of_isComponentOf σ J hdg hcompP

theorem exists_conj_levi_twE6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {R : Subgroup (Γ₂ F)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hRG : R ≤ twistedE6RootGroup F σ)
    {A L : Subgroup (Γ₂ F)} (hA3 : IsPGroup 3 A) (hAG : A ≤ twistedE6InndiagGL F σ)
    (hAN : A ≤ Subgroup.normalizer (R : Set (Γ₂ F)))
    (hLN : L ≤ Subgroup.normalizer (R : Set (Γ₂ F))) {d : Γ₂ F} (hdA : d ∈ A)
    (hdK : stdLayerD (twistedE6RootGroup F σ) d ≤ L)
    (hcomp : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)))) :
    ∃ g ∈ twistedE6RootGroup F σ, ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
      A.map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
      (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  classical
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    have ho : TwistTag.E6.order = 2 := rfl
    rw [ho, pow_two]
    ext c
    haveI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 2 ^ n * 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, hF, pow_two]
    show σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← hcard, FiniteField.pow_card]
  haveI : CharP F 2 := by
    have hF2 : Nat.card F = 2 ^ (2 * n) := by
      rw [hF, pow_two, ← pow_add, show n + n = 2 * n by omega]
    exact CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF2
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨k, hk⟩ := hA3.exists_card_eq
    rw [hk]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  obtain ⟨g, hgC, J, hJ, hAg, hKg⟩ :=
    exists_conj_levi_sup_diag_twE6 σ hσ2 hR hR2 hRG hAodd hAG hAN hLN hdK
  have hdg : (MulAut.conj g) d ∈
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ :=
    hAg ⟨d, hdA, rfl⟩
  have hKLL : (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ :=
    le_graphFixedParabolicLevi_map_of_isComponentOf σ J hgC hcomp hKg hdg
  have hperfK : ⁅stdLayerD (twistedE6RootGroup F σ) d,
      stdLayerD (twistedE6RootGroup F σ) d⁆ = stdLayerD (twistedE6RootGroup F σ) d := by
    have h := congrArg (Subgroup.map (stdLayerD (twistedE6RootGroup F σ) d).subtype)
      hcomp.2.2.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hperfKg : ⁅(stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom,
      (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom⁆ =
      (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hperfK]
  exact ⟨g, hgC, J, hJ, hAg, le_graphFixedParabolicLevi_of_perfect σ J hKLL hperfKg⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
