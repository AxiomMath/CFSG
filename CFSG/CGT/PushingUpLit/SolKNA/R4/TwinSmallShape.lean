module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallCore
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups commutatorElement

theorem commute_of_solvable_subnormal {F : Type} [Group F] [Finite F] {C I X : Subgroup F}
    (hI : CFSG.Open.IsSubnormal I C) (hIq : CFSG.IsQuasisimple ↥I)
    (hX : CFSG.Open.IsSubnormal X C) (hXs : Group.IsSolvable ↥X) :
    ∀ a ∈ I, ∀ x ∈ X, a * x = x * a := by
  have hIC : I ≤ C := hI.le
  have hXC : X ≤ C := hX.le
  have hLsub : (I.subgroupOf C).IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hIC).1 hI
  have hRsub : (X.subgroupOf C).IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hXC).1 hX
  have hLq : CFSG.IsQuasisimple ↥(I.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hIC).symm hIq
  have hRsolv : Group.IsSolvable ↥(X.subgroupOf C) :=
    solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hXC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXC).injective
  have hcent := (CFSG.LocalCores.component_solvable_centralizer hRsolv hRsub).1 _
    ⟨hLq, hLsub⟩
  intro a ha x hx
  have h1 : ⁅(⟨a, hIC ha⟩ : ↥C), (⟨x, hXC hx⟩ : ↥C)⁆ ∈ ⁅I.subgroupOf C, X.subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr ha)
      (Subgroup.mem_subgroupOf.mpr hx)
  rw [hcent, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp h1)

@[expose] def TwoCompShape (F : Type) [Group F] : Prop :=
  ∀ z : F, orderOf z = 2 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁)
    (_ : Finite F₂) (I₁ I₂ : Subgroup F), Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧
      4 ≤ Nat.card F₁ ∧ 4 ≤ Nat.card F₂ ∧
      CFSG.Open.IsSubnormal I₁ (Subgroup.centralizer ({z} : Set F)) ∧
      CFSG.Open.IsSubnormal I₂ (Subgroup.centralizer ({z} : Set F)) ∧
      (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) ∧ Nonempty (↥I₁ ≃* SL(2, F₁)) ∧
      Nonempty (↥I₂ ≃* SL(2, F₂))

theorem not_twinPair_of_twoCompShape {F : Type} [Group F] [Finite F] (hsh : TwoCompShape F)
    (hsmall : TwoSubgroupsFourGenerated F) : ¬ TwinPair F := by
  rintro ⟨z, X₁, X₂, u₁, u₂, hz, hX₁, hX₂, hs₁, hs₂, hu₁, hu₂, ho₁, ho₂, hsq₁, hsq₂, hne⟩
  obtain ⟨F₁, F₂, _, _, _, _, I₁, I₂, hF₁, hF₂, h4₁, h4₂, hsI₁, hsI₂, hcomm, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    hsh z hz
  have hq₁ : CFSG.IsQuasisimple ↥I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4₁)
  have hq₂ : CFSG.IsQuasisimple ↥I₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4₂)
  have hc₁ : ∀ a ∈ I₁, a * u₁ = u₁ * a := fun a ha =>
    commute_of_solvable_subnormal hsI₁ hq₁ hs₁ hX₁ a ha u₁ hu₁
  have hc₂ : ∀ b ∈ I₂, b * u₁ = u₁ * b := fun b hb =>
    commute_of_solvable_subnormal hsI₂ hq₂ hs₁ hX₁ b hb u₁ hu₁
  obtain ⟨φ₁, hi₁, hr₁, -⟩ := exists_q8_of_mulEquiv_sl2 hF₁ I₁ e₁
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hF₂ I₂ e₂
  have hu4 : u₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one u₁
    rwa [ho₁] at this
  let χ := LocalAnalysis.ComponentInitial.zmodHom 4 u₁ hu4
  have hχi : Function.Injective χ := Q5Cube.zmodHom_injective hu4 ho₁
  have hχc : ∀ (v : F), Commute v u₁ → ∀ m, Commute v (χ m) := by
    intro v hv m
    rcases Q5Cube.z4_cases m with rfl | rfl | rfl | rfl <;>
      simp only [map_one, map_pow, LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one, χ]
    · exact Commute.one_right v
    · exact hv
    · exact hv.pow_right 2
    · exact hv.pow_right 3
  exact Q5Cube.not_gen4_of_q8_q8_z4 φ₁ φ₂ χ hi₁ hi₂ hχi
    (fun x y => hcomm _ (hr₁ x) _ (hr₂ y))
    (fun x m => hχc _ (hc₁ _ (hr₁ x)) m) (fun y m => hχc _ (hc₂ _ (hr₂ y)) m) hsmall

theorem isSubnormal_map_subtype {F : Type} [Group F] {C : Subgroup F} (I : Subgroup ↥C)
    (hI : I.Normal) : CFSG.Open.IsSubnormal (I.map C.subtype) C := by
  refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le I) ?_ (CFSG.Open.IsSubnormal.refl C)
  have : (I.map C.subtype).subgroupOf C = I :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective I
  rw [this]
  exact hI

theorem twoCompShape_of_shape {F : Type} [Group F] {z : F} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (Sh : Shape ↥(Subgroup.centralizer ({z} : Set F)) F₁ F₂) :
    ∃ (I₁ I₂ : Subgroup F), CFSG.Open.IsSubnormal I₁ (Subgroup.centralizer ({z} : Set F)) ∧
      CFSG.Open.IsSubnormal I₂ (Subgroup.centralizer ({z} : Set F)) ∧
      (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) ∧ Nonempty (↥I₁ ≃* SL(2, F₁)) ∧
      Nonempty (↥I₂ ≃* SL(2, F₂)) := by
  set C := Subgroup.centralizer ({z} : Set F)
  refine ⟨Sh.I₁.map C.subtype, Sh.I₂.map C.subtype,
    isSubnormal_map_subtype _ Sh.normal₁, isSubnormal_map_subtype _ Sh.normal₂, ?_,
    ⟨(Subgroup.equivMapOfInjective Sh.I₁ C.subtype C.subtype_injective).symm.trans Sh.e₁⟩,
    ⟨(Subgroup.equivMapOfInjective Sh.I₂ C.subtype C.subtype_injective).symm.trans Sh.e₂⟩⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (Sh.comm a ha b hb)

theorem socleComm2_of_outTwoCyclic {F : Type} [Group F] (h : Nobq.OutTwoCyclic F) :
    SocleComm2 F := by
  have : SocleOutAbelian F := fun P hP => by
    haveI := h P hP
    exact IsCyclic.isMulCommutative
  exact this.comm2


theorem twoCompShape_g2 {F : Type} [Group F] [Finite F] (h : SmallG2Ne3 F) : TwoCompShape F := by
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := h
  intro z hz
  obtain ⟨F', _, _, Sh, hcard, -⟩ := GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hm z hz
  obtain ⟨ho, h4⟩ := odd_four_le_of_card hp hp2 (Q5G2D4.five_le hp hp2 hf h3) le_rfl
    (hcard.trans (pow_one _).symm)
  obtain ⟨I₁, I₂, hs₁, hs₂, hc, he₁, he₂⟩ := twoCompShape_of_shape Sh
  exact ⟨F', F', inferInstance, inferInstance, inferInstance, inferInstance, I₁, I₂, ho, ho, h4, h4,
    hs₁, hs₂, hc, he₁, he₂⟩


theorem twoCompShape_d4 {F : Type} [Group F] [Finite F] (h : SmallD4Ne3 F) : TwoCompShape F := by
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := h
  intro z hz
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, -⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hm z hz
  have h5 := Q5G2D4.five_le hp hp2 hf h3
  obtain ⟨ho₁, h4₁⟩ := odd_four_le_of_card hp hp2 h5 (by norm_num) hc₁
  obtain ⟨ho₂, h4₂⟩ := odd_four_le_of_card hp hp2 h5 le_rfl (hc₂.trans (pow_one _).symm)
  obtain ⟨I₁, I₂, hs₁, hs₂, hc, he₁, he₂⟩ := twoCompShape_of_shape Sh
  exact ⟨F₁, F₂, inferInstance, inferInstance, inferInstance, inferInstance, I₁, I₂, ho₁, ho₂, h4₁,
    h4₂, hs₁, hs₂, hc, he₁, he₂⟩

theorem false_of_g2Ne3 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar Y))
    (hF : SmallG2Ne3 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)
  exact not_twinPair_of_twoCompShape (twoCompShape_g2 ⟨p, f, hp, hp2, hf, h3, hm⟩) hsmall
    (exists_twinPair_of_perp hr h (socleComm2_of_outTwoCyclic (outTwoCyclic_G2 hp2 hce)))

theorem false_of_d4Ne3 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar Y))
    (hF : SmallD4Ne3 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)
  exact not_twinPair_of_twoCompShape (twoCompShape_d4 ⟨p, f, hp, hp2, hf, h3, hm⟩) hsmall
    (exists_twinPair_of_perp hr h (socleComm2_of_outTwoCyclic (outTwoCyclic_trialityD4 hp2 hce)))

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
