module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapEdge
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam TwistOn)

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def modelEmb (e : L ≃* adjointGroup .F4 K) : adjointGroup .F4 K →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem modelEmb_injective (e : L ≃* adjointGroup .F4 K) : Function.Injective (modelEmb e) :=
  L.subtype_injective.comp e.symm.injective

theorem subgroupToG_eq_map (e : L ≃* adjointGroup .F4 K) (H : Subgroup (adjointGroup .F4 K)) :
    subgroupToG e H = H.map (modelEmb e) := by
  rw [subgroupToG, Subgroup.map_map]
  rfl

theorem subgroupToG_sup (e : L ≃* adjointGroup .F4 K) (H H' : Subgroup (adjointGroup .F4 K)) :
    subgroupToG e (H ⊔ H') = subgroupToG e H ⊔ subgroupToG e H' := by
  rw [subgroupToG_eq_map, subgroupToG_eq_map, subgroupToG_eq_map, Subgroup.map_sup]

theorem subgroupToG_inf_centralizer (e : L ≃* adjointGroup .F4 K)
    (H X : Subgroup (adjointGroup .F4 K)) :
    subgroupToG e H ⊓ centralizer (subgroupToG e X : Set G) =
      subgroupToG e (H ⊓ centralizer (X : Set (adjointGroup .F4 K))) := by
  rw [subgroupToG_eq_map, subgroupToG_eq_map, subgroupToG_eq_map]
  ext g
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hc⟩
    have hc' := mem_centralizer_iff.1 hc
    refine ⟨h, ⟨hh, mem_centralizer_iff.2 fun x hx => ?_⟩, rfl⟩
    apply modelEmb_injective e
    rw [map_mul, map_mul]
    exact hc' _ ⟨x, hx, rfl⟩
  · rintro ⟨h, ⟨hh, hc⟩, rfl⟩
    have hc' := mem_centralizer_iff.1 hc
    refine ⟨⟨h, hh, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hc' x hx]

theorem perfectCore_subgroupToG
    [Finite G] [Finite K] (e : L ≃* adjointGroup .F4 K)
    (H : Subgroup (adjointGroup .F4 K)) :
    perfectCore (subgroupToG e H) = subgroupToG e (perfectCore H) := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup .F4 K) := inferInstance
  rw [subgroupToG_eq_map, subgroupToG_eq_map, CFSG.Quasithin.map_perfectCore]

@[expose] noncomputable def subgroupToGEquiv (e : L ≃* adjointGroup .F4 K)
    (H : Subgroup (adjointGroup .F4 K)) : H ≃* subgroupToG e H :=
  (H.equivMapOfInjective (modelEmb e) (modelEmb_injective e)).trans
    (MulEquiv.subgroupCongr (subgroupToG_eq_map e H).symm)

theorem commute_of_mem_subgroupToG (e : L ≃* adjointGroup .F4 K)
    {B Y : Subgroup (adjointGroup .F4 K)} (hBY : B ≤ centralizer (Y : Set (adjointGroup .F4 K)))
    {u : G} (hu : u ∈ subgroupToG e B) : ∀ y ∈ subgroupToG e Y, u * y = y * u := by
  rw [subgroupToG_eq_map] at hu
  obtain ⟨b, hb, rfl⟩ := hu
  intro y hy
  rw [subgroupToG_eq_map] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  rw [← map_mul, ← map_mul, (mem_centralizer_iff.1 (hBY hb) y hy).symm]

theorem conj_mem_of_mem_subgroupToG (e : L ≃* adjointGroup .F4 K)
    {B Y : Subgroup (adjointGroup .F4 K)} (hBY : B ≤ normalizer (Y : Set (adjointGroup .F4 K)))
    {u : G} (hu : u ∈ subgroupToG e B) : ∀ y ∈ subgroupToG e Y, u * y * u⁻¹ ∈ subgroupToG e Y := by
  rw [subgroupToG_eq_map] at hu ⊢
  obtain ⟨b, hb, rfl⟩ := hu
  intro y hy
  obtain ⟨y, hy, rfl⟩ := hy
  refine ⟨b * y * b⁻¹, (mem_normalizer_iff.1 (hBY hb) y).1 hy, ?_⟩
  rw [map_mul, map_mul, map_inv]

end Transport

theorem forall_mulAut_eq_conj_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ φ : MulAut A, ∃ a, φ = MulAut.conj a) : ∀ φ : MulAut B, ∃ b, φ = MulAut.conj b := by
  intro φ
  obtain ⟨a, ha⟩ := h ((e.trans φ).trans e.symm)
  refine ⟨e a, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun ψ : MulAut A => ψ (e.symm x)) ha
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.symm.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

section Std


variable (K : Type) [Field K]

@[expose] noncomputable def stdOverlap (xPP : Subgroup (adjointGroup .F4 K)) :
    Subgroup (adjointGroup .F4 K) :=
  perfectCore (C3Levi K ⊓ centralizer (xPP : Set (adjointGroup .F4 K)))

@[expose] noncomputable def stdOverlapCentralizer (xPP : Subgroup (adjointGroup .F4 K)) :
    Subgroup (adjointGroup .F4 K) :=
  C3Levi K ⊓ centralizer (stdOverlap K xPP : Set (adjointGroup .F4 K)) ⊓
    centralizer (xPP : Set (adjointGroup .F4 K))

structure TwoStdPairFacts (xPP bPP : Subgroup (adjointGroup .F4 K)) : Prop where
  xPP_le : xPP ≤ C3Levi K
  bPP_le : bPP ≤ C3Levi K
  bPP_le_centralizer : bPP ≤ centralizer (xPP : Set (adjointGroup .F4 K))
  isSimpleGroup : IsSimpleGroup (stdOverlap K xPP)
  center_eq_bot : center (stdOverlap K xPP) = ⊥
  odd_card : Odd (Nat.card (stdOverlapCentralizer K xPP))
  bPP_le_normalizer : bPP ≤ normalizer (stdOverlap K xPP : Set (adjointGroup .F4 K))
  bPP_le_centralizer_overlap :
    bPP ≤ centralizer (stdOverlapCentralizer K xPP : Set (adjointGroup .F4 K))

end Std

section Edge


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_twistOn_of_frames_F4_two {t : G} (hw : F4Work L K t 1)
    {xPP bPP : Subgroup (adjointGroup .F4 K)} (hF : TwoStdPairFacts K xPP bPP)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (ε₁ ε₂ : L ≃* adjointGroup .F4 K) {D₁ D₂ : Subgroup G}
    (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂) (hinj₁ : Function.Injective P₁.Ψ)
    (hinj₂ : Function.Injective P₂.Ψ) (hD₁ : D₁ = subgroupToG ε₁ (C3Levi K))
    (hD₂ : D₂ = subgroupToG ε₂ (C3Levi K))
    (hr₁ : P₁.Ψ.range = centralizerPerfectCore (subgroupToG ε₁ X₀))
    (hr₂ : P₂.Ψ.range = centralizerPerfectCore (subgroupToG ε₂ X₀))
    (hT : subgroupToG ε₁ (X₀ ⊔ xPP) = subgroupToG ε₂ (X₀ ⊔ xPP)) (S : Set G)
    (hS : ∀ u ∈ S, u ∈ subgroupToG ε₁ bPP ∧ u ∈ subgroupToG ε₂ bPP ∧ ∃ k : ℕ, u ^ 2 ^ k = 1) :
    ∃ s : ℤˣ, TwistOn s P₁ P₂ (closure S) := by
  subst hD₁ hD₂
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hO : perfectCore (subgroupToG ε₁ (C3Levi K) ⊓
      centralizer (subgroupToG ε₁ xPP : Set G)) = subgroupToG ε₁ (stdOverlap K xPP) := by
    rw [subgroupToG_inf_centralizer, perfectCore_subgroupToG]
    rfl
  have hZ : subgroupToG ε₁ (C3Levi K) ⊓ centralizer (perfectCore (subgroupToG ε₁ (C3Levi K) ⊓
      centralizer (subgroupToG ε₁ xPP : Set G)) : Set G) ⊓
      centralizer (subgroupToG ε₁ xPP : Set G) = subgroupToG ε₁ (stdOverlapCentralizer K xPP) := by
    rw [hO, subgroupToG_inf_centralizer, subgroupToG_inf_centralizer]
    rfl
  have := isSimpleGroup_C3Levi (K := K)
  have : IsSimpleGroup (subgroupToG ε₁ (C3Levi K)) :=
    (subgroupToGEquiv ε₁ (C3Levi K)).symm.isSimpleGroup
  have := hF.isSimpleGroup
  have : IsSimpleGroup (perfectCore (subgroupToG ε₁ (C3Levi K) ⊓
      centralizer (subgroupToG ε₁ xPP : Set G))) := by
    rw [hO]
    exact (subgroupToGEquiv ε₁ (stdOverlap K xPP)).symm.isSimpleGroup
  have hZDX : ∀ a : subgroupToG ε₁ (C3Levi K),
      (∀ b : subgroupToG ε₁ (C3Levi K), a * b = b * a) → a = 1 := by
    intro a ha
    have hc : a ∈ center (subgroupToG ε₁ (C3Levi K)) := mem_center_iff.2 fun b => (ha b).symm
    rw [center_subgroupToG_C3Levi_eq_bot, mem_bot] at hc
    exact hc
  have hAut : ∀ φ : MulAut (subgroupToG ε₁ (C3Levi K)), ∃ g, φ = MulAut.conj g :=
    forall_mulAut_eq_conj_of_mulEquiv (subgroupToGEquiv ε₁ (C3Levi K))
      (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_of_lieModel
        (lieModel_C3Levi hw.card_eq))
  have hZc : center (perfectCore (subgroupToG ε₁ (C3Levi K) ⊓
      centralizer (subgroupToG ε₁ xPP : Set G))) = ⊥ := by
    rw [hO]
    exact center_eq_bot_congr (subgroupToGEquiv ε₁ (stdOverlap K xPP)) hF.center_eq_bot
  have hZodd : Odd (Nat.card (subgroupToG ε₁ (C3Levi K) ⊓ centralizer
      (perfectCore (subgroupToG ε₁ (C3Levi K) ⊓ centralizer (subgroupToG ε₁ xPP : Set G)) :
        Set G) ⊓ centralizer (subgroupToG ε₁ xPP : Set G) : Subgroup G)) := by
    rw [hZ, ← Nat.card_congr (subgroupToGEquiv ε₁ (stdOverlapCentralizer K xPP)).toEquiv]
    exact hF.odd_card
  have hWodd := odd_card_centralizer_inf_centralizer_nonsplit_F4_two hw ε₁ hXJ hcyc hX₀ P₁ hr₁
  have hT' : subgroupToG ε₁ X₀ ⊔ subgroupToG ε₁ xPP = subgroupToG ε₂ X₀ ⊔ subgroupToG ε₂ xPP := by
    rw [← subgroupToG_sup, ← subgroupToG_sup, hT]
  refine exists_twistOn_of_edge_of_odd ht2 P₁ P₂ hinj₁ hinj₂ hr₁ hr₂
    (subgroupToG_mono ε₁ hF.xPP_le) (subgroupToG_mono ε₂ hF.xPP_le) hT' hZDX hAut hZc hZodd
    hWodd S fun u hu => ?_
  obtain ⟨hu₁, hu₂, hk⟩ := hS u hu
  refine ⟨subgroupToG_mono ε₁ hF.bPP_le hu₁, subgroupToG_mono ε₂ hF.bPP_le hu₂,
    commute_of_mem_subgroupToG ε₁ hF.bPP_le_centralizer hu₁,
    commute_of_mem_subgroupToG ε₂ hF.bPP_le_centralizer hu₂, ?_, ?_, hk⟩
  · rw [hO]
    exact conj_mem_of_mem_subgroupToG ε₁ hF.bPP_le_normalizer hu₁
  · rw [hZ]
    exact commute_of_mem_subgroupToG ε₁ hF.bPP_le_centralizer_overlap hu₁

end Edge

end CFSG.SeitzReduction.F4Pilot
