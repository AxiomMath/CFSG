module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Block
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf23AViolA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
open scoped commutatorElement

section Close

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem map_mem_aStar_of_mem_aStar_omegaAFam (hΩ : HypOmegaGen Ω)
    (hcore : ∀ P ∈ Ω, tightCore P = P) {L L' X : Subgroup G} (hL : L ∈ Ω)
    (hXB : X ≤ conjStab (aStar Ω L)) (hBX : ∀ M ∈ aStar Ω L, M ≤ X) (hL' : L' ∈ aStar Ω L)
    {Q' : Subgroup ↥X} (hQ' : Q' ∈ aStar (omegaAFam Ω X) (L'.subgroupOf X)) :
    Q'.map X.subtype ∈ aStar Ω L := by
  have hΩc := hΩ.conjInvariant
  have hΦ : HypOmegaGen (omegaAFam Ω X) := hypOmegaGen_omegaAFam hΩ X
  have hBΩ : ∀ {M : Subgroup G}, M ∈ aStar Ω L → M ∈ Ω := fun hM => mem_of_mem_aStar hL hM
  have hBΦ : ∀ {M : Subgroup G}, M ∈ aStar Ω L → M.subgroupOf X ∈ omegaAFam Ω X :=
    fun hM => subgroupOf_mem_omegaAFam (hBΩ hM) (hcore _ (hBΩ hM)) (hBX _ hM)
  have hinv : ∀ {Q R : Subgroup G} {w : ↥X}, Q ∈ Ω → IsSylow2In R Q → R ≤ X →
      IsUniqueInvolution ((tightCore (Q ⊓ X)).subgroupOf X) w → IsUniqueInvolution Q (w : G) := by
    intro Q R w hQ hR hRX hw
    have h1 : IsUniqueInvolution (tightCore (Q ⊓ X)) (w : G) :=
      isUniqueInvolution_of_subgroupOf hw ((tightCore_le _).trans inf_le_right)
    obtain ⟨zQ, hzQ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hQ
    rw [h1.eq (isUniqueInvolution_core hΩ hQ hR hRX hzQ)]
    exact hzQ
  have hfin : ∀ {Q : Subgroup G}, Q ∈ Ω → Q ∈ aStar Ω L →
      ((tightCore (Q ⊓ X)).subgroupOf X).map X.subtype ∈ aStar Ω L := by
    intro Q hQ hQB
    rwa [Subgroup.map_subgroupOf_eq_of_le ((tightCore_le _).trans inf_le_right),
      tightCore_inf_eq_of_le (hcore Q hQ) (hBX _ hQB)]
  induction hQ' with
  | refl =>
    rw [Subgroup.map_subgroupOf_eq_of_le (hBX _ hL')]
    exact hL'
  | @tail b c _ hbc ih =>
    obtain ⟨L₁, hL₁B, rfl⟩ : ∃ L₁ ∈ aStar Ω L, b = L₁.subgroupOf X :=
      ⟨b.map X.subtype, ih, (subgroupOf_map_subtype' b).symm⟩
    have hL₁X : L₁ ≤ X := hBX _ hL₁B
    obtain ⟨hcΦ, hA | hA | ⟨htw, -⟩⟩ := hbc
    ·
      obtain ⟨Q, hQ, ⟨R, hR, hRX⟩, rfl⟩ := exists_of_mem_omegaAFam hcΦ
      refine hfin hQ ?_
      obtain ⟨zb, zc, hv⟩ := hA
      have hinA : InA (omegaAFam Ω X) (L₁.subgroupOf X) ((tightCore (Q ⊓ X)).subgroupOf X) :=
        ⟨hv.star, hv.not_nbr, zb, zc, hv.hzK, hv.hzJ, fun ⟨g, hg, h⟩ => hv.no_conj g hg h⟩
      obtain ⟨-, -, -, -, Kstar, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htw', ⟨y, -, hyc⟩, -⟩ :=
        Sec6Gen.l6_4ThreeGen ↥X (omegaAFam Ω X) hΦ _ (hBΦ hL₁B) _ hcΦ hinA zb zc hv.hzK hv.hzJ _ _
          rfl rfl
      obtain ⟨hKsΦ, w, hwb, hwK⟩ : Kstar ∈ twinSet (omegaAFam Ω X) (L₁.subgroupOf X) := by
        rw [htw']
        exact Or.inr rfl
      obtain ⟨Q', hQ', ⟨R', hR', hR'X⟩, rfl⟩ := exists_of_mem_omegaAFam hKsΦ
      have hwL₁ : IsUniqueInvolution L₁ (w : G) := isUniqueInvolution_of_subgroupOf hwb hL₁X
      have hQ'B : Q' ∈ aStar Ω L := mem_aStar_of_twin hL₁B hQ' hwL₁ (hinv hQ' hR' hR'X hwK)
      have hQ'X : tightCore (Q' ⊓ X) = Q' := tightCore_inf_eq_of_le (hcore Q' hQ') (hBX _ hQ'B)
      rw [conjSub_subgroupOf] at hyc
      have hyQ0X : conjSub (y : G) (tightCore (Q ⊓ X)) ≤ X := by
        have := conjSub_mono (n := (y : G)) ((tightCore_le (Q ⊓ X)).trans inf_le_right)
        rwa [conjSub_eq_self_of_mem y.2] at this
      have e1 : conjSub (y : G) (tightCore (Q ⊓ X)) = Q' := by
        have := Subgroup.subgroupOf_inj.mp hyc
        rwa [inf_eq_left.mpr hyQ0X, inf_eq_left.mpr ((tightCore_le _).trans inf_le_right),
          hQ'X] at this
      have hle : Q' ≤ conjSub (y : G) Q := by
        rw [← e1]
        exact conjSub_mono ((tightCore_le _).trans inf_le_left)
      have e2 : Q' = conjSub (y : G) Q := member_eq_of_le hΩ hQ' (hΩc _ Q hQ) hle
      have hyQ : conjSub (y : G) Q ∈ aStar Ω L := by
        rw [← e2]
        exact hQ'B
      exact (mem_conjStab_iff.mp (hXB y.2) Q).mp hyQ
    ·
      obtain ⟨Q, hQ, ⟨R, hR, hRX⟩, rfl⟩ := exists_of_mem_omegaAFam hcΦ
      refine hfin hQ ?_
      obtain ⟨zc, zb, hv⟩ := hA
      have hinA : InA (omegaAFam Ω X) ((tightCore (Q ⊓ X)).subgroupOf X) (L₁.subgroupOf X) :=
        ⟨hv.star, hv.not_nbr, zc, zb, hv.hzK, hv.hzJ, fun ⟨g, hg, h⟩ => hv.no_conj g hg h⟩
      obtain ⟨-, -, -, -, Kstar, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htw', ⟨y, -, hyb⟩, -⟩ :=
        Sec6Gen.l6_4ThreeGen ↥X (omegaAFam Ω X) hΦ _ hcΦ _ (hBΦ hL₁B) hinA zc zb hv.hzK hv.hzJ _ _
          rfl rfl
      obtain ⟨hKsΦ, w, hwc, hwK⟩ :
          Kstar ∈ twinSet (omegaAFam Ω X) ((tightCore (Q ⊓ X)).subgroupOf X) := by
        rw [htw']
        exact Or.inr rfl
      obtain ⟨Q', hQ', ⟨R', hR', hR'X⟩, rfl⟩ := exists_of_mem_omegaAFam hKsΦ
      rw [conjSub_subgroupOf] at hyb
      have hyL₁B : conjSub (y : G) L₁ ∈ aStar Ω L := (mem_conjStab_iff.mp (hXB y.2) L₁).mpr hL₁B
      have e1 : conjSub (y : G) L₁ = tightCore (Q' ⊓ X) := by
        have := Subgroup.subgroupOf_inj.mp hyb
        rwa [inf_eq_left.mpr (hBX _ hyL₁B), inf_eq_left.mpr ((tightCore_le _).trans inf_le_right)]
          at this
      have e2 : conjSub (y : G) L₁ = Q' :=
        member_eq_of_le hΩ (hBΩ hyL₁B) hQ' (e1.le.trans ((tightCore_le _).trans inf_le_left))
      have hQ'B : Q' ∈ aStar Ω L := by
        rw [← e2]
        exact hyL₁B
      exact mem_aStar_of_twin hQ'B hQ (hinv hQ' hR' hR'X hwK) (hinv hQ hR hRX hwc)
    ·
      obtain ⟨Q, hQ, ⟨R, hR, hRX⟩, rfl⟩ := exists_of_mem_omegaAFam hcΦ
      refine hfin hQ ?_
      obtain ⟨-, w, hwb, hwc⟩ := htw
      exact mem_aStar_of_twin hL₁B hQ (isUniqueInvolution_of_subgroupOf hwb hL₁X)
        (hinv hQ hR hRX hwc)

private theorem omegaAFam_thm3_data (hΩ : TypeRHyp Ω) (hcore : ∀ P ∈ Ω, tightCore P = P)
    (hb : Thm3A.Thm3RBelowG (Nat.card G)) {L L' J Q R X : Subgroup G} {zL zJ : G} (hL : L ∈ Ω)
    (hXB : X ≤ conjStab (aStar Ω L)) (hBX : ∀ M ∈ aStar Ω L, M ≤ X) (hX : X ≠ ⊤)
    (hL' : L' ∈ aStar Ω L) (hv : AViol Ω L' J zL zJ) (hQ : Q ∈ Ω) (hQB : Q ∉ aStar Ω L)
    (hR : IsSylow2In R Q) (hRX : R ≤ X) :
    Thm3A.Thm3RGroupQuotG ↥X ∧ TypeRHyp (omegaAFam Ω X) ∧
      L'.subgroupOf X ∈ omegaAFam Ω X ∧ ¬ AEmpty (omegaAFam Ω X) (L'.subgroupOf X) ∧
      (tightCore (Q ⊓ X)).subgroupOf X ∈ omegaAFam Ω X ∧
      (tightCore (Q ⊓ X)).subgroupOf X ∉ aStar (omegaAFam Ω X) (L'.subgroupOf X) := by
  have hlt : Nat.card ↥X < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group X)
      (fun h => hX ((Subgroup.card_eq_iff_eq_top X).mp h))
  have hL'Ω : L' ∈ Ω := mem_of_mem_aStar hL hL'
  have hL'X : L' ≤ X := hBX _ hL'
  have hJX : J ≤ X := hBX _ (hL'.trans (mem_aStar_of_aViol hv))
  have hQ0X : tightCore (Q ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  refine ⟨Thm3A.thm3RGroupQuotG_of_belowG hb hlt, typeRHyp_omegaAFam hΩ X,
    subgroupOf_mem_omegaAFam hL'Ω (hcore L' hL'Ω) hL'X,
    not_aEmpty_iff.mpr ⟨J.subgroupOf X, _, _, aViol_omegaAFam_of_le hΩ.hyp hcore hL'Ω hL'X hJX hv⟩,
    tightCore_inf_subgroupOf_mem_omegaAFam hQ hR hRX, fun h => hQB ?_⟩
  have h1 := map_mem_aStar_of_mem_aStar_omegaAFam hΩ.hyp hcore hL hXB hBX hL' h
  rw [Subgroup.map_subgroupOf_eq_of_le hQ0X] at h1
  rw [eq_of_tightCore_inf_le hΩ.hyp hQ (mem_of_mem_aStar hL h1) hR hRX le_rfl]
  exact h1

theorem comm_tightCore_inf_of_sylow_le (hΩ : TypeRHyp Ω) (hcore : ∀ P ∈ Ω, tightCore P = P)
    (hb : Thm3A.Thm3RBelowG (Nat.card G)) {L L' J Q R X : Subgroup G} {zL zJ : G} (hL : L ∈ Ω)
    (hXB : X ≤ conjStab (aStar Ω L)) (hBX : ∀ M ∈ aStar Ω L, M ≤ X) (hX : X ≠ ⊤)
    (hL' : L' ∈ aStar Ω L) (hv : AViol Ω L' J zL zJ) (hQ : Q ∈ Ω) (hQB : Q ∉ aStar Ω L)
    (hR : IsSylow2In R Q) (hRX : R ≤ X) :
    ⁅tightCore (Q ⊓ X), L'⁆ ≤
      (oddCoreOf (tightCore (Q ⊓ X)) ⊔ oddCoreOf X) ⊓ (oddCoreOf L' ⊔ oddCoreOf X) := by
  obtain ⟨hQ3, hΦ, hL'Φ, hnA, hQΦ, hQA⟩ :=
    omegaAFam_thm3_data hΩ hcore hb hL hXB hBX hX hL' hv hQ hQB hR hRX
  exact commutator_le_oddCoreOf_sup_inf_of_subgroupOf ((tightCore_le _).trans inf_le_right)
    (hBX _ hL') (Thm3A.thm3R_comm_mod hQ3 hΦ hL'Φ hnA hQΦ hQA Relation.ReflTransGen.refl)

end Close

section Frame

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem comm_locMember_of_sylow_le (hs : FrameStd K z J zJ) {L Q R L' : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hQ : Q ∈ CoreAssembly.conjClass K)
    (hQB : Q ∉ aStar (CoreAssembly.conjClass K) L) (hR : IsSylow2In R Q)
    (hRX : R ≤ conjStab (aStar (CoreAssembly.conjClass K) L))
    (hL' : L' ∈ aStar (CoreAssembly.conjClass K) L) :
    ⁅tightCore (Q ⊓ conjStab (aStar (CoreAssembly.conjClass K) L)), L'⁆ ≤
      (oddCoreOf (tightCore (Q ⊓ conjStab (aStar (CoreAssembly.conjClass K) L))) ⊔
          oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) L))) ⊓
        (oddCoreOf L' ⊔ oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) L))) := by
  obtain ⟨J', zL', zJ', hv⟩ := hs.exists_aViol (mem_of_mem_aStar hL hL')
  exact comm_tightCore_inf_of_sylow_le hs.typeRHyp (fun P hP => hs.tightCore_eq hP) hs.below hL
    le_rfl (fun M hM => le_conjStab_aStar hs.hyp.conjInvariant hL hM) (hs.conjStab_ne_top hL) hL'
    hv hQ hQB hR hRX

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
