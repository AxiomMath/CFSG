module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainLift
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.OmegaPilot (OmegaOvergroup)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem mem_center_of_mem_oddCore_of_commute_nonsplit_E7_of_finite
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hKc
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E7_of_finite hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact mem_center_of_mem_oddCore_of_commute_E7 hL htC ht hK e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd le_rfl hX htX

theorem nonempty_spinGroup_mulEquiv_centralizerPerfectCore_nonsplit_E7_of_finite
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : IsComponent Kb)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kb)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : OmegaOvergroup Kb (Kb.normalizerMonoidHom ⟨_, hsN⟩) 6 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (spinGroup (quadPlus 6 F) ≃* centralizerPerfectCore X) := by
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hKc
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  exact nonempty_spinGroup_mulEquiv_centralizerPerfectCore_of_omegaOvergroup ht htX hDt hf
    (neighbour_standard_E7_nonsplit_of_finite hL htC ht hK hKc e hAJ hA hcyc hX htX hDe).2.1
    (mem_center_of_mem_oddCore_of_commute_nonsplit_E7_of_finite hL htC ht hK hKc e hAJ hA hcyc hX
      htX) hKb hDK hsN hov

theorem nonempty_levi_high_mulEquiv_centralizerPerfectCore_nonsplit_E7
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : IsComponent Kb)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kb)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : OmegaOvergroup Kb (Kb.normalizerMonoidHom ⟨_, hsN⟩) 6 f) (K₂ : Type) [Field K₂]
    [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) :
    Nonempty (E7Neighbour.high.levi K₂ ≃* centralizerPerfectCore X) := by
  obtain ⟨F, _, _, _, hF, ⟨Ψ⟩⟩ :=
    nonempty_spinGroup_mulEquiv_centralizerPerfectCore_nonsplit_E7_of_finite hL htC ht hK hKc e
      hAJ hA hcyc hX htX hDe hKb hDK hsN hov
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card F = Fintype.card K₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK₂]
  exact ⟨((MulEquiv.subgroupCongr (E7Neighbour.levi_high K₂)).trans
    (perpLeviRingEquivE7 (FiniteField.ringEquivOfCardEq hc)).symm).trans
      ((spinEquivPerpLevi F).symm.trans Ψ)⟩

theorem perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_E7 [Finite K] [CharP K 2]
    (hset : StandardSetting G L) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) = D := by
  obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E7_of_finite hAJ hA hcyc
  have hLX := inf_centralizer_nonsplit_E7_of_finite (G := G) (L := L) e hAJ hA hcyc
  have hDq : CFSG.IsQuasisimple D := by
    rw [hDe]
    exact isQuasisimple_map_perpLevi_E7 e
  subst hX hDe
  have hDperf := isPerfect_iff.mp hDq.1
  have hDH := map_perpLevi_le_centralizer_E7_of_charTwo (G := G) (L := L) e
    (Subgroup.map_mono (Subgroup.map_mono hAJ))
  have hDE := CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  have hDt : ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (centralizerPerfectCore ((A.map e.symm.toMonoidHom).map L.subtype) ⊓
    centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hPL : P ≤ L :=
    std_perfect_le hset (isSolvable_outer_of_mulEquiv_E7_of_finite e) htC ht hP hPt
  have hPX : P ≤ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX := le_inf hPL hPX
  rw [hLX] at hPLX
  have hXD := le_centralizer_iff.mp (F4Pilot.map_map_symm_le_centralizer (G := G) (L := L) e hAD)
  have hXX := F4Pilot.map_map_symm_le_centralizer (G := G) (L := L) e
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc)
  have hXsolv : Group.IsSolvable ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end CFSG.SeitzReduction.E7Pilot
