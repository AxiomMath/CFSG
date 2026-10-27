module

import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Goldschmidt.Steps.G37QuotL
public import CFSG.Goldschmidt.Steps.G37QuotX

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Goldschmidt.SStarTransport
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

theorem normalClosureIn_top_eq {M : Type*} [Group M] (B : Subgroup M) :
    normalClosureIn ⊤ B = Subgroup.normalClosure (B : Set M) := by
  rw [normalClosureIn, Subgroup.map_normalClosure _ _ (fun x => ⟨⟨x, trivial⟩, rfl⟩)]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem barOf_normalClosureIn {G : Type*} [Group G] (H A : Subgroup G) :
    barOf H (normalClosureIn H A) = normalClosureIn ⊤ (barOf H A) := by
  rw [normalClosureIn_top_eq, barOf, normalClosureIn,
    show ((Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H)).map
        H.subtype).subgroupOf H = Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H)
      from Subgroup.comap_map_eq_self_of_injective H.subtype_injective _,
    Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  rfl

variable {G : Type} [Group G] [Finite G] {H A : Subgroup G} {a : G} {X : Subgroup G}

theorem bar_setting (hS : IsSStarIn H A) (hE : CFSG.Open.IsElemAbelian 2 A) (haA : a ∈ A)
    (hXH : X ≤ H)
    (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) :
    goldschmidtOddCore (H ⧸ goldschmidtOddCore H) = ⊥ ∧
      IsSStarIn (⊤ : Subgroup (H ⧸ goldschmidtOddCore H)) (barOf H A) ∧
      CFSG.Open.IsElemAbelian 2 (barOf H A) ∧
      QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, hS.1 haA⟩ ∈ barOf H A ∧
      Subgroup.centralizer ({QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, hS.1 haA⟩} :
          Set (H ⧸ goldschmidtOddCore H)) ≤
        Subgroup.normalizer (barOf H X : Set (H ⧸ goldschmidtOddCore H)) ∧
      barOf H X = componentLayerOf (barOf H X) ⊔
        oddCoreOf (CFSG.fittingSubgroupOf (barOf H X)) :=
  ⟨CFSG.Goldschmidt.goldschmidtOddCore_quotient_eq_bot H, isSStarIn_barOf hS,
    isElemAbelian_map (isElemAbelian_subgroupOf hE H) _, ⟨⟨a, hS.1 haA⟩, haA, rfl⟩,
    centralizer_le_normalizer_barOf hXH (hS.1 haA) (hE.2 a haA) hXa, barOf_eq_sup hXH hXE⟩

omit [Finite G] in
theorem oddCoreOf_le_normalizer_normalClosureIn (H A : Subgroup G) :
    oddCoreOf H ≤ Subgroup.normalizer (normalClosureIn H A : Set G) :=
  (Subgroup.map_subtype_le _).trans
    (le_normalizer_map_subtype (Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H)))

theorem le_normalClosureIn_of_barOf_le {L : Subgroup G} (hLH : L ≤ H) (hLp : Group.IsPerfect L)
    (h : barOf H L ≤ normalClosureIn ⊤ (barOf H A)) : L ≤ normalClosureIn H A := by
  have hKH : normalClosureIn H A ≤ H := Subgroup.map_subtype_le _
  rw [← barOf_normalClosureIn, ← le_preOf_iff hLH, preOf_barOf' hKH, sup_comm] at h
  exact le_of_perfect_of_le_sup hLp h (oddCoreOf_le_normalizer_normalClosureIn H A)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Completion.odd_card_oddCoreOf H))

theorem eq_of_barOf_eq {K L : Subgroup G} (hKL : K ≤ L) (hKH : K ≤ H) (hLH : L ≤ H)
    (hLp : Group.IsPerfect L) (hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G))
    (h : barOf H L = barOf H K) : K = L := by
  refine le_antisymm hKL ?_
  have h1 : L ≤ oddCoreOf H ⊔ K := by
    rw [sup_comm, ← preOf_barOf' hKH, le_preOf_iff hLH, h]
  refine le_of_perfect_of_le_sup hLp h1 (fun o ho => ?_)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Completion.odd_card_oddCoreOf H))
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hKO hk) o ho).symm

omit [Finite G] in
theorem commutator_le_oddCoreOf_of_barOf_le {K : Subgroup G} (hKH : K ≤ H) (haH : a ∈ H)
    (h : barOf H K ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, haH⟩} : Set (H ⧸ goldschmidtOddCore H))) :
    ⁅K, Subgroup.zpowers a⁆ ≤ oddCoreOf H := by
  have hZH : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr haH
  rw [← barOf_eq_bot_iff ((Subgroup.commutator_mono hKH hZH).trans (commutator_self_le H)),
    barOf_commutator hKH hZH, barOf_zpowers haH]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rw [CFSG.Walter.centralizer_zpowers_eq']
  exact h

variable (h31 : S_G31) (h32Q : S_G32Q) (h33 : S_G33) (h34 : S_G34) (h35 : S_G35)
  (hS : IsSStarIn H A) (hE : CFSG.Open.IsElemAbelian 2 A) (haA : a ∈ A) (hXH : X ≤ H)
  (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
  (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X))

include h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE

theorem part3a : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ normalClosureIn H A ⊔ oddCoreOf H := by
  obtain ⟨hO, hS', hE', hā, hXba, hXbE⟩ := bar_setting hS hE haA hXH hXa hXE
  have hYH : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ H := (oddFit_le X).trans hXH
  have h1 := (barOf_oddFit_le hXH).trans
    (core_oddFit_le h31 h32Q h33 h34 h35 hO hS' hE' hā hXba hXbE)
  have hKH : normalClosureIn H A ≤ H := Subgroup.map_subtype_le _
  rwa [← barOf_normalClosureIn, ← le_preOf_iff hYH, preOf_barOf' hKH] at h1

theorem part3b {L : Subgroup G} (hL : IsComponentOf L H)
    (hYL : ¬ oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set G)) :
    L ≤ normalClosureIn H A ∧ IsGoldL2 L ∧
      oddCoreOf (CFSG.fittingSubgroupOf X) ≤ L ⊔ H ⊓ Subgroup.centralizer (L : Set G) ∧
      (∃ y ∈ oddCoreOf (CFSG.fittingSubgroupOf X), oddCoreOf (CFSG.fittingSubgroupOf X) ≤
        Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set G)) ∧
      ⁅A ⊓ L, oddCoreOf (CFSG.fittingSubgroupOf X)⁆ ≠ ⊥ := by
  obtain ⟨hO, hS', hE', hā, hXba, hXbE⟩ := bar_setting hS hE haA hXH hXa hXE
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYH : Y ≤ H := (oddFit_le X).trans hXH
  have hLH : L ≤ H := hL.1
  have hLO := le_centralizer_oddCoreOf_of_isComponentOf hL
  have hLp : Group.IsPerfect L := Group.isPerfect_def.mpr hL.2.2.2.1
  have hOL : oddCoreOf H ≤ H ⊓ Subgroup.centralizer (L : Set G) :=
    le_inf (Subgroup.map_subtype_le _) (Subgroup.le_centralizer_iff.mp hLO)
  have hC := preOf_centralizer_barOf hLH hLp hLO
  have hYbL : ¬ barOf H Y ≤ Subgroup.centralizer (barOf H L : Set _) := by
    intro h
    apply hYL
    have h1 : ⁅Y, L⁆ ≤ oddCoreOf H := by
      rw [← barOf_eq_bot_iff ((Subgroup.commutator_mono hYH hLH).trans (commutator_self_le H)),
        barOf_commutator hYH hLH]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
    have h2 : ⁅⁅L, Y⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L Y, eq_bot_iff]
      calc ⁅⁅Y, L⁆, L⁆ ≤ ⁅oddCoreOf H, L⁆ := Subgroup.commutator_mono h1 le_rfl
        _ = ⊥ := by
            rw [Subgroup.commutator_comm]
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLO
        _ ≤ ⊥ := le_rfl
    have h3 := CFSG.LocalCores.perfect_double_commutator hLp h2
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  obtain ⟨hLK, hL2, hYLC, ⟨yb, hyb, hYyb⟩, hAL⟩ :=
    core_oddFit_component h31 h32Q h33 h34 h35 hO hS' hE' hā hXba hXbE
      (isComponentOf_barOf_top hL) (barOf_oddFit_le hXH) hYbL
  refine ⟨le_normalClosureIn_of_barOf_le hLH hLp hLK, isGoldL2_of_barOf hLH hLp hLO hL2, ?_, ?_,
    ?_⟩
  · have e : barOf H L ⊔ Subgroup.centralizer (barOf H L : Set _) =
        barOf H (L ⊔ H ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [barOf_sup hLH inf_le_left, ← hC, barOf_preOf]
    have h1 := (le_preOf_iff hYH).mpr hYLC
    rw [e, preOf_barOf' (sup_le hLH inf_le_left)] at h1
    exact h1.trans (sup_le le_rfl (hOL.trans le_sup_right))
  · obtain ⟨y, hy, rfl⟩ := hyb
    refine ⟨y, hy, ?_⟩
    have hyH : Subgroup.zpowers (y : G) ≤ H := Subgroup.zpowers_le.mpr y.2
    have e : Subgroup.zpowers (QuotientGroup.mk' (goldschmidtOddCore H) y) ⊔
        Subgroup.centralizer (barOf H L : Set _) =
        barOf H (Subgroup.zpowers (y : G) ⊔ H ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [barOf_sup hyH inf_le_left, barOf_zpowers y.2, ← hC, barOf_preOf]
    have h1 := (le_preOf_iff hYH).mpr hYyb
    rw [e, preOf_barOf' (sup_le hyH inf_le_left)] at h1
    exact h1.trans (sup_le (sup_le_sup_left inf_le_right _)
      ((Subgroup.le_centralizer_iff.mp hLO).trans le_sup_right))
  · intro h
    apply hAL
    have hA2 : IsPGroup 2 A := by
      obtain ⟨-, -, T, hT, hAT, -⟩ := hS
      exact hT.2.1.to_le hAT
    rw [eq_bot_iff]
    calc ⁅barOf H A ⊓ barOf H L, barOf H Y⁆ ≤ ⁅barOf H (A ⊓ L), barOf H Y⁆ :=
          Subgroup.commutator_mono (barOf_inf_le hA2 hLH hLO) le_rfl
      _ = barOf H ⁅A ⊓ L, Y⁆ := (barOf_commutator (inf_le_right.trans hLH) hYH).symm
      _ ≤ ⊥ := by rw [h]; exact (barOf_eq_bot_iff bot_le).mpr bot_le |>.le

theorem part2 {K : Subgroup G} (hK : IsComponentOf K X)
    (hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G)) :
    ∃ L : Subgroup G, IsComponentOf L H ∧ K ≤ L ∧ (K = L ∨ (IsGoldL2 K ∧
      K ≤ Subgroup.centralizer ({a} : Set G) ∧ IsGoldJR L ∧ L ≤ normalClosureIn H A)) := by
  obtain ⟨hO, hS', hE', hā, hXba, hXbE⟩ := bar_setting hS hE haA hXH hXa hXE
  have haH : a ∈ H := hS.1 haA
  have hKH : K ≤ H := hK.1.trans hXH
  have hKp : Group.IsPerfect K := Group.isPerfect_def.mpr hK.2.2.2.1
  have hKb := isComponentOf_barOf' hXH hK
  obtain ⟨Lb, hLb, hKLb, hcase⟩ :=
    core_component h31 h32Q h33 h34 h35 hO hS' hE' hā hXba hXbE hKb
  have hcov : Lb ≤ barOf H (H ⊓ Subgroup.centralizer (oddCoreOf H : Set G)) := by
    have hN : (⊤ : Subgroup (H ⧸ goldschmidtOddCore H)) ≤ Subgroup.normalizer
        (barOf H (H ⊓ Subgroup.centralizer (oddCoreOf H : Set G)) : Set _) := by
      rw [← barOf_self]
      refine (barOf_mono (le_inf le_rfl fun h hh => ?_)).trans (barOf_normalizer_le inf_le_left)
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hh, normalizer_le_normalizer_centralizer'
          (oddCoreOf H) (Completion.le_normalizer_oddCoreOf H hh)⟩
    rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot hLb le_top hN with h | h
    · exact h
    · exfalso
      apply not_le_centralizer_self hKb.2.2
      have h1 : barOf H K ≤ Subgroup.centralizer (Lb : Set _) := by
        have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          ((Subgroup.commutator_comm _ _).trans h)
        exact (barOf_mono (le_inf hKH hKO)).trans h2
      exact h1.trans (Subgroup.centralizer_le hKLb)
  obtain ⟨L, hL, hLLb, hlift⟩ := exists_isComponentOf_of_le_barOf hLb hcov
  have hKL : K ≤ L := hlift K hKH hKO hKp hKLb
  have hLp : Group.IsPerfect L := Group.isPerfect_def.mpr hL.2.2.2.1
  refine ⟨L, hL, hKL, ?_⟩
  rcases hcase with heq | ⟨hL2, hKa, hJR, hLK⟩
  · exact Or.inl (eq_of_barOf_eq hKL hKH hL.1 hLp hKO (hLLb.trans heq.symm))
  · refine Or.inr ⟨isGoldL2_of_barOf hKH hKp hKO hL2, ?_,
      isGoldJR_of_barOf hL.1 hLp (le_centralizer_oddCoreOf_of_isComponentOf hL) (hLLb ▸ hJR),
      le_normalClosureIn_of_barOf_le hL.1 hLp (hLLb ▸ hLK)⟩
    have h1 := commutator_le_oddCoreOf_of_barOf_le hKH haH hKa
    have haX : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr (hXa (Subgroup.mem_inf.mpr
        ⟨haH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩))
    rcases le_commutator_or_commutator_eq_bot hK haX with h | h
    · exact absurd (h.trans h1) (not_le_oddCoreOf hK.2.2)
    · rw [← CFSG.Walter.centralizer_zpowers_eq']
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

end CFSG.Goldschmidt.G37
