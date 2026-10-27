module

public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentSubnormal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_self_of_isTwoComponent' {P : Subgroup G}
    (hP : TwoComponents.IsTwoComponent P) : ⁅P, P⁆ = P :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr (TwoComponents.perfect hP))

theorem commutator_self_of_isTwoComponent {C P : Subgroup G} (hPC : P ≤ C)
    (hP : TwoComponents.IsTwoComponent (P.subgroupOf C)) : ⁅P, P⁆ = P := by
  have h2 := commutator_self_of_isTwoComponent' hP
  have h3 := congrArg (Subgroup.map C.subtype) h2
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPC] at h3

theorem ne_bot_of_isTwoComponent [Finite G] {C P : Subgroup G}
    (hP : TwoComponents.IsTwoComponent (P.subgroupOf C)) : P ≠ ⊥ := by
  intro h
  have hn := TwoComponents.nontrivial hP
  have hbot : P.subgroupOf C = ⊥ := by rw [h, Subgroup.bot_subgroupOf]
  rw [hbot] at hn
  exact ((Subgroup.nontrivial_iff_ne_bot (⊥ : Subgroup ↥C)).mp hn) rfl

section TwoFactors

variable {X Y P : Subgroup G} {t : G}

theorem le_or_le_of_isTwoComponent_centralizer [Finite G] (hXY : ⁅X, Y⁆ = ⊥)
    (hX : t ∈ normalizer (X : Set G)) (hY : t ∈ normalizer (Y : Set G))
    (hPC : P ≤ centralizer ({t} : Set G))
    (hP : TwoComponents.IsTwoComponent (P.subgroupOf (centralizer ({t} : Set G))))
    (hPXY : P ≤ X ⊔ Y) : P ≤ X ∨ P ≤ Y := by
  classical
  set C := centralizer ({t} : Set G) with hCdef
  set A := X ⊓ C with hAdef
  set B := Y ⊓ C with hBdef
  set D := A ⊔ B with hDdef
  have hperf : ⁅P, P⁆ = P := commutator_self_of_isTwoComponent hPC hP
  have hPD : P ≤ D := by
    rw [← hperf]
    exact (commutator_mono (le_inf hPXY hPC) (le_inf hPXY hPC)).trans
      (commutator_fixed_sup_le hXY hX hY)
  have hDC : D ≤ C := sup_le inf_le_right inf_le_right
  have hABC : ⁅A, B⁆ = ⊥ := eq_bot_iff.2 (hXY ▸ commutator_mono inf_le_left inf_le_left)
  have hnormA : D ≤ normalizer (A : Set G) :=
    sup_le le_normalizer ((commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact hABC)).trans (centralizer_le_normalizer _))
  have hnormB : D ≤ normalizer (B : Set G) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.1 hABC).trans (centralizer_le_normalizer _))
      le_normalizer
  have hPD' : TwoComponents.IsTwoComponent (P.subgroupOf D) :=
    TwoComponentTransport.restrict_nested P D C hPD hDC hP
  have hAn : (A.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hnormA
  have hBn : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hnormB
  have hsubn : ∀ N : Subgroup ↥D, N.Normal → CFSG.Open.IsSubnormal N ⊤ := fun N hN =>
    Components.chain_of_mathlib_subnormal
      (Subgroup.IsSubnormal.step N ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  have hle : ∀ N : Subgroup G, P.subgroupOf D ≤ N.subgroupOf D → P ≤ N := fun N h j hj =>
    Subgroup.mem_subgroupOf.1
      (h (Subgroup.mem_subgroupOf.2 hj : (⟨j, hPD hj⟩ : D) ∈ P.subgroupOf D))
  rcases TwoComponentSubnormal.contains_or_normalizes_core (P.subgroupOf D) (A.subgroupOf D) hPD'
      (hsubn _ hAn) with h1 | ⟨h1n, h1c⟩
  · exact Or.inl ((hle A h1).trans inf_le_left)
  rcases TwoComponentSubnormal.contains_or_normalizes_core (P.subgroupOf D) (B.subgroupOf D) hPD'
      (hsubn _ hBn) with h2 | ⟨h2n, h2c⟩
  · exact Or.inr ((hle B h2).trans inf_le_left)
  exfalso
  set P' : Subgroup ↥D := P.subgroupOf D with hP'def
  set R : Subgroup ↥D := (CFSG.Open.componentClassificationOddCore ↥P').map P'.subtype with hRdef
  have hdecomp : ∀ q : ↥D, ∃ a ∈ A, ∃ b ∈ B, a * b = (q : G) := by
    intro q
    have hq : (q : G) ∈ ((A ⊔ B : Subgroup G) : Set G) := q.2
    rw [coe_sup_of_commutator_eq_bot hABC] at hq
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hq
    exact ⟨a, ha, b, hb, hab⟩
  have hAD : A ≤ D := le_sup_left
  have hBD : B ≤ D := le_sup_right
  have hPnorm : P'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine top_unique fun q _ => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp q
    have hq : q = (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩ := Subtype.ext hab.symm
    rw [hq]
    exact Subgroup.mul_mem _ (h1n (Subgroup.mem_subgroupOf.2 ha))
      (h2n (Subgroup.mem_subgroupOf.2 hb))
  have hRn : R.Normal := by
    have : (pPrimeCore 2 ↥P').Characteristic := inferInstance
    have h := (CatalogueBAlternating.primeCore_two_eq_oddCore ↥P')
    rw [hRdef, ← h]
    exact ConjAct.normal_of_characteristic_of_normal
  have hPR : P' ≤ R := by
    have hperf' : ⁅P', P'⁆ = P' := commutator_self_of_isTwoComponent' hPD'
    rw [← hperf', Subgroup.commutator_le]
    intro p hp q hq
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp q
    have hq' : q = (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩ := Subtype.ext hab.symm
    have hpa : ⁅p, (⟨a, hAD ha⟩ : ↥D)⁆ ∈ R :=
      h1c (Subgroup.commutator_mem_commutator hp (Subgroup.mem_subgroupOf.2 ha))
    have hpb : ⁅p, (⟨b, hBD hb⟩ : ↥D)⁆ ∈ R :=
      h2c (Subgroup.commutator_mem_commutator hp (Subgroup.mem_subgroupOf.2 hb))
    have hid : ⁅p, (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩⁆ =
        ⁅p, (⟨a, hAD ha⟩ : ↥D)⁆ * ((⟨a, hAD ha⟩ : ↥D) * ⁅p, (⟨b, hBD hb⟩ : ↥D)⁆ *
          (⟨a, hAD ha⟩ : ↥D)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hq', hid]
    exact R.mul_mem hpa (hRn.conj_mem _ hpb _)
  have hRodd : Odd (Nat.card R) := by
    rw [hRdef, Subgroup.card_map_of_injective P'.subtype_injective]
    exact OddCore.odd_card ↥P'
  have hP'odd : Odd (Nat.card P') := Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hPR)
  have hsolv : Group.IsSolvable ↥P' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hP'odd
  have hnt := TwoComponents.nontrivial hPD'
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P'
  rw [TwoComponents.perfect hPD'] at h1
  exact lt_irrefl _ h1

end TwoFactors

section Orbit

variable {H : Type*} [Group H] [Finite H] {t : H}

theorem exists_mem_le_sup_conjSub_of_isTwoComponent (ht : orderOf t = 2) {P : Subgroup H}
    (hPC : P ≤ centralizer ({t} : Set H))
    (hP : TwoComponents.IsTwoComponent (P.subgroupOf (centralizer ({t} : Set H)))) :
    ∀ (n : ℕ) (S : Finset (Subgroup H)), S.card ≤ n → (∀ K ∈ S, CFSG.IsComponent K) →
      (∀ K ∈ S, conjSub t⁻¹ K ∈ S) → P ≤ sSup (S : Set (Subgroup H)) →
        ∃ L ∈ S, P ≤ L ⊔ conjSub t⁻¹ L := by
  classical
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hPne : P ≠ ⊥ := ne_bot_of_isTwoComponent hP
  have hJne : ∀ S : Finset (Subgroup H), P ≤ sSup (S : Set (Subgroup H)) → S.Nonempty := by
    intro S hS
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, sSup_empty, le_bot_iff] at hS
    exact hPne hS
  intro n
  induction n with
  | zero =>
    intro S hS _ _ hJS
    obtain ⟨K, hK⟩ := hJne S hJS
    exact absurd (Finset.card_pos.2 ⟨K, hK⟩) (by omega)
  | succ n ih =>
    intro S hS hcomp hinv hJS
    obtain ⟨L, hL⟩ := hJne S hJS
    set O : Finset (Subgroup H) := {L, conjSub t⁻¹ L} with hOdef
    have hOS : O ⊆ S := by
      intro K hK
      rw [Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl
      · exact hL
      · exact hinv L hL
    set S' := S \ O with hS'def
    have hS'inv : ∀ K ∈ S', conjSub t⁻¹ K ∈ S' := by
      intro K hK
      rw [Finset.mem_sdiff] at hK ⊢
      refine ⟨hinv K hK.1, fun hKO => hK.2 ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton] at hKO ⊢
      rcases hKO with h | h
      · right
        rw [← h, conjSub_conjSub_of_inv_eq ht']
      · left
        have := congrArg (conjSub t⁻¹) h
        rwa [conjSub_conjSub_of_inv_eq ht', conjSub_conjSub_of_inv_eq ht'] at this
    have hS'card : S'.card ≤ n := by
      have : S'.card < S.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hOS ⟨L, Finset.mem_insert_self _ _⟩)
      omega
    have hsplit : sSup (S : Set (Subgroup H)) =
        (L ⊔ conjSub t⁻¹ L) ⊔ sSup (S' : Set (Subgroup H)) := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hOS]
      rw [Finset.coe_union, sSup_union, hOdef, Finset.coe_pair, sSup_pair]
    have hLcomp := hcomp L hL
    have hLtcomp := hcomp _ (hinv L hL)
    have hcommute : ⁅L ⊔ conjSub t⁻¹ L, sSup (S' : Set (Subgroup H))⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
      refine sSup_le fun K hK => ?_
      have hK' := Finset.mem_sdiff.1 hK
      have hKL : K ≠ L := fun h => hK'.2 (by rw [h]; exact Finset.mem_insert_self _ _)
      have hKLt : K ≠ conjSub t⁻¹ L := fun h => hK'.2 (by
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hc1 := (CFSG.LocalCores.distinct_components_commute (hcomp K hK'.1) hLcomp).resolve_left
        hKL
      have hc2 := (CFSG.LocalCores.distinct_components_commute (hcomp K hK'.1)
        hLtcomp).resolve_left hKLt
      rw [← le_centralizer_iff]
      exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc1))
        (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc2))
    have hnormO : t ∈ normalizer ((L ⊔ conjSub t⁻¹ L : Subgroup H) : Set H) := by
      refine mem_normalizer_of_conjSub_inv_le ht' ?_
      rw [conjSub, Subgroup.map_sup]
      refine sup_le le_sup_right ?_
      change conjSub t⁻¹ (conjSub t⁻¹ L) ≤ _
      rw [conjSub_conjSub_of_inv_eq ht']
      exact le_sup_left
    have hnormS' : t ∈ normalizer ((sSup (S' : Set (Subgroup H)) : Subgroup H) : Set H) :=
      mem_normalizer_of_conjSub_inv_le ht' (conjSub_sSup_le fun K hK => hS'inv K hK)
    rw [hsplit] at hJS
    rcases le_or_le_of_isTwoComponent_centralizer hcommute hnormO hnormS' hPC hP hJS with h | h
    · exact ⟨L, hL, h⟩
    · obtain ⟨L', hL', hJL'⟩ := ih S' hS'card (fun K hK => hcomp K (Finset.mem_sdiff.1 hK).1)
        hS'inv h
      exact ⟨L', (Finset.mem_sdiff.1 hL').1, hJL'⟩

theorem exists_component_orbit_location (ht : orderOf t = 2) {P : Subgroup H}
    (hPC : P ≤ centralizer ({t} : Set H))
    (hP : TwoComponents.IsTwoComponent (P.subgroupOf (centralizer ({t} : Set H))))
    (hPE : P ≤ CFSG.layer H) :
    ∃ L : Subgroup H, CFSG.IsComponent L ∧
      ((conjSub t⁻¹ L = L ∧ P ≤ L) ∨
        (conjSub t⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥, P ≤ (swapDiag hAB).range)) := by
  classical
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have : Finite (Subgroup H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  set S₀ : Finset (Subgroup H) := (Set.toFinite {K : Subgroup H | CFSG.IsComponent K}).toFinset
    with hS₀
  have hmem : ∀ K, K ∈ S₀ ↔ CFSG.IsComponent K := fun K => by
    rw [hS₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsSup : sSup (S₀ : Set (Subgroup H)) = CFSG.layer H := by
    rw [hS₀, Set.Finite.coe_toFinset]
    rfl
  obtain ⟨L, hL, hPL⟩ := exists_mem_le_sup_conjSub_of_isTwoComponent ht hPC hP S₀.card S₀ le_rfl
    (fun K hK => (hmem K).1 hK) (fun K hK => (hmem _).2 (isComponent_conjSub ((hmem K).1 hK) _))
    (hsSup ▸ hPE)
  have hLc := (hmem L).1 hL
  refine ⟨L, hLc, ?_⟩
  by_cases hLt : conjSub t⁻¹ L = L
  · refine Or.inl ⟨hLt, ?_⟩
    rw [hLt, sup_idem] at hPL
    exact hPL
  · have hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥ := commutator_conjSub_eq_bot hLc hLt
    refine Or.inr ⟨hLt, hAB, ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
      swapped_quasisimple_fixed_central_product ht (assembly_isQuasisimple_of_isComponent hLc) hAB
    have hperf : ⁅P, P⁆ = P := commutator_self_of_isTwoComponent hPC hP
    rw [← hder, ← hperf]
    exact commutator_mono (le_inf hPL hPC) (le_inf hPL hPC)

end Orbit

end CFSG.GH74.GLS.TwoThin
