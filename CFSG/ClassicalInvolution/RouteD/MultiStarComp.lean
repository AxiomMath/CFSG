module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.RouteD.AllA1
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryThree

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have := hsimple
  have hNmap : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hNmap.eq_bot_or_eq_top with h | h
  · right
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hperf' : (⊤ : Subgroup Q) ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ := by
      rw [← _root_.commutator_def, hperf]
    exact eq_top_iff.mpr (le_of_perfect_of_le_sup_center le_rfl hperf' hsup.ge)

theorem isQuasisimple_range {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) : CFSG.Open.IsQuasisimple (D.hom i).range := by
  have hK : CFSG.Open.IsQuasisimple
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag i)
      (D.admissible i)).1
  have hq := CFSG.ComponentClassification.Quasisimple.central_quotient hK (D.hom i).ker
    (D.ker_le_center i)
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (QuotientGroup.quotientKerEquivRange (D.hom i)).symm hq


theorem conjSub_le_centralizer_of_mem {x g : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    {N : Subgroup G} (hN : N ≤ Subgroup.centralizer ({x} : Set G)) :
    conjSub g N ≤ Subgroup.centralizer ({x} : Set G) := by
  intro n hn
  rw [mem_conjSub_iff] at hn
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hN hn)
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h4 : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [← h2]
      _ = x * g⁻¹ := by group
  calc n * x = g * (g⁻¹ * n * g) * (g⁻¹ * x) := by group
    _ = g * (g⁻¹ * n * g) * (x * g⁻¹) := by rw [h4]
    _ = g * ((g⁻¹ * n * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
    _ = (g * x) * (g⁻¹ * n * g) * g⁻¹ := by group
    _ = (x * g) * (g⁻¹ * n * g) * g⁻¹ := by rw [h2]
    _ = x * n := by group

section Blocks

variable {Ω : Set (Subgroup G)} {x : G}

theorem conjSub_mem_compMembers (hΩ : InClass p f Ω)
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card} {N : Subgroup G}
    (hN : N ∈ Gaps.compMembers Ω x D i) (y : ↥(locLayer Ω x)) :
    conjSub (y : G) N ∈ Gaps.compMembers Ω x D i := by
  obtain ⟨⟨hNΩ, hNC⟩, hNi⟩ := hN
  refine ⟨⟨hΩ.conjInvariant _ _ hNΩ,
    conjSub_le_centralizer_of_mem (centralizingLayer_le_centralizer Ω {x} y.2) hNC⟩, ?_⟩
  rw [Gaps.locImg_conjSub_layer]
  intro u hu
  obtain ⟨a, ha, rfl⟩ := hu
  exact (D.range_normal i).conj_mem _ (hNi ha) _

theorem range_le_iSup_locImg [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card} {a : Subgroup G}
    (ha : a ∈ Gaps.compMembers Ω x D i) :
    (D.hom i).range ≤ ⨆ N : ↥(Gaps.compMembers Ω x D i), locImg Ω x N.1 := by
  set H : Subgroup (locQuot Ω x) := ⨆ N : ↥(Gaps.compMembers Ω x D i), locImg Ω x N.1 with hHdef
  have hHle : H ≤ (D.hom i).range := iSup_le fun N => N.2.2
  have hnorm : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    induction hn using Subgroup.iSup_induction' with
    | hp N u hu =>
      have hmem : conjSub (y : G) N.1 ∈ Gaps.compMembers Ω x D i :=
        conjSub_mem_compMembers hΩ N.2 y
      have h1 : Gaps.locMk Ω x y * u * (Gaps.locMk Ω x y)⁻¹ ∈
          locImg Ω x (conjSub (y : G) N.1) := by
        rw [Gaps.locImg_conjSub_layer]
        exact ⟨u, hu, rfl⟩
      exact (le_iSup (fun N : ↥(Gaps.compMembers Ω x D i) => locImg Ω x N.1)
        ⟨conjSub (y : G) N.1, hmem⟩) h1
    | h1 => simp
    | hmul u v _ _ hu hv =>
      have e : (y : locQuot Ω x) * (u * v) * (y : locQuot Ω x)⁻¹ =
          ((y : locQuot Ω x) * u * (y : locQuot Ω x)⁻¹) *
            ((y : locQuot Ω x) * v * (y : locQuot Ω x)⁻¹) := by group
      rw [e]
      exact H.mul_mem hu hv
  have hsub : (H.subgroupOf (D.hom i).range).Normal := hnorm.subgroupOf _
  rcases normal_eq_top_or_le_center (isQuasisimple_range D i) hsub with h | h
  · exact Subgroup.subgroupOf_eq_top.mp h
  · exfalso
    refine Gaps.locImg_not_commutative hΩ hex ha.1 fun u hu v hv => ?_
    have hu' : (⟨u, ha.2 hu⟩ : ↥(D.hom i).range) ∈ H.subgroupOf (D.hom i).range :=
      Subgroup.mem_subgroupOf.mpr ((le_iSup (fun N : ↥(Gaps.compMembers Ω x D i) =>
        locImg Ω x N.1) ⟨a, ha⟩) hu)
    have := Subgroup.mem_center_iff.mp (h hu') ⟨v, ha.2 hv⟩
    exact congrArg Subtype.val this.symm

theorem commutes_iSup_iSup {X : Type*} [Group X] {ι κ : Type*} {S : ι → Subgroup X}
    {T : κ → Subgroup X} (h : ∀ i j, Commutes (S i) (T j)) :
    Commutes (⨆ i, S i) (⨆ j, T j) := by
  intro u hu v hv
  induction hu using Subgroup.iSup_induction' with
  | hp i u hu =>
    induction hv using Subgroup.iSup_induction' with
    | hp j v hv => exact h i j u hu v hv
    | h1 => simp
    | hmul v₁ v₂ _ _ h₁ h₂ => rw [← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]
  | h1 => simp
  | hmul u₁ u₂ _ _ h₁ h₂ => rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]

theorem linked_of_mem_compMembers [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card} {a b : Subgroup G}
    (ha : a ∈ Gaps.compMembers Ω x D i) (hb : b ∈ Gaps.compMembers Ω x D i) :
    Linked Ω x a b := by
  by_contra hnb
  let E : Set (Subgroup G) := {N | N ∈ Gaps.compMembers Ω x D i ∧ Linked Ω x a N}
  let E' : Set (Subgroup G) := {N | N ∈ Gaps.compMembers Ω x D i ∧ ¬ Linked Ω x a N}
  let H₁ : Subgroup (locQuot Ω x) := ⨆ N : ↥E, locImg Ω x N.1
  let H₂ : Subgroup (locQuot Ω x) := ⨆ N : ↥E', locImg Ω x N.1
  have hcomm : Commutes H₁ H₂ := by
    refine commutes_iSup_iSup fun N N' => commutes_locImg_of_commutes ?_
    by_contra hc
    exact N'.2.2 (N.2.2.trans (Linked.single ⟨N.2.1.1, N'.2.1.1, hc⟩))
  have hcover : (D.hom i).range ≤ H₁ ⊔ H₂ := by
    refine (range_le_iSup_locImg hΩ hex ha).trans (iSup_le fun N => ?_)
    by_cases hN : Linked Ω x a N.1
    · exact (le_iSup (fun N : ↥E => locImg Ω x N.1) ⟨N.1, N.2, hN⟩).trans le_sup_left
    · exact (le_iSup (fun N : ↥E' => locImg Ω x N.1) ⟨N.1, N.2, hN⟩).trans le_sup_right
  have hH₁le : H₁ ≤ (D.hom i).range := iSup_le fun N => N.2.1.2
  have hnormlz : H₁ ⊔ H₂ ≤ Subgroup.normalizer (H₁ : Set (locQuot Ω x)) := by
    refine sup_le Subgroup.le_normalizer fun w hw => ?_
    rw [Subgroup.mem_normalizer_iff]
    have hfix : ∀ w ∈ H₂, ∀ h ∈ H₁, w * h * w⁻¹ = h := by
      intro w hw h hh
      have := hcomm h hh w hw
      calc w * h * w⁻¹ = (h * w) * w⁻¹ := by rw [this]
        _ = h := by group
    intro n
    constructor
    · intro hn
      rw [hfix w hw n hn]
      exact hn
    · intro hn
      have h2 := hfix w⁻¹ (H₂.inv_mem hw) _ hn
      have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hn
  have hsub : (H₁.subgroupOf (D.hom i).range).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hnormlz (hcover g.2)) n).mp hn
    exact this
  have haE : a ∈ E := ⟨ha, Relation.ReflTransGen.refl⟩
  have haH₁ : locImg Ω x a ≤ H₁ := le_iSup (fun N : ↥E => locImg Ω x N.1) ⟨a, haE⟩
  have hrange : (D.hom i).range ≤ H₁ := by
    rcases normal_eq_top_or_le_center (isQuasisimple_range D i) hsub with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exfalso
      refine Gaps.locImg_not_commutative hΩ hex ha.1 fun u hu v hv => ?_
      have hu' : (⟨u, ha.2 hu⟩ : ↥(D.hom i).range) ∈ H₁.subgroupOf (D.hom i).range :=
        Subgroup.mem_subgroupOf.mpr (haH₁ hu)
      have := Subgroup.mem_center_iff.mp (h hu') ⟨v, ha.2 hv⟩
      exact congrArg Subtype.val this.symm
  have hbE' : b ∈ E' := ⟨hb, hnb⟩
  have hbH₂ : locImg Ω x b ≤ H₂ := le_iSup (fun N : ↥E' => locImg Ω x N.1) ⟨b, hbE'⟩
  refine Gaps.locImg_not_commutative hΩ hex hb.1 fun u hu v hv => ?_
  exact hcomm u (hrange (hb.2 hu)) v (hbH₂ hv)

theorem exists_mem_compMembers [Finite G]
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} (i : Fin D.card) :
    ∃ N, N ∈ Gaps.compMembers Ω x D i := by
  obtain ⟨R, -, hR⟩ := D.meets i
  obtain ⟨N, hN, hNR⟩ := mem_locFamily_iff.mp hR
  exact ⟨N, hN, hNR ▸ Subgroup.map_le_range _ _⟩

theorem NonClassical.Linked.mem_centralizingMembers {A B : Subgroup G} (h : Linked Ω x A B)
    (hA : A ∈ centralizingMembers Ω {x}) : B ∈ centralizingMembers Ω {x} := by
  induction h with
  | refl => exact hA
  | tail _ hbc _ => exact hbc.2.1

theorem linked_iff_mem_compMembers [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} {a B : Subgroup G} (ha : a ∈ Gaps.compMembers Ω x D i) :
    Linked Ω x a B ↔ B ∈ Gaps.compMembers Ω x D i :=
  ⟨fun h => ⟨h.mem_centralizingMembers ha.1, h.le_range hΩ hP1 D ha.2⟩,
    fun h => linked_of_mem_compMembers hΩ hex ha h⟩

theorem eq_of_mem_compMembers_a1 [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} (hi : IsA1Comp D i) {N N' : Subgroup G}
    (hN : N ∈ Gaps.compMembers Ω x D i) (hN' : N' ∈ Gaps.compMembers Ω x D i) : N = N' := by
  have e1 : locImg Ω x N = (D.hom i).range :=
    Subgroup.eq_of_le_of_card_ge hN.2 (by
      rw [card_locImg hΩ hex hN.1]
      exact card_range_le_of_psl_two D i hi.1 hi.2)
  have e2 : locImg Ω x N' = (D.hom i).range :=
    Subgroup.eq_of_le_of_card_ge hN'.2 (by
      rw [card_locImg hΩ hex hN'.1]
      exact card_range_le_of_psl_two D i hi.1 hi.2)
  exact locImg_injOn hΩ hP1 hN.1 hN'.1 (e1.trans e2.symm)

theorem exists_ne_of_not_isA1Comp [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}
    (hi : ¬ IsA1Comp D i) : ∃ N N' : Subgroup G, N ∈ Gaps.compMembers Ω x D i ∧
      N' ∈ Gaps.compMembers Ω x D i ∧ N ≠ N' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_mem_compMembers (D := D) i
  have hrange : (D.hom i).range ≤ locImg Ω x a := by
    refine (range_le_iSup_locImg hΩ hex ha).trans (iSup_le fun N => ?_)
    have : N.1 = a := hcon N.1 a N.2 ha
    rw [this]
  obtain ⟨R, hRmem, hRfund, hRimg⟩ := Gaps.exists_corr_left hΩ hex D ha
  have hK : CFSG.Open.IsQuasisimple
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag i)
      (D.admissible i)).1
  have hperf : (⊤ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K), ⊤⁆ := by
    rw [← _root_.commutator_def, hK.1]
  have hsup : (⊤ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K) ≤
      R ⊔ (D.hom i).ker := by
    intro k _
    have hk : D.hom i k ∈ R.map (D.hom i) := hRimg ▸ hrange ⟨k, rfl⟩
    obtain ⟨r, hr, hrk⟩ := hk
    have hmem : r⁻¹ * k ∈ (D.hom i).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrk, inv_mul_cancel]
    have : k = r * (r⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hmem)
  have hRtop : R = ⊤ :=
    eq_top_iff.mpr (le_of_perfect_of_le_sup_center (D.ker_le_center i) hperf hsup)
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag (D.tag i) := by
    have := D.isFundTag i
    generalize D.tag i = t at this ⊢
    cases t <;> trivial
  exact (CFSG.ClassicalInvolution.ModelFacts.fundamentalIsWhole (D.tag i) (D.rank i) p (D.exp i)
    Fact.out hfund' (D.admissible i)).2 (fun h => hi h) R hRfund hRtop

end Blocks

end CFSG.ClassicalInvolution.RouteD
