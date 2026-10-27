module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts
open scoped commutatorElement MatrixGroups

variable {X : Type} [Group X]

theorem inf_oddIn_le [Finite X] {S K : Subgroup X} (hSK : S ≤ K) : S ⊓ oddIn K ≤ oddIn S := by
  rintro x ⟨hxS, hxO⟩
  set N := (oddIn K).subgroupOf S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hN, mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hoe⟩ := hn
    refine ⟨⟨g, hSK g.2⟩ * o * (⟨g, hSK g.2⟩)⁻¹,
      (pPrimeCore_normal (G := ↥K) (p := 2)).conj_mem o ho _, ?_⟩
    have hoe' : (o : X) = n := hoe
    simp [hoe']
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card (oddIn K) := by
      have e1 : Nat.card N = Nat.card (N.map S.subtype) :=
        (Subgroup.card_map_of_injective S.subtype_injective).symm
      rw [e1]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h2 : Nat.card (oddIn K) = Nat.card (pPrimeCore 2 ↥K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact ⟨⟨x, hxS⟩, CFSG.GroupTheory.le_pPrimeCore_of_normal hNn hcop
    (mem_subgroupOf.mpr hxO), rfl⟩

theorem not_commutator_le_oddIn [Finite X] {α : X} {E S K : Subgroup X} (hSK : S ≤ K)
    (h : ActsProperly α E S ((pPrimeCore 2 ↥S).map S.subtype)) : ¬ ⁅K, E⁆ ≤ oddIn K := by
  intro hle
  obtain ⟨hN, -, e, he, a, ha, hae⟩ := h
  have heN : e ∈ normalizer (S : Set X) :=
    (mem_inf.mp (hN (subset_closure (Set.mem_insert_of_mem _ he)))).1
  have hcS : ⁅a, e⁆ ∈ S := by
    rw [commutatorElement_def]
    have h1 : e * a⁻¹ * e⁻¹ ∈ S := (mem_normalizer_iff.mp heN _).mp (S.inv_mem ha)
    have h2 : a * e * a⁻¹ * e⁻¹ = a * (e * a⁻¹ * e⁻¹) := by group
    rw [h2]
    exact S.mul_mem ha h1
  exact hae (inf_oddIn_le hSK ⟨hcS, hle (commutator_mem_commutator (hSK ha) he)⟩)

theorem gsUnbalancingTriple_of_actsProperly [Finite X] {α γ : X} (hα : orderOf α = 2)
    (hγ : orderOf γ = 2) (hαγ : α * γ = γ * α) {K S E : Subgroup X}
    (hKγ : K ≤ centralizer ({γ} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({γ} : Set X)))) (hSK : S ≤ K)
    (hEα : E ≤ oddCentralizerCore α) (hEγ : E ≤ centralizer ({γ} : Set X))
    (h : ActsProperly α E S ((pPrimeCore 2 ↥S).map S.subtype)) :
    GSUnbalancingTriple γ α K :=
  GrS5.gsUnbalancingTriple_of_not_le solomonCommutingCoreInput hα hγ hαγ hKγ hK
    (le_inf hEα hEγ) (not_commutator_le_oddIn hSK h)

theorem eq_bot_of_perfect_of_le {G : Type*} [Group G] {P C : Subgroup G} (hPC : P ≤ C)
    (hperf : ⁅P, P⁆ = P) (hC : Group.IsSolvable C) : P = ⊥ := by
  have hsol : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPC)
      (Subgroup.inclusion_injective hPC)
  have hp : Group.IsPerfect P := (Subgroup.isPerfect_iff (H := P)).2 hperf
  obtain ⟨n, hn⟩ := (Group.isSolvable_def P).1 hsol
  have htop : ∀ m, derivedSeries P m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hp.commutator_eq_top]
  rw [htop n] at hn
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : P) ∈ (⊤ : Subgroup P) := mem_top _
  rw [hn, mem_bot] at h1
  exact mem_bot.mpr (congrArg Subtype.val h1)

variable {K S : Subgroup X} (hSK : S ≤ K)

@[expose] noncomputable def imageHom {Y : Type*} [Group Y] (q : Jhat K →* Y) : ↥S →* Y :=
  (q.comp (jq K)).comp (Subgroup.inclusion hSK)

theorem imageHom_apply {Y : Type*} [Group Y] (q : Jhat K →* Y) (s : ↥S) :
    imageHom hSK q s = q (jq K ⟨s, hSK s.2⟩) := rfl

theorem commutator_range_imageHom {Y : Type*} [Group Y] (q : Jhat K →* Y)
    (hS : ⁅S, S⁆ = S) : ⁅(imageHom hSK q).range, (imageHom hSK q).range⁆ =
      (imageHom hSK q).range := by
  have hp : Group.IsPerfect ↥S := (Subgroup.isPerfect_iff (H := S)).2 hS
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    hp.commutator_eq_top]

theorem card_sl2_dvd [Finite X] {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (e : ↥S ⧸ pPrimeCore 2 ↥S ≃* SL(2, F)) {Y : Type*} [Group Y] (q : Jhat K →* Y)
    (hqker : q.ker = center (Jhat K)) :
    Nat.card SL(2, F) ∣ 2 * Nat.card (imageHom hSK q).range := by
  set ψ := imageHom hSK q with hψ
  set π : ↥S →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥S)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : ∀ s, s ∈ pPrimeCore 2 ↥S → π s = 1 := by
    intro s hs
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff s).mpr hs,
      map_one]
  have hcomm : ∀ s ∈ ψ.ker, ∀ t : ↥S, π s * π t = π t * π s := by
    intro s hs t
    have hsz : jq K ⟨s, hSK s.2⟩ ∈ center (Jhat K) := by
      rw [← hqker]
      exact hs
    have h1 : jq K ⟨((s * t * s⁻¹ * t⁻¹ : ↥S) : X), hSK (s * t * s⁻¹ * t⁻¹).2⟩ = 1 := by
      have e1 : (⟨((s * t * s⁻¹ * t⁻¹ : ↥S) : X), hSK (s * t * s⁻¹ * t⁻¹).2⟩ : K) =
          ⟨s, hSK s.2⟩ * ⟨t, hSK t.2⟩ * (⟨s, hSK s.2⟩)⁻¹ * (⟨t, hSK t.2⟩)⁻¹ := rfl
      have hc := mem_center_iff.mp hsz (jq K ⟨t, hSK t.2⟩)
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    have h2 := (mem_oddIn_iff (hSK (s * t * s⁻¹ * t⁻¹).2)).mpr h1
    obtain ⟨o, ho, hoe⟩ := inf_oddIn_le hSK ⟨(s * t * s⁻¹ * t⁻¹).2, h2⟩
    have hoe' : o = s * t * s⁻¹ * t⁻¹ := Subtype.ext hoe
    have h3 := hπker _ (hoe' ▸ ho)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc π s * π t = π s * π t * (π s)⁻¹ * (π t)⁻¹ * (π t * π s) := by group
      _ = π t * π s := by rw [h3, one_mul]
  set M := ψ.ker.map π with hM
  have hMc : M ≤ center SL(2, F) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨t, rfl⟩ := hπs g
    exact (hcomm s hs t).symm
  have : M.Normal := CFSG.GroupTheory.normal_of_le_center hMc
  have hM2 : Nat.card M ∣ 2 := by
    have h := Subgroup.card_dvd_of_le hMc
    rwa [CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2] at h
  set g := (QuotientGroup.mk' M).comp π with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective M).comp hπs
  have hker : ψ.ker ≤ g.ker := by
    intro s hs
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨s, hs, rfl⟩
  have hidx := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hgs,
    Subgroup.card_top] at hidx
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M, mul_comm 2]
  exact mul_dvd_mul hidx hM2

theorem card_range_dvd_card_sl2 [Finite X] {F : Type*} [Field F]
    (e : ↥S ⧸ pPrimeCore 2 ↥S ≃* SL(2, F))
    {Y : Type*} [Group Y] (q : Jhat K →* Y) [IsSimpleGroup (imageHom hSK q).range]
    (heven : 2 ∣ Nat.card (imageHom hSK q).range) :
    Nat.card (imageHom hSK q).range ∣ Nat.card SL(2, F) := by
  set ψ := imageHom hSK q with hψ
  have hN : ((pPrimeCore 2 ↥S).map ψ.rangeRestrict).Normal :=
    (pPrimeCore_normal (G := ↥S) (p := 2)).map _ ψ.rangeRestrict_surjective
  have hle : pPrimeCore 2 ↥S ≤ ψ.ker := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 ↥S).map ψ.rangeRestrict)
      with h | h
    · rw [← MonoidHom.ker_rangeRestrict, ← Subgroup.map_eq_bot_iff]
      exact h
    · exfalso
      have hd : Nat.card ψ.range ∣ Nat.card (pPrimeCore 2 ↥S) := by
        have := Subgroup.card_map_dvd (pPrimeCore 2 ↥S) ψ.rangeRestrict
        rwa [h, Subgroup.card_top] at this
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥S)) := pPrimeCore_coprime_card
      exact absurd (hcop.eq_one_of_dvd (heven.trans hd)) (by norm_num)
  have hidx := Subgroup.index_dvd_of_le hle
  rwa [Subgroup.index_ker, Subgroup.index, Nat.card_congr e.toEquiv] at hidx

end CFSG.ComponentClassification.TBLit.L34P
