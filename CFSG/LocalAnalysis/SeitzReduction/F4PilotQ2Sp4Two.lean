module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2CentralizerTU
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.PresentationLocal (sympFour omegaPerm omegaPerm_injective
  omegaPerm_surjective commutator_sympFour isSimpleGroup_commutator_sympFour
  not_isMulCommutative_commutator_sympFour isPerfect_commutator_sympFour)
open Equiv Equiv.Perm

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem sign_eq_one_of_odd_orderOf {σ : Perm α} (h : Odd (orderOf σ)) : sign σ = 1 := by
  have h1 : sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem closure_odd_eq_alternatingGroup :
    Subgroup.closure {σ : Perm α | Odd (orderOf σ)} = alternatingGroup α := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro σ hσ
    exact mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hσ)
  · rw [← closure_three_cycles_eq_alternating]
    refine Subgroup.closure_mono fun σ hσ => ?_
    show Odd (orderOf σ)
    rw [hσ.orderOf]
    decide

end Perm

theorem closure_odd_sympFour :
    Subgroup.closure {s : sympFour | Odd (orderOf s)} = commutator sympFour := by
  set e : sympFour ≃* Perm (Fin 6) :=
    MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩ with he
  have heω : e.toMonoidHom = omegaPerm := MonoidHom.ext fun _ => rfl
  have hmap : (Subgroup.closure {s : sympFour | Odd (orderOf s)}).map e.toMonoidHom =
      alternatingGroup (Fin 6) := by
    rw [MonoidHom.map_closure, ← closure_odd_eq_alternatingGroup]
    congr 1
    ext σ
    constructor
    · rintro ⟨s, hs, rfl⟩
      show Odd (orderOf (e s))
      rw [MulEquiv.orderOf_eq]
      exact hs
    · intro hσ
      refine ⟨e.symm σ, ?_, by simp⟩
      show Odd (orderOf (e.symm σ))
      rw [MulEquiv.orderOf_eq]
      exact hσ
  rw [commutator_sympFour, ← hmap, heω, comap_map_eq_self_of_injective omegaPerm_injective]

section B2


variable {K : Type} [Field K]

theorem factOddB2LeviTwo [Finite K] [CharP K 2] (hK : Nat.card K = 2) : FactOddB2LeviTwo K := by
  have := finite_adjointGroup_F4 (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have E : B2Levi K ≃* sympFour :=
    (b2LeviEquiv K).symm.trans
      ((CFSG.Monster.Existence.Compat.statedProjEquivOfBot (CFSG.Assembly.LowTwoRank.StatedSp 2 K)
        (CFSG.Monster.Existence.Compat.statedScalars_eq_bot hK)).symm.trans
        (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hK))
  set H : Subgroup sympFour := commutator sympFour with hHdef
  have hHperf : ⁅H, H⁆ = H := by
    have h := congrArg (Subgroup.map H.subtype)
      (Group.isPerfect_def.1 isPerfect_commutator_sympFour)
    clear_value H
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hodd : oddB2Levi K = (H.map E.symm.toMonoidHom).map (B2Levi K).subtype := by
    rw [hHdef, ← closure_odd_sympFour, MonoidHom.map_closure, MonoidHom.map_closure, oddB2Levi]
    congr 1
    ext c
    constructor
    · rintro ⟨hcM, hco⟩
      refine ⟨⟨c, hcM⟩, ⟨E ⟨c, hcM⟩, ?_, by simp⟩, rfl⟩
      show Odd (orderOf (E ⟨c, hcM⟩))
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hco
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨(E.symm s).2, ?_⟩
      have hs' : Odd (orderOf s) := hs
      rw [← MulEquiv.orderOf_eq E.symm, ← Subgroup.orderOf_coe] at hs'
      exact hs'
  refine ⟨?_, ?_⟩
  · rw [hodd, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hHperf]
  · have eH : H ≃* oddB2Levi K :=
      (H.equivMapOfInjective _ E.symm.injective).trans
        (((H.map E.symm.toMonoidHom).equivMapOfInjective _ (B2Levi K).subtype_injective).trans
          (MulEquiv.subgroupCongr hodd.symm))
    have : IsSimpleGroup H := isSimpleGroup_commutator_sympFour
    have hnab : ∃ a b : H, a * b ≠ b * a := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact not_isMulCommutative_commutator_sympFour ⟨⟨h⟩⟩
    exact EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv eH
      (EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup hnab)

theorem factF3TUTwo_two [Finite K] [CharP K 2] (hK : Nat.card K = 2) : FactF3TUTwo K :=
  factF3TUTwo_of_factOddB2LeviTwo hK (factOddB2LeviTwo hK)

theorem not_normal_map_oddCore_nonsplit_two_of_Z3 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ3 : FactZ3RootTUTwo K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hX₀ : Nat.card X₀ = 3)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact not_normal_map_oddCore_nonsplit_two hset hK e ht hKt (factF3TUTwo_two hK) hZ3 hXJ₀ hX₀ hX
    hDe

variable (K) in
@[expose] def FactZ3RootSp4Two : Prop :=
  ∀ y : CFSG.Assembly.LowTwoRank.StatedSp 2 K, orderOf y = 3 →
    ∃ H : Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 2 K), IsSpRootSL2 2 K H ∧ y ∈ H

theorem factZ3RootTUTwo_of_sp4 [Finite K] [CharP K 2] (h : FactZ3RootSp4Two K) :
    FactZ3RootTUTwo K := by
  intro Y hY hY3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic Y := isCyclic_of_prime_card hY3
  obtain ⟨⟨y, hyY⟩, hgen⟩ := IsCyclic.exists_generator (α := Y)
  have hy3 : orderOf y = 3 := by
    rw [← Subgroup.orderOf_mk y hyY, orderOf_eq_card_of_forall_mem_zpowers hgen, hY3]
  have hyM : y ∈ levi K .tu := ((closure_le _).2 fun c hc => hc.1) (hY hyY)
  set L := leviModelTU K with hLdef
  have hyE : y ∈ L.E.range := by rw [L.range_eq]; exact hyM
  obtain ⟨y', rfl⟩ := hyE
  have hy'3 : orderOf y' = 3 := by rw [← orderOf_injective L.E L.injective y', hy3]
  obtain ⟨H, hH, hy'H⟩ := h y' hy'3
  refine ⟨H.map L.E, ?_, fun x hx => ?_⟩
  · rw [leviRootSL2s_eq]
    exact (L.mem_rootSL2Set_iff _).2 ⟨H, hH, rfl⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨x, hx⟩)
    have hk' : (L.E y') ^ k = x := by
      have := congrArg Subtype.val hk
      simpa using this
    have hmem : L.E y' ∈ H.map L.E := Subgroup.mem_map_of_mem L.E hy'H
    rw [← hk']
    exact zpow_mem hmem k

theorem not_normal_map_oddCore_nonsplit_two_of_sp4Z3 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ3 : FactZ3RootSp4Two K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hX₀ : Nat.card X₀ = 3)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact not_normal_map_oddCore_nonsplit_two_of_Z3 hset hK e ht hKt (factZ3RootTUTwo_of_sp4 hZ3)
    hXJ₀ hX₀ hX hDe

end B2

end CFSG.SeitzReduction.F4Pilot
