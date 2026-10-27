module

public import CFSG.CGT.Timmesfeld75.ConclusionIso
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.CGT.Timmesfeld75.ZStarSmall

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

theorem StrongWC.subgroupOf {G : Type*} [Group G] {T : Subgroup G} (hT : StrongWC T)
    (K : Subgroup G) : StrongWC (T.subgroupOf K) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun t ht ht1 a ha g hg => ?_⟩
  · have := hT.1.1
    infer_instance
  · exact Subtype.ext (hT.1.2 (x : G) (Subgroup.mem_subgroupOf.1 hx))
  · have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    have haT : (a : G) ∈ T := Subgroup.mem_subgroupOf.1 ha
    have hg' : (g : G)⁻¹ * (a : G) * (g : G) ∈ Subgroup.centralizer ({(t : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg t (Set.mem_singleton t))
    exact Subgroup.mem_subgroupOf.2 (hT.2 (t : G) htT ht1' (a : G) haT (g : G) hg')

theorem zStarCase_of_commutative {K : Type*} [Group K] (h : ∀ a b : K, a * b = b * a) :
    ZStarCase K := by
  have : (⊥ : Subgroup K).Normal := inferInstance
  refine zStarCase_of_comm_mem (⊥ : Subgroup K) (by simp) fun a b => ?_
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 (h a b)

theorem four_le_card_of_isElemAbelian {G : Type*} [Group G] {T : Subgroup G}
    (hT : IsElemAbelian 2 T) [Finite T] (hTbot : T ≠ ⊥) (h2 : Nat.card T ≠ 2) :
    4 ≤ Nat.card T := by
  have : Fact (IsPGroup 2 T) := ⟨isPGroup_two_of_isElemAbelian hT⟩
  obtain ⟨n, hn⟩ := (isPGroup_two_of_isElemAbelian hT).exists_card_eq
  rcases n with _ | _ | n
  · exact absurd (Subgroup.card_eq_one.1 (by simpa using hn)) hTbot
  · exact absurd (by simpa using hn) h2
  · rw [hn, pow_add]
    have : 0 < 2 ^ n := by positivity
    omega

theorem lemma25_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hAsc : AschbacherNoPolarInput) (hT : StrongWC T)
    (hK : Subgroup.normalClosure (T : Set G) = ⊤) :
    ZStarCase G ∨ CFSG.BenderSuzuki.IsBenderGroup (G ⧸ Subgroup.center G) := by
  by_cases hnT : ∀ g : G, conjSubgroup g T = T
  · left
    have hTn : T.Normal := ⟨fun x hx g => by
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      have : g * x * g⁻¹ ∈ conjSubgroup g T := by
        rw [mem_conjSubgroup, e]
        exact hx
      rwa [hnT g] at this⟩
    have hTtop : T = ⊤ := by
      rw [← hK]
      exact (Subgroup.normalClosure_eq_self T).symm
    refine zStarCase_of_commutative fun a b => ?_
    have ha : a ∈ T := by rw [hTtop]; trivial
    have hb : b ∈ T := by rw [hTtop]; trivial
    exact elemAbelian_mul_comm hT.1 ha hb
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    refine hnT fun g => ?_
    ext x
    rw [mem_conjSubgroup, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]
      group
    · intro h
      rw [h]
      group
  by_cases h2 : Nat.card T = 2
  · left
    have h := zStarCase_normalClosure_of_card_two hT.isWC h2
    rw [hK] at h
    exact zStarCase_of_mulEquiv Subgroup.topEquiv h
  right
  have h4 : 4 ≤ Nat.card T := four_le_card_of_isElemAbelian hT.1 hTbot h2
  have hcentral : ∀ (P : Subgroup G) (p : ℕ), p.Prime → P.Normal → IsPGroup p P →
      ∀ n ∈ P, ∀ k : G, n * k = k * n := by
    intro P p hp hPn hPp n hn k
    have hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ P, k * n * k⁻¹ ∈ P :=
      fun k _ n hn => hPn.conj_mem n hn k
    have hkK : k ∈ Subgroup.normalClosure (T : Set G) := by rw [hK]; trivial
    have hPK : P ≤ Subgroup.normalClosure (T : Set G) := by rw [hK]; exact le_top
    by_cases hp2 : p = 2
    · subst hp2
      exact twoCore_le_center hT hnT P hPK hNn hPp n hn k hkK
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨m, hm⟩ := hPp.exists_card_eq
      have hodd : Odd (Nat.card P) := by
        rw [hm]
        exact (hp.odd_of_ne_two hp2).pow
      exact oddCore_le_center hT.isWC h4 P hPK hNn hodd n hn k hkK
  refine isBenderGroup_quotient_center hAsc hT hK hnT hTbot ?_ ?_ ?_
  · intro t ht ht1
    obtain ⟨k, -, hk⟩ := not_central_of_mem_T hT hnT ht ht1
    exact ⟨k, hk⟩
  · intro x hx y hy hz
    exact commute_of_comm_central hT hnT hx hy fun k _ => hz k
  · exact solvable_normal_bot_of_pSubgroups_central fun p hp P hPn hPp =>
      fun n hn => Subgroup.mem_center_iff.2 fun k => (hcentral P p hp hPn hPp n hn k).symm

theorem lemma25 {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hAsc : AschbacherNoPolarInput) (hT : StrongWC T) :
    ZStarCase ↥(Subgroup.normalClosure (T : Set G)) ∨
      CFSG.BenderSuzuki.IsBenderGroup
        (↥(Subgroup.normalClosure (T : Set G)) ⧸
          Subgroup.center ↥(Subgroup.normalClosure (T : Set G))) :=
  lemma25_top hAsc (hT.subgroupOf _) (normalClosure_subgroupOf_eq_top hT.isWC)

end CFSG.CGT.Timmesfeld75
