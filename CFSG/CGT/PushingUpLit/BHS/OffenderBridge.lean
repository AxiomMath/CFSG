module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.PushingUpLit.BHS.Offender
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conjAct_apply' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

theorem conjAct_eq_one_iff (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem mem_autOn_iff {V A : Subgroup G} {x : MulAut V} :
    x ∈ autOn A V ↔ ∃ a : Subgroup.normalizer (V : Set G), (a : G) ∈ A ∧ conjAct V a = x :=
  CFSG.Quasithin.AutOn.mem_autOn_iff

theorem autOn_eq_bot_of_le_centralizer {V A : Subgroup G}
    (h : A ≤ Subgroup.centralizer (V : Set G)) : autOn A V = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer h

section Bridge

variable {V A : Subgroup G}

theorem wt_autOn (hV : IsElemAbelian 2 V) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    @wt V (commGroupOfElemAbelian hV) (autOn A V) = wtG V A := by
  unfold wt wtG
  rw [card_autOn_eq_relIndex hA, card_fixV_autOn_eq hV hA]

theorem exists_autOn_eq {B : Subgroup (MulAut V)} (hB : B ≤ autOn A V) :
    ∃ A' : Subgroup G, A' ≤ A ∧ autOn A' V = B := by
  set N := Subgroup.normalizer (V : Set G) with hN
  set K : Subgroup N := B.comap (conjAct V) ⊓ A.subgroupOf N with hK
  refine ⟨K.map N.subtype, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact hk.2
  · have h1 : (K.map N.subtype).subgroupOf N = K :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective K
    unfold autOn
    rw [h1]
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.1
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_autOn_iff.mp (hB hb)
      exact ⟨a, ⟨hb, ha⟩, rfl⟩

theorem conjAct_comm_eq_one_iff (V : Subgroup G) (a b : Subgroup.normalizer (V : Set G)) :
    conjAct V a * conjAct V b = conjAct V b * conjAct V a ↔
      ⁅(a : G), (b : G)⁆ ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : ((⁅a, b⁆ : Subgroup.normalizer (V : Set G)) : G) = ⁅(a : G), (b : G)⁆ := rfl
  rw [← h1, ← conjAct_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]

theorem isOffG_iff_isOff_autOn (hV : IsElemAbelian 2 V) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    IsOffG V A ↔ @IsOff V (commGroupOfElemAbelian hV) (autOn A V) := by
  constructor
  · rintro ⟨-, hne, hcomm, hsq, hw⟩
    refine ⟨le_top, autOn_ne_bot_of_not_le_centralizer hA hne, ⟨?_, ?_⟩, ?_⟩
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := mem_autOn_iff.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_autOn_iff.mp hy
      exact (conjAct_comm_eq_one_iff V a b).mpr (hcomm a ha b hb)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_autOn_iff.mp hx
      rw [← map_pow, conjAct_eq_one_iff]
      exact hsq a ha
    · intro B hB
      obtain ⟨A', hA'A, rfl⟩ := exists_autOn_eq hB
      have h1 := wt_autOn hV (hA'A.trans hA)
      have h2 := wt_autOn hV hA
      have h3 := hw A' hA'A
      unfold wt at h1 h2
      rw [h1, h2]
      exact h3
  · rintro ⟨-, hne, hel, hwt⟩
    refine ⟨hA, fun h => hne (autOn_eq_bot_of_le_centralizer h), fun a ha b hb => ?_,
      fun a ha => ?_, fun B hBA => ?_⟩
    · have hx : conjAct V ⟨a, hA ha⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩
      have hy : conjAct V ⟨b, hA hb⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨b, hA hb⟩, hb, rfl⟩
      exact (conjAct_comm_eq_one_iff V ⟨a, hA ha⟩ ⟨b, hA hb⟩).mp (hel.1 _ hx _ hy)
    · have hx : conjAct V ⟨a, hA ha⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩
      have h1 := hel.2 _ hx
      rw [← map_pow, conjAct_eq_one_iff] at h1
      exact h1
    · have h1 := hwt (autOn B V) (autOn_le_autOn V hBA)
      have h2 := wt_autOn hV (hBA.trans hA)
      have h3 := wt_autOn hV hA
      unfold wt at h2 h3
      rw [h2, h3] at h1
      exact h1

end Bridge

end CFSG.CGT.PushingUpLit.BHS
