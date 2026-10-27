module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Iface
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono
public import CFSG.Monster.CodeAut.Bridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

@[expose, instance_reducible] def actC : MulAction AutPerm C where
  smul p a := permC p a
  one_smul a := permC_one a
  mul_smul p q a := permC_mul p q a

attribute [local instance] actC

@[expose] def stabC (d : C) : Subgroup AutPerm := MulAction.stabilizer AutPerm d

theorem mem_stabC {d : C} {p : AutPerm} : p ∈ stabC d ↔ permC p d = d := Iff.rfl

abbrev signSub : Subgroup latticeO := monoSub ⊥

theorem mem_signSub {g : latticeO} : g ∈ signSub ↔ ∃ a : C, g = gO a := by
  constructor
  · rintro ⟨a, p, hp, rfl⟩
    rw [Subgroup.mem_bot.1 hp, PO_one, mul_one]
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact gO_mem_monoSub ⊥ a

theorem natCard_signSub : Nat.card signSub = 2 ^ 12 := by
  rw [card_monoSub, Subgroup.card_bot, mul_one]

theorem hammingNorm_permC (p : AutPerm) (a : C) :
    hammingNorm (permC p a : Fin 24 → ZMod 2) = hammingNorm (a : Fin 24 → ZMod 2) :=
  hammingNorm_comp_perm _ _

@[expose] def wt12 : Set C := {a | hammingNorm (a : Fin 24 → ZMod 2) = 12}

theorem ncard_wt12 : wt12.ncard = 2576 := by
  rw [← Nat.card_coe_set_eq, ← wtCount_twelve, ← card_filter_wt 12, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1, Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, a.1.2⟩, a.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.1 (Finset.mem_filter.1 x.2).1).2⟩,
        (Finset.mem_filter.1 x.2).2⟩
      left_inv := fun a => rfl
      right_inv := fun x => rfl }

theorem wt12_finite : wt12.Finite := Set.toFinite _

theorem monoSub_stabC_le (d : C) : monoSub (stabC d) ≤ Subgroup.centralizer {gO d} := by
  rintro _ ⟨a, p, hp, rfl⟩
  exact (mul_PO_mem_centralizer_gO_iff a p d).2 hp

theorem orbit_dod₂_subset : MulAction.orbit AutPerm dod₂ ⊆ wt12 := by
  rintro _ ⟨p, rfl⟩
  show hammingNorm (permC p dod₂ : Fin 24 → ZMod 2) = 12
  rw [hammingNorm_permC]
  exact hammingNorm_dod₂

theorem card_stabC_dod₂ (hcls : Co0ClassData) :
    Nat.card (stabC dod₂) = 95040 ∧ MulAction.orbit AutPerm dod₂ = wt12 := by
  have hfin : Finite (Subgroup.centralizer {gO dod₂}) :=
    Nat.finite_of_card_ne_zero (by rw [hcls.card_cent_dod]; decide)
  have hle : Nat.card (stabC dod₂) ≤ 95040 := by
    have h1 := Subgroup.card_le_of_le (monoSub_stabC_le dod₂)
    rw [card_monoSub, hcls.card_cent_dod] at h1
    norm_num [co0C3] at h1
    omega
  have hidx : (stabC dod₂).index = (MulAction.orbit AutPerm dod₂).ncard :=
    MulAction.index_stabilizer AutPerm dod₂
  have hmul := (stabC dod₂).index_mul_card
  rw [card_AutPerm, hidx] at hmul
  have hcardle : (MulAction.orbit AutPerm dod₂).ncard ≤ 2576 := by
    rw [← ncard_wt12]
    exact Set.ncard_le_ncard orbit_dod₂_subset wt12_finite
  have hge : 95040 ≤ Nat.card (stabC dod₂) := by
    by_contra hlt
    have := Nat.mul_le_mul hcardle (Nat.le_of_lt_succ (not_le.1 hlt))
    omega
  have hcard : Nat.card (stabC dod₂) = 95040 := le_antisymm hle hge
  have horb : (MulAction.orbit AutPerm dod₂).ncard = 2576 := by
    rw [hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 95040) (by rw [hmul])
  exact ⟨hcard, Set.eq_of_subset_of_ncard_le orbit_dod₂_subset (by rw [ncard_wt12, horb])
    wt12_finite⟩

theorem exists_permC_dod₂ (hcls : Co0ClassData) {a : C}
    (ha : hammingNorm (a : Fin 24 → ZMod 2) = 12) : ∃ p : AutPerm, permC p dod₂ = a := by
  have h := (card_stabC_dod₂ hcls).2
  have ha' : a ∈ wt12 := ha
  rw [← h] at ha'
  obtain ⟨p, hp⟩ := ha'
  exact ⟨p, hp⟩

theorem centralizer_gO_dod₂ (hcls : Co0ClassData) :
    Subgroup.centralizer {gO dod₂} = monoSub (stabC dod₂) := by
  have hfin : Finite (Subgroup.centralizer {gO dod₂}) :=
    Nat.finite_of_card_ne_zero (by rw [hcls.card_cent_dod]; decide)
  symm
  refine Subgroup.eq_of_le_of_card_ge (monoSub_stabC_le dod₂) ?_
  rw [card_monoSub, (card_stabC_dod₂ hcls).1, hcls.card_cent_dod]
  norm_num [co0C3]

private theorem separate : ∀ i j : Fin 24, i ≠ j → ∃ k : Fin 12, B k i ≠ B k j := by decide

theorem permC_eq_one_of_forall {p : AutPerm} (h : ∀ b : C, permC p b = b) : p = 1 := by
  refine Subtype.ext (Equiv.ext fun i => ?_)
  by_contra hne
  obtain ⟨k, hk⟩ := separate i ((p : Equiv.Perm (Fin 24)) i) (fun e => hne e.symm)
  have h1 := congrFun (congrArg Subtype.val (h ⟨B k, B_mem_C k⟩)) ((p : Equiv.Perm (Fin 24)) i)
  rw [coe_permC, permWord_apply] at h1
  exact hk h1

theorem centralizer_signSub_le (hcls : Co0ClassData) :
    Subgroup.centralizer (signSub : Set latticeO) ≤ signSub := by
  intro g hg
  have h1 : g ∈ Subgroup.centralizer {gO dod₂} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg (gO dod₂) (gO_mem_monoSub ⊥ dod₂)).symm
  rw [centralizer_gO_dod₂ hcls] at h1
  obtain ⟨a, p, hp, rfl⟩ := h1
  have hp1 : p = 1 := permC_eq_one_of_forall fun b =>
    (mul_PO_mem_centralizer_gO_iff a p b).1 (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg (gO b) (gO_mem_monoSub ⊥ b)).symm)
  subst hp1
  exact mem_signSub.2 ⟨a, by rw [PO_one, mul_one]⟩

end CFSG.EvenSporadicStandard.TwoCo1
