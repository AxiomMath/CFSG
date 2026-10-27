module

public import CFSG.LargeExtraspecial.S97RBasic
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S9SevenD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

theorem exists_mul_of_mem_sup_normalizer {H : Type*} [Group H] {P N : Subgroup H}
    (hPN : P ≤ normalizer (N : Set H)) {y : H} (hy : y ∈ P ⊔ N) :
    ∃ a ∈ P, ∃ b ∈ N, a * b = y := by
  have hy' : y ∈ ((P ⊔ N : Subgroup H) : Set H) := hy
  rw [coe_mul_of_left_le_normalizer_right P N hPN] at hy'
  exact Set.mem_mul.mp hy'

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O}

variable (S g k) in
noncomputable abbrev X97 : Subgroup S.O := S.Lbar g ⊔ S.Lbar ((k : G) * g)

variable (S g k) in
noncomputable abbrev Q97 : Type := ↥(X97 S g k) ⧸ CFSG.pCore 2 ↥(X97 S g k)

variable (S g k) in
@[expose] noncomputable def Tj97 (j : G) : Subgroup (Q97 S g k) :=
  ((S.Lbar j).subgroupOf (X97 S g k)).map (QuotientGroup.mk' _)

theorem Q97.eq_bot_of_normal (N : Subgroup (Q97 S g k)) (hN : N.Normal) (hP : IsPGroup 2 N) :
    N = ⊥ :=
  eq_bot_of_normal_isPGroup_quotient_pCore N hN hP

theorem Tj97_sup : Tj97 S g k g ⊔ Tj97 S g k ((k : G) * g) = ⊤ := by
  rw [Tj97, Tj97, ← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

namespace Hyp97

variable (X : Hyp97 S g k O)
include X

theorem subgroupOf_eq_pCore : O.subgroupOf (X97 S g k) = CFSG.pCore 2 ↥(X97 S g k) := by
  refine le_antisymm ?_ ?_
  · have hN : (O.subgroupOf (X97 S g k)).Normal := ⟨fun n hn x => by
      rw [mem_subgroupOf] at hn ⊢
      exact X.normal x x.2 n hn⟩
    have hP : IsPGroup 2 (O.subgroupOf (X97 S g k)) :=
      X.isPGroup.of_equiv (subgroupOfEquivOfLe X.le).symm
    exact le_sSup ⟨hN, hP⟩
  · intro y hy
    rw [mem_subgroupOf]
    have hle : (CFSG.pCore 2 ↥(X97 S g k)).map (X97 S g k).subtype ≤ O := by
      refine X.max _ (map_subtype_le _) ?_ (CFSG.pCore_isPGroup.map _)
      rintro x hx _ ⟨o, ho, rfl⟩
      exact ⟨⟨x, hx⟩ * o * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem o ho ⟨x, hx⟩, rfl⟩
    exact hle ⟨y, hy, rfl⟩

theorem mk_eq_mk_iff {x y : X97 S g k} :
    (x : Q97 S g k) = (y : Q97 S g k) ↔ ((x⁻¹ * y : X97 S g k) : S.O) ∈ O := by
  rw [QuotientGroup.eq, ← X.subgroupOf_eq_pCore, mem_subgroupOf]

theorem mk_eq_one_iff {x : X97 S g k} : (x : Q97 S g k) = 1 ↔ (x : S.O) ∈ O := by
  rw [QuotientGroup.eq_one_iff, ← X.subgroupOf_eq_pCore, mem_subgroupOf]

theorem le_normalizer_O : X97 S g k ≤ normalizer (O : Set S.O) := fun _ hx =>
  mem_normalizer_of_forall_conj X.normal hx

theorem mk_mem_Tj97_iff {j : G} (hj : S.Lbar j ≤ X97 S g k) (x : X97 S g k) :
    (x : Q97 S g k) ∈ Tj97 S g k j ↔ (x : S.O) ∈ S.Lbar j ⊔ O := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 := (X.mk_eq_mk_iff).mp hyx
    have e : (x : S.O) = (y : S.O) * ((y⁻¹ * x : X97 S g k) : S.O) := by simp
    rw [e]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hy)) (mem_sup_right h1)
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_mul_of_mem_sup_normalizer (hj.trans X.le_normalizer_O) hx
    refine ⟨⟨a, hj ha⟩, mem_subgroupOf.mpr ha, (X.mk_eq_mk_iff).mpr ?_⟩
    have e : ((((⟨a, hj ha⟩ : X97 S g k))⁻¹ * x : X97 S g k) : S.O) = b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hab]
      group
    rw [e]
    exact hb

theorem mk_mem_conj_Tj97_iff {j : G} (hj : S.Lbar j ≤ X97 S g k) (x u : X97 S g k) :
    (u : Q97 S g k) ∈ conjSubgroup (x : Q97 S g k) (Tj97 S g k j) ↔
      (u : S.O) ∈ (S.Lbar j ⊔ O).map (MulAut.conj (x : S.O)).toMonoidHom := by
  have e0 : (x : Q97 S g k)⁻¹ * (u : Q97 S g k) * (x : Q97 S g k) =
      ((x⁻¹ * u * x : X97 S g k) : Q97 S g k) := rfl
  rw [mem_conjSubgroup, e0, X.mk_mem_Tj97_iff hj]
  constructor
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩
  · rintro ⟨v, hv, hvu⟩
    have e : ((x⁻¹ * u * x : X97 S g k) : S.O) = v := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hvu]
      simp [mul_assoc]
    rw [e]
    exact hv

variable {j : G} (hj : S.Lbar j ≤ X97 S g k)
include hj

theorem Tj97_isTI
    (hTI : ∀ x ∈ X97 S g k, (S.Lbar j ⊔ O).map (MulAut.conj x).toMonoidHom = S.Lbar j ⊔ O ∨
      (S.Lbar j ⊔ O).map (MulAut.conj x).toMonoidHom ⊓ (S.Lbar j ⊔ O) ≤ O) (y : Q97 S g k) :
    Tj97 S g k j ⊓ conjSubgroup y (Tj97 S g k j) = ⊥ ∨
      Tj97 S g k j ⊓ conjSubgroup y (Tj97 S g k j) = Tj97 S g k j := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    rcases hTI x x.2 with h | h
    · refine Or.inr (inf_eq_left.mpr fun w hw => ?_)
      induction w using QuotientGroup.induction_on with
      | H u =>
        rw [X.mk_mem_conj_Tj97_iff hj, h, ← X.mk_mem_Tj97_iff hj]
        exact hw
    · refine Or.inl (eq_bot_iff.mpr ?_)
      intro w hw
      induction w using QuotientGroup.induction_on with
      | H u =>
        have hw1 := (mem_inf.mp hw).1
        have hw2 := (mem_inf.mp hw).2
        rw [X.mk_mem_Tj97_iff hj] at hw1
        rw [X.mk_mem_conj_Tj97_iff hj] at hw2
        exact (mem_bot).mpr ((X.mk_eq_one_iff).mpr (h ⟨hw2, hw1⟩))

end Hyp97

end CFSG.LargeExtraspecial.S9
