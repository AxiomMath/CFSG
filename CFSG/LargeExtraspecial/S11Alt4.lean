module

public import CFSG.LargeExtraspecial.S11Alt4A
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open
open scoped MatrixGroups commutatorElement

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {k : G} {t : S.O} {τ : S.M}
  {u : G}

section Conf

variable (hy : Hyp S k) (K : Conf S k t τ u) (hCE : CentralExtInput.{u_G})
include hy K hCE

theorem Conf.pCoreOf_Rbar_eq (h3 : 3 ≤ finrank (ZMod 2) (Vt S k t)) :
    CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar) = (Nbar S k t).subgroupOf S.Mbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hnab⟩ := (S45Q.hyp45Q hy.hyp4 hy.cons).lin K.mem_Lbar K.lin h3
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    have h1 := pCore_le_ker_of_simple hy.hyp4 hs hnab hp
    rw [MonoidHom.mem_ker, S7.resRM_eq_one_iff] at h1
    exact mem_subgroupOf.mpr h1
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 (fun x hx =>
      mem_subgroupOf.mpr (Nbar_le_Rbar (mem_subgroupOf.mp hx))) ⟨fun n hn r => ?_⟩ ?_
    · rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
      have hrR : (((r : (Rbar S k t).subgroupOf S.Mbar) : S.Mbar) : S.O) ∈ Rbar S k t :=
        mem_subgroupOf.mp r.2
      obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.mp
        ((r : (Rbar S k t).subgroupOf S.Mbar) : S.Mbar).2
      have hκt : S.ρ κ * t = t * S.ρ κ := by
        rw [hκ]
        exact commute_of_mem_Rbar hy.hyp4.conj_mem hrR
      have h1 := conj_mem_Nbar hy.hyp4.conj_mem hκt hn
      rw [hκ] at h1
      exact h1
    · have h1 : IsPGroup 2 (Nbar S k t) := (isPGroup_Lbar u).to_le (K.timmesfeld_11_5 hy hCE)
      exact h1.comap_of_injective S.Mbar.subtype S.Mbar.subtype_injective

omit hy hCE in
theorem Conf.sq_comm_mem_zpowers_of_mem_Lbar {x : S.O} (hx : x ∈ S.Lbar u) :
    x ^ 2 ∈ zpowers t ∧ ∀ y ∈ S.Lbar u, ⁅x, y⁆ ∈ zpowers t := by
  have hτ : (S.conjBy u).z = (τ : G) := K.conj_eq.symm
  have hρτ : S.ρ τ = t := K.rho_eq
  obtain ⟨x₀, hx₀, rfl⟩ := (S4.mem_Lbar S).mp hx
  have hx₀u : (x₀ : G) ∈ (S.conjBy u).QG := (mem_inf.mp hx₀).1
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← map_pow]
    rcases (S.conjBy u).sq_eq_one_or_z hx₀u with h | h
    · rw [show x₀ ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact h), map_one]
      exact one_mem _
    · rw [show x₀ ^ 2 = τ from Subtype.ext (by rw [Subgroup.coe_pow, h, hτ]), hρτ]
      exact mem_zpowers t
  · obtain ⟨y₀, hy₀, rfl⟩ := (S4.mem_Lbar S).mp hy
    have hy₀u : (y₀ : G) ∈ (S.conjBy u).QG := (mem_inf.mp hy₀).1
    rw [← map_commutatorElement]
    rcases (S.conjBy u).commutator_eq_one_or_z hx₀u hy₀u with h | h
    · rw [show ⁅x₀, y₀⁆ = 1 from Subtype.ext (by rw [commutatorElement_def]; exact h), map_one]
      exact one_mem _
    · rw [show ⁅x₀, y₀⁆ = τ from Subtype.ext (by rw [commutatorElement_def]; exact h.trans hτ),
        hρτ]
      exact mem_zpowers t

theorem Conf.frattini_le_zpowers (h3 : 3 ≤ finrank (ZMod 2) (Vt S k t)) :
    (frattini (CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar))).map
      (CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar)).subtype ≤
        zpowers (⟨t, S.Lbar_le_Mbar k K.mem_Lbar⟩ : S.Mbar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ((Rbar S k t).subgroupOf S.Mbar)
  have heq := K.pCoreOf_Rbar_eq hy hCE h3
  have hN : ∀ x ∈ CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar),
      (x : S.O) ∈ S.Lbar u := fun x hx => by
    rw [heq] at hx
    exact K.timmesfeld_11_5 hy hCE (mem_subgroupOf.mp hx)
  refine frattini_map_le_of_sq hP (fun x hx => ?_) (fun x hx y hy => ?_)
  · rw [S7.mem_zpowers_Mbar_iff]
    exact (K.sq_comm_mem_zpowers_of_mem_Lbar (hN x hx)).1
  · rw [S7.mem_zpowers_Mbar_iff]
    exact (K.sq_comm_mem_zpowers_of_mem_Lbar (hN x hx)).2 _ (hN y hy)

theorem Conf.quotientIso_PSL3 (hm : finrank (ZMod 2) (Vt S k t) = 3) :
    timmesfeldQuotientIso (CFSG.Open.pCore 2 ((Rbar S k t).subgroupOf S.Mbar))
      PSL(3, ZMod 2) := by
  set b := Module.finBasisOfFinrankEq (ZMod 2) (Vt S k t) hm
  have heq := K.pCoreOf_Rbar_eq hy hCE hm.ge
  refine ⟨(toPSL3 b).comp (S7.resRM S k hy.hyp4.conj_mem t), ?_, ?_⟩
  · have hsurj : Function.Surjective (S7.resRM S k hy.hyp4.conj_mem t) := by
      rw [← MonoidHom.range_eq_top, S7.range_resRM, K.lin.eq_top]
    exact (toPSL3_surjective b).comp hsurj
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      show toPSL3 b (S7.resRM S k hy.hyp4.conj_mem t x) = 1 ↔
        S7.resRM S k hy.hyp4.conj_mem t x = 1 from
        ⟨fun h => toPSL3_injective b (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩,
      S7.resRM_eq_one_iff]
    constructor
    · intro hx
      have h1 : (x : S.Mbar) ∈ CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar) := by
        rw [heq]
        exact mem_subgroupOf.mpr hx
      obtain ⟨y, hy', hyx⟩ := h1
      rwa [Subtype.ext hyx] at hy'
    · intro hx
      have h1 : (x : S.Mbar) ∈ CFSG.Open.pCoreOf 2 ((Rbar S k t).subgroupOf S.Mbar) :=
        ⟨x, hx, rfl⟩
      rw [heq] at h1
      exact mem_subgroupOf.mp h1

end Conf

theorem irr_of_not_isReducible' {S : Setting G} (hirr : ¬ S.IsReducible) : S5.Irr S := by
  intro U hU
  by_contra h
  push Not at h
  exact hirr ⟨U, h.1, h.2, fun m v hv => hU _ ⟨m, rfl⟩ v hv⟩

theorem s11Alt4Stmt (hCE : CentralExtInput.{0}) : S14.S11Alt4Stmt := by
  intro G _ _ _ S k u τ hy K hm hn hirr
  obtain ⟨h3, hq, -⟩ := S5.timmesfeld_5_5 hCE (irr_of_not_isReducible' hirr) hy.hyp4 hy.noA2'
    hy.cons (S45Q.hyp45Q hy.hyp4 hy.cons) (by omega)
  have ht := K.mem_Lbar
  have hto : orderOf (⟨S.ρ τ, S.Lbar_le_Mbar k ht⟩ : S.Mbar) = 2 :=
    orderOf_eq_prime (Subtype.ext (by
      rw [pow_two]
      exact mul_self_of_mem_Lbar S hy.hyp4.conj_mem ht)) fun h => K.ne_one (congrArg Subtype.val h)
  exact ⟨hn, hq, Nat.le_of_dvd (by norm_num) h3, _, hto, _,
    S7.Rbar_subgroupOf_le_centralizer hy.hyp4 ht, S7.Rbar_subgroupOf_normal ht,
    K.frattini_le_zpowers hy hCE hm.ge, Or.inl (K.quotientIso_PSL3 hy hCE hm)⟩

end CFSG.LargeExtraspecial.S11
