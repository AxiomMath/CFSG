module

public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM

@[expose] def InnPartOddFree (X : Type) [Group X] : Prop :=
  ∀ 𝒳 : Subgroup (MulAut X), innSubgroup X ≤ 𝒳 → ∀ f : 𝒳, (f : MulAut X) ∈ innSubgroup X →
    orderOf f = 2 →
      oddCoreIn (Subgroup.centralizer ({f} : Set 𝒳) ⊓ (innSubgroup X).subgroupOf 𝒳) = ⊥

theorem oddCoreIn_eq_bot_of_mulEquiv_of_mem_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {U : Subgroup A} {U' : Subgroup B} (h : ∀ g, g ∈ U ↔ e g ∈ U') (hU' : oddCoreIn U' = ⊥) :
    oddCoreIn U = ⊥ := by
  have hU : U = U'.map e.symm.toMonoidHom := by
    ext g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hg
      exact ⟨e g, (h g).mp hg, e.symm_apply_apply g⟩
    · rintro ⟨g', hg', rfl⟩
      exact (h _).mpr (by rwa [e.apply_symm_apply])
  rw [hU]
  exact oddCoreIn_map_eq_bot e.symm.toMonoidHom e.symm.injective hU'

theorem innPartOddFree_of_oddCoreFree {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (hO : ∀ x : S, orderOf x = 2 → oddCoreIn (Subgroup.centralizer ({x} : Set S)) = ⊥) :
    InnPartOddFree S := by
  intro 𝒳 hinn f hfinn hf
  obtain ⟨s, hs⟩ := hfinn
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  have hss : s * s = 1 := by
    apply conj_injective_of_center_eq_bot hZ
    rw [map_mul, hs, map_one]
    exact congrArg Subtype.val hf2
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one] at hs
    have : orderOf f = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hs.symm
    omega
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rwa [← sq] at hss) hs1
  have hfs : (f : MulAut S) = MulAut.conj s := hs.symm
  have hfix : oddCoreIn (fixedSubgroup (f : MulAut S)) = ⊥ := by
    rw [hfs, fixedSubgroup_conj]
    exact hO s hs2
  exact oddCoreIn_centralizer_inner_eq_bot hZ 𝒳 hinn f hf2 hfix

theorem mem_innSubgroup_iff_autToCentralQuotient {X : Type} [Group X] [Group.IsPerfect X]
    (α : MulAut X) :
    α ∈ innSubgroup X ↔
      autToCentralQuotient X α ∈ innSubgroup (X ⧸ Subgroup.center X) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨x, autToCentralQuotient_injective (X := X) ?_⟩
    rw [← hs]
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl

theorem innPartOddFree_of_centralQuotient {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (h : InnPartOddFree (X ⧸ Subgroup.center X)) : InnPartOddFree X := by
  intro 𝒳 hinn f hfinn hf
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  have hεinn : ((ε f : ↥𝒳') : MulAut (X ⧸ Subgroup.center X)) ∈
      innSubgroup (X ⧸ Subgroup.center X) :=
    (mem_innSubgroup_iff_autToCentralQuotient (f : MulAut X)).mp hfinn
  have key := h 𝒳' hinn' (ε f) hεinn hf'
  refine oddCoreIn_eq_bot_of_mulEquiv_of_mem_iff ε (fun g => ?_) key
  have hcomm : g * f = f * g ↔ ε g * ε f = ε f * ε g := by
    rw [← map_mul ε g f, ← map_mul ε f g, ε.injective.eq_iff]
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
  exact and_congr hcomm (mem_innSubgroup_iff_autToCentralQuotient (g : MulAut X))

section D4


theorem innPartOddFree_of_D4 (X : Type) [Group X] [Finite X]
    (ψ : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) : InnPartOddFree X := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨hXq, hψ', hker', hSq, hZS⟩ :=
    centralQuotientData (t := .POmegaPlus) (n := 4) Nat.prime_three trivial hadm X ψ hψ hker
  have : Group.IsPerfect X := ⟨hXq.1⟩
  refine innPartOddFree_of_centralQuotient (innPartOddFree_of_oddCoreFree hZS fun x hx => ?_)
  exact modelOddCentralizerFree3_proved .POmegaPlus 4 Nat.prime_three trivial hadm
    (X ⧸ Subgroup.center X) _ hψ' hker' x hx

end D4

end CFSG.ClassicalInvolution.Q3.Q3T6D
