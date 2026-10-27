module

public import Mathlib.GroupTheory.Index
import CFSG.GroupTheory.ConjQuot
import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem card_mulAut_dvd_six_of_card_eq_four {V : Type*} [Group V] (h : Nat.card V = 4) :
    Nat.card (MulAut V) ∣ 6 := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  have hS : Nat.card {x : V // x ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, h]
  let φ : MulAut V →* Equiv.Perm {x : V // x ≠ 1} :=
    { toFun := fun σ => σ.toEquiv.subtypeEquiv (fun a => by simp)
      map_one' := by ext; rfl
      map_mul' := fun σ τ => by ext; rfl }
  have hφ : Function.Injective φ := by
    intro σ τ hστ
    ext x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · have := congrArg (fun π : Equiv.Perm {x : V // x ≠ 1} => (π ⟨x, hx⟩ : V)) hστ
      simpa [φ] using this
  have h1 := Subgroup.card_dvd_of_injective φ hφ
  have hperm : Nat.card (Equiv.Perm {x : V // x ≠ 1}) = 6 := by
    have : Fintype {x : V // x ≠ 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hS]
    rfl
  rwa [hperm] at h1

theorem exists_ne_one_commutator_mem_of_index_four {G : Type*} [Group G] {T N H : Subgroup G}
    (hNT : N ≤ T) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hHT : H ≤ Subgroup.normalizer (T : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hidx : (N.subgroupOf T).index = 4) (hH : 6 < Nat.card H) :
    ∃ h ∈ H, h ≠ 1 ∧ ∀ t ∈ T, ⁅h, t⁆ ∈ N := by
  haveI : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr hTN
  have hA := card_mulAut_dvd_six_of_card_eq_four (V := ↥T ⧸ N.subgroupOf T)
    (by rw [← Subgroup.index_eq_card, hidx])
  obtain ⟨h, hker, hne⟩ : ∃ h ∈ (conjQuotHom hHT hHN).ker, h ≠ 1 := by
    by_contra! hall
    have hinj : Function.Injective (conjQuotHom hHT hHN) :=
      (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).mpr hall)
    have := Nat.le_of_dvd (by norm_num) ((Subgroup.card_dvd_of_injective _ hinj).trans hA)
    omega
  refine ⟨h, h.2, fun h1 => hne (Subtype.ext h1), fun t ht => ?_⟩
  have hfix := DFunLike.congr_fun (MonoidHom.mem_ker.mp hker)
    ((⟨t⁻¹, T.inv_mem ht⟩ : ↥T) : ↥T ⧸ N.subgroupOf T)
  rw [conjQuotHom_apply, conjQuotAut_mk, MulAut.one_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hfix
  simpa [commutatorElement_def, mul_assoc] using hfix

end CFSG.GroupTheory
