module

public import Mathlib.Data.Nat.Prime.Defs
import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
public import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v w

theorem natCard_fixedPoints_comp_subtype_eq_natCard_subtype {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range V)
      = Nat.card {v : V // ∀ b ∈ B, ρ b v = v} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixedPoints_comp_subtype_iff ρ B)

theorem natCard_multiplicative_pi_zmod (p d : ℕ) :
    Nat.card (Multiplicative (Fin d → ZMod p)) = p ^ d := by
  rw [Nat.card_congr (Multiplicative.toAdd (α := Fin d → ZMod p)), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_invariant_normal_elementaryAbelian {A : Type u} {V : Type v} [Group A] [Group V]
    [Finite A] [Finite V] [Nontrivial V] [Group.IsSolvable A] [Group.IsSolvable V]
    (ρ : A →* MulAut V) :
    ∃ (N : Subgroup V) (p d : ℕ), N.Normal ∧ IsInvariantSubgroup ρ N ∧ N ≠ ⊥ ∧ p.Prime ∧ 1 ≤ d ∧
      Nonempty (↥N ≃* Multiplicative (Fin d → ZMod p)) := by
  have : Finite (V ⋊[ρ] A) := Finite.of_equiv _ equivProd.symm
  have hXsolv : Group.IsSolvable (V ⋊[ρ] A) :=
    Group.isSolvable_of_ker_le_range (inl : V →* V ⋊[ρ] A) (rightHom : V ⋊[ρ] A →* A)
      (le_of_eq range_inl_eq_ker_rightHom.symm)
  have hWn : (inl : V →* V ⋊[ρ] A).range.Normal := by
    rw [range_inl_eq_ker_rightHom]; infer_instance
  have hWb : (inl : V →* V ⋊[ρ] A).range ≠ ⊥ := by
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    intro hc
    rw [Subgroup.eq_bot_iff_forall] at hc
    exact hv (inl_injective (by simpa using hc (inl v) ⟨v, rfl⟩))
  obtain ⟨M, hMn, hMb, hMW, hmin⟩ := exists_normal_ne_bot_le_forall_lt_eq_bot hWn hWb
  have : M.Normal := hMn
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hMb hmin
  have key : ∀ b : A, ∀ v : V, (inl v : V ⋊[ρ] A) ∈ M → (inl (ρ b v) : V ⋊[ρ] A) ∈ M := by
    intro b v hv
    have := hMn.conj_mem (inl v) hv (inr b)
    rwa [← map_inv, ← inl_aut] at this
  refine ⟨M.comap (inl : V →* V ⋊[ρ] A), p, d, hMn.comap _, ?_, ?_, hp, hd, ?_⟩
  · refine isInvariantSubgroup_iff_forall_map_eq.2 fun b => le_antisymm ?_ ?_
    · rintro x ⟨v, hv, rfl⟩
      exact key b v hv
    · intro v hv
      refine ⟨ρ b⁻¹ v, key b⁻¹ v hv, ?_⟩
      change ρ b (ρ b⁻¹ v) = v
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  · intro hc
    rw [← Subgroup.map_comap_eq_self hMW, hc, Subgroup.map_bot] at hMb
    exact hMb rfl
  · exact ⟨(Subgroup.equivMapOfInjective _ _ inl_injective).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hMW)).trans e)⟩

private theorem prod_natCard_fixedPoints_comp_subtype_pow_eq_of_natCard_le
    {A : Type u} [Group A] [Finite A] [Group.IsSolvable A]
    {ι : Type w} [Fintype ι] (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∀ k : ℕ, ∀ {V : Type v} [Group V] [Finite V] [Group.IsSolvable V] (ρ : A →* MulAut V),
      Nat.card V ≤ k → (Nat.card A).Coprime (Nat.card V) →
      ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V) ^ (m i * Nat.card (B i))
        = ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V)
            ^ (n i * Nat.card (B i)) := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ ρ hk _
    exact absurd (Nat.le_zero.1 hk) Nat.card_pos.ne'
  | succ k ih =>
    intro V _ _ _ ρ hk hcop
    rcases subsingleton_or_nontrivial V with hV | hV
    ·
      have h1 : ∀ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V) = 1 :=
        fun _ => by rw [Subgroup.card_eq_one]; exact Subsingleton.elim _ _
      simp only [h1, one_pow, Finset.prod_const_one]
    · obtain ⟨N, p, d, hNn, hNinv, hNb, hp, hd, ⟨e⟩⟩ :=
        exists_invariant_normal_elementaryAbelian ρ
      have : N.Normal := hNn
      by_cases hNtop : N = ⊤
      ·
        subst hNtop
        have eV : V ≃* Multiplicative (Fin d → ZMod p) := Subgroup.topEquiv.symm.trans e
        have hpV : p ∣ Nat.card V := by
          rw [Nat.card_eq_of_bijective eV eV.bijective, natCard_multiplicative_pi_zmod]
          exact dvd_pow_self p (by omega)
        have hA : ¬ p ∣ Nat.card A := fun hc =>
          hp.one_lt.ne' (Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hc hpV))
        simp only [natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
        exact prod_natCard_fixedPoints_pow_eq_of_monoidHom_mulAut hp hA ⟨eV⟩ ρ B m n hmn
      ·
        have hNlt : Nat.card ↥N < Nat.card V :=
          natCard_lt_natCard_of_lt_top (lt_of_le_of_ne le_top hNtop)
        have hQlt : Nat.card (V ⧸ N) < Nat.card V :=
          natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hNb)
        have hN := ih hNinv.restrictAut (by omega)
          (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N))
        have hQ := ih hNinv.quotientAut (by omega)
          (hcop.coprime_dvd_right N.card_quotient_dvd_card)
        have hmul : ∀ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V)
            = Nat.card (FixedPoints.subgroup (hNinv.restrictAut.comp (B i).subtype).range ↥N)
              * Nat.card (FixedPoints.subgroup
                  (hNinv.quotientAut.comp (B i).subtype).range (V ⧸ N)) := fun i =>
          natCard_fixedPoints_comp_subtype_eq_mul hNinv hcop (B i)
        simp only [hmul, mul_pow, Finset.prod_mul_distrib, hN, hQ]

variable {A V : Type*} [Group A] [Group V] [Finite A] [Finite V] [Group.IsSolvable A]
  [Group.IsSolvable V] {ι : Type*} [Fintype ι]

theorem prod_natCard_fixedPoints_comp_subtype_pow_eq (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (B : ι → Subgroup A)
    [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V) ^ (m i * Nat.card (B i))
      = ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V)
          ^ (n i * Nat.card (B i)) :=
  prod_natCard_fixedPoints_comp_subtype_pow_eq_of_natCard_le B m n hmn (Nat.card V) ρ le_rfl hcop

theorem prod_natCard_centralizer_pow_eq (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (B : ι → Subgroup A)
    [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∏ i, Nat.card {v : V // ∀ b ∈ B i, ρ b v = v} ^ (m i * Nat.card (B i))
      = ∏ i, Nat.card {v : V // ∀ b ∈ B i, ρ b v = v} ^ (n i * Nat.card (B i)) := by
  simp only [← natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
  exact prod_natCard_fixedPoints_comp_subtype_pow_eq ρ hcop B m n hmn

end CFSG.FeitThompson
