module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep03

variable {G : Type*} [Group G]

theorem sat_eq_conjugatesOfSet (S : Set G) : sat S = Group.conjugatesOfSet S := by
  rw [conjugatesOfSet_eq_iUnion_image_conj_inv]
  rfl

theorem coprime_natCard_of_isCyclic_of_inf_eq_bot [Finite G] {Z K A : Subgroup G}
    [IsCyclic ↥Z] (hK : K ≤ Z) (hA : A ≤ Z) (hinter : K ⊓ A = ⊥) :
    (Nat.card ↥K).Coprime (Nat.card ↥A) := by
  by_contra hc
  obtain ⟨p, hp, hpK, hpA⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpA
  have hxZ : zpowers ((x : G)) ≤ Z := zpowers_le.2 (hK x.2)
  have hyZ : zpowers ((y : G)) ≤ Z := zpowers_le.2 (hA y.2)
  have hcard : Nat.card ↥(zpowers ((x : G))) = Nat.card ↥(zpowers ((y : G))) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_coe, orderOf_coe, hx, hy]
  have heq := eq_of_le_of_natCard_eq_of_isCyclic hxZ hyZ hcard
  have hxmem : (x : G) ∈ K ⊓ A := by
    refine ⟨x.2, ?_⟩
    have hmem : (x : G) ∈ zpowers ((y : G)) := heq ▸ mem_zpowers _
    exact (zpowers_le (H := A)).2 y.2 hmem
  rw [hinter] at hxmem
  have hx1 : x = 1 := Subtype.ext hxmem
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem lt_two_mul_pred_mul_pred {a b : ℕ} (hao : Odd a) (hbo : Odd b) (ha : 1 < a) (hb : 1 < b)
    (hne : a ≠ b) : (a : ℚ) * b < 2 * (((a : ℚ) - 1) * ((b : ℚ) - 1)) := by
  obtain ⟨k, hk⟩ := hao
  obtain ⟨l, hl⟩ := hbo
  have h5 : (3 ≤ a ∧ 5 ≤ b) ∨ (5 ≤ a ∧ 3 ≤ b) := by omega
  rcases h5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (3 : ℚ) ≤ a := by exact_mod_cast h1
    have h2' : (5 : ℚ) ≤ b := by exact_mod_cast h2
    nlinarith
  · have h1' : (5 : ℚ) ≤ a := by exact_mod_cast h1
    have h2' : (3 : ℚ) ≤ b := by exact_mod_cast h2
    nlinarith

theorem ncard_sdiff_union_eq_rat [Finite G] {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥) :
    ((((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))).ncard : ℚ))
      = ((Nat.card ↥W₁ : ℚ) - 1) * ((Nat.card ↥W₂ : ℚ) - 1) := by
  have hsub := Set.ncard_sdiff_add_ncard_of_subset (union_subset_of_coe_eq_mul hW)
    (Set.toFinite _)
  have h1 := ncard_union_add_one (G := G) hinter
  have h2 := natCard_of_coe_eq_mul (G := G) hW hinter
  rw [(Nat.card_coe_set_eq ((W : Set G))).symm] at hsub
  have hsub' : ((((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))).ncard : ℚ))
      + (((W₁ : Set G) ∪ (W₂ : Set G)).ncard : ℚ) = (Nat.card ↥W : ℚ) := by
    exact_mod_cast hsub
  have h1' : ((((W₁ : Set G) ∪ (W₂ : Set G)).ncard : ℚ)) + 1
      = (Nat.card ↥W₁ : ℚ) + Nat.card ↥W₂ := by exact_mod_cast h1
  have h2' : (Nat.card ↥W : ℚ) = (Nat.card ↥W₁ : ℚ) * Nat.card ↥W₂ := by exact_mod_cast h2
  linear_combination hsub' - h1' + h2'

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_pair_mixed_density (h₁ : Statements.FNI_kappa_local_pair.{u}) :
    Statements.FNI_kappa_pair_mixed_density.{u} := by
  intro G _ _ M K A Z hsetup
  obtain ⟨Mstar, -, -, -, -, -, -, hdirect, hcyc, -, -, -, -,
    ⟨hTne, hTnorm, hTTI⟩, -⟩ := h₁ G M K A Z hsetup
  obtain ⟨hKZ, hAZ, hsup, hinter, hcomm⟩ := hdirect
  set T : Set G := (Z : Set G) \ ((K : Set G) ∪ (A : Set G)) with hTdef
  have hcomm' : ∀ x ∈ K, ∀ y ∈ A, Commute x y := by
    intro x hx y hy
    have hcx := (commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := A)).1 hcomm hx
    exact (mem_centralizer_iff.1 hcx y hy).symm
  have hW : (Z : Set G) = (K : Set G) * (A : Set G) := by
    rw [← hsup]; exact coe_sup_eq_mul_of_commute hcomm'
  obtain ⟨d, hdZ, hdKA⟩ := hTne
  have hKbot : K ≠ ⊥ := by
    rintro rfl
    rw [bot_sup_eq] at hsup
    exact hdKA (Or.inr (hsup ▸ hdZ))
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hsup
    exact hdKA (Or.inl (hsup ▸ hdZ))
  have hTI : IsTIWithNormalizer T Z := by
    refine ⟨⟨d, hdZ, hdKA⟩, by simp [hTdef], hTnorm, fun g hg => ?_⟩
    have hg' : g⁻¹ ∉ Z := fun hc => hg (by simpa using Z.inv_mem hc)
    rw [Set.disjoint_iff_inter_eq_empty]
    refine Eq.trans (congrArg _ ?_) (hTTI g⁻¹ hg')
    exact (Set.image_congr' fun x => by simp [MulAut.conj_apply]).symm
  have hZcard : Nat.card ↥Z = Nat.card ↥K * Nat.card ↥A := natCard_of_coe_eq_mul hW hinter
  have hKpos : (0 : ℚ) < Nat.card ↥K := by exact_mod_cast Nat.card_pos (α := ↥K)
  have hApos : (0 : ℚ) < Nat.card ↥A := by exact_mod_cast Nat.card_pos (α := ↥A)
  have hidxN : Z.index * (Nat.card ↥K * Nat.card ↥A) = Nat.card G := by
    rw [← hZcard]; exact Subgroup.index_mul_card Z
  have hidx : (Z.index : ℚ) * ((Nat.card ↥K : ℚ) * (Nat.card ↥A : ℚ)) = (Nat.card G : ℚ) := by
    exact_mod_cast hidxN
  have hsatcard : ((sat T).ncard : ℚ) = (Z.index : ℚ) * (T.ncard : ℚ) := by
    rw [sat_eq_conjugatesOfSet]
    exact_mod_cast ncard_conjugatesOfSet_eq_index_mul_ncard hTI
  have hTcard : (T.ncard : ℚ) = ((Nat.card ↥K : ℚ) - 1) * ((Nat.card ↥A : ℚ) - 1) :=
    ncard_sdiff_union_eq_rat hW hinter
  have hexact : ((sat T).ncard : ℚ)
      = (Nat.card G : ℚ) * ((Nat.card ↥K : ℚ) - 1) * ((Nat.card ↥A : ℚ) - 1)
          / ((Nat.card ↥K : ℚ) * (Nat.card ↥A : ℚ)) := by
    rw [hsatcard, hTcard, eq_div_iff (by positivity), ← hidx]
    ring
  refine ⟨hexact, ?_⟩
  have hodd : Odd (Nat.card G) := hsetup.ambient.odd_natCard
  have hKodd : Odd (Nat.card ↥K) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hAodd : Odd (Nat.card ↥A) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card A)
  have hK1 : 1 < Nat.card ↥K := (Subgroup.one_lt_card_iff_ne_bot K).2 hKbot
  have hA1 : 1 < Nat.card ↥A := (Subgroup.one_lt_card_iff_ne_bot A).2 hAbot
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥A) :=
    coprime_natCard_of_isCyclic_of_inf_eq_bot hKZ hAZ hinter
  have hne : Nat.card ↥K ≠ Nat.card ↥A := by
    intro h
    rw [h] at hcop
    have := (Nat.coprime_self _).1 hcop
    omega
  have key := lt_two_mul_pred_mul_pred hKodd hAodd hK1 hA1 hne
  have hGpos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  rw [hexact, lt_div_iff₀ (by positivity)]
  nlinarith [key, hGpos]

end CFSG.FeitThompson.Proofs

end
