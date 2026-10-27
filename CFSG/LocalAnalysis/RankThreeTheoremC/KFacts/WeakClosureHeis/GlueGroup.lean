module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup
open scoped commutatorElement

section Glue

variable {p : ℕ}

theorem central_of_normal_of_card_prime [Fact p.Prime] {X : Type*} [Group X] [Finite X] {Q A : Subgroup X}
    (hQ : IsPGroup p Q) (hAQ : A ≤ Q) (hA : Nat.card A = p)
    (hn : ∀ q ∈ Q, A.map (MulAut.conj q).toMonoidHom ≤ A) : ∀ a ∈ A, ∀ q ∈ Q, q * a = a * q := by
  classical
  have hconj : ∀ q ∈ Q, ∀ a ∈ A, q * a * q⁻¹ ∈ A := by
    intro q hq a ha
    have h1 := hn q hq (Subgroup.mem_map_of_mem _ ha)
    simpa [MulAut.conj_apply] using h1
  letI : MulAction Q A :=
    { smul := fun q a => ⟨(q : X) * (a : X) * (q : X)⁻¹, hconj (q : X) q.2 (a : X) a.2⟩
      one_smul := fun a => Subtype.ext (by
        show ((1 : Q) : X) * (a : X) * ((1 : Q) : X)⁻¹ = (a : X)
        simp)
      mul_smul := fun q r a => Subtype.ext (by
        show ((q * r : Q) : X) * (a : X) * ((q * r : Q) : X)⁻¹
          = (q : X) * ((r : X) * (a : X) * (r : X)⁻¹) * (q : X)⁻¹
        simp [mul_assoc]) }
  have hmod := hQ.card_modEq_card_fixedPoints A
  rw [hA] at hmod
  have hp0 : p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints Q A) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hp0)
  have hone : (1 : A) ∈ MulAction.fixedPoints Q A := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by
      show (g : X) * (1 : X) * (g : X)⁻¹ = 1
      simp)
  haveI : Nonempty (MulAction.fixedPoints Q A) := ⟨⟨1, hone⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q A) := Nat.card_pos
  have hle1 : p ≤ Nat.card (MulAction.fixedPoints Q A) := Nat.le_of_dvd hpos hdvd
  have hcardF : Nat.card (MulAction.fixedPoints Q A) = (MulAction.fixedPoints Q A).ncard :=
    Nat.card_coe_set_eq _
  have hFeq : MulAction.fixedPoints Q A = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, hA, ← hcardF]
    exact hle1
  intro a ha q hq
  have hmem : (⟨a, ha⟩ : A) ∈ MulAction.fixedPoints Q A := by
    rw [hFeq]
    exact Set.mem_univ _
  rw [MulAction.mem_fixedPoints] at hmem
  have h2 : (q : X) * a * (q : X)⁻¹ = a := congrArg Subtype.val (hmem ⟨q, hq⟩)
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem pow_eq_one_of_card_prime {X : Type*} [Group X] [Finite X] {A : Subgroup X} (hA : Nat.card A = p) :
    ∀ a ∈ A, a ^ p = 1 := by
  intro a ha
  have h1 : orderOf (⟨a, ha⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
  rw [hA, Subgroup.orderOf_mk] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp h1

theorem pow_three_le_card_of_nonabelian [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (hn : ¬ IsMulCommutative G) : p ^ 3 ≤ Nat.card G := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hG
  rw [hcard]
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · exfalso
    apply hn
    interval_cases n
    ·
      have h0 : Nat.card G = 1 := by rw [hcard, pow_zero]
      obtain ⟨hsub, _⟩ := Nat.card_eq_one_iff_unique.mp h0
      exact IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
    ·
      have h1 : Nat.card G = p := by rw [hcard, pow_one]
      haveI : IsCyclic G := isCyclic_of_prime_card h1
      exact IsCyclic.isMulCommutative
    ·
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  · exact Nat.pow_le_pow_right hp.pos h3

end Glue

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
