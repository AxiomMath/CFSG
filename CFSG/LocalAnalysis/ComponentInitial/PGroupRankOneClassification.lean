module

public import CFSG.LocalAnalysis.ComponentInitial.CyclicAbelianIndexTwo
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.GroupTheory.QuaternionCentralizers

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem pgroup_rank_one_classification {p : ℕ} (hp : p.Prime) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) :
    CFSG.pRank p P ≤ 1 ↔ IsCyclic P ∨
      (p = 2 ∧ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))) := by
  rw [pgroup_rank_one_abelian_subgroups hp hP]
  constructor
  · intro hcyc
    by_cases hab : ∀ a b : P, a * b = b * a
    · left
      have htop : IsMulCommutative (⊤ : Subgroup P) :=
        ⟨⟨fun a b => Subtype.ext (hab a b)⟩⟩
      have := hcyc ⊤ htop
      exact isCyclic_of_surjective (Subgroup.topEquiv).toMonoidHom Subgroup.topEquiv.surjective
    right
    have hnab : ∃ a b : P, a * b ≠ b * a := by
      push Not at hab
      exact hab
    obtain ⟨hp2, -⟩ := cyclic_abelian_prime_and_center hp hP hnab hcyc
    subst hp2
    refine ⟨rfl, ?_⟩
    obtain ⟨N, hNn, hNc, hN4, -, hKc, hK2, -⟩ :=
      cyclic_abelian_index_two_cyclic hp hP hnab hcyc
    obtain ⟨g, hg⟩ := hKc.exists_generator
    have hKx : centralizer (N : Set P) = zpowers (g : P) := by
      apply le_antisymm
      · intro a ha
        obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
        replace hi : g ^ i = ⟨a, ha⟩ := hi
        exact ⟨i, by
          show (g : P) ^ i = a
          rw [← Subgroup.coe_zpow, hi]⟩
      · exact zpowers_le.2 g.2
    obtain ⟨y, hyK, hy4⟩ := order_four_outside_cyclic_index_two hP hnab hcyc hKc hK2
    rw [hKx] at hyK hK2
    obtain ⟨hyx, hk⟩ := quaternion_conjugation_forcing hP hnab hcyc hNn hNc hN4 hKx hK2 hyK hy4
    obtain ⟨k, hkx⟩ := hP.exists_orderOf_eq_pow (g : P)
    obtain ⟨hk2, hy2⟩ := hk k (by rw [Nat.card_zpowers, hkx])
    have hgen : closure ({(g : P), y} : Set P) = ⊤ := by
      have hle : zpowers (g : P) ≤ closure ({(g : P), y} : Set P) :=
        zpowers_le.2 (subset_closure (Set.mem_insert _ _))
      have hyc : y ∈ closure ({(g : P), y} : Set P) :=
        subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton y))
      have hdvd := Subgroup.index_dvd_of_le hle
      rw [hK2] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact Subgroup.index_eq_one.1 h
      · exfalso
        apply hyK
        have hcard : Nat.card (closure ({(g : P), y} : Set P)) ≤ Nat.card (zpowers (g : P)) := by
          have h1 := (closure ({(g : P), y} : Set P)).index_mul_card
          have h2 := (zpowers (g : P)).index_mul_card
          rw [h] at h1
          rw [hK2] at h2
          omega
        have heq := Subgroup.eq_of_le_of_card_ge hle hcard
        rw [heq]
        exact hyc
    refine ⟨k + 1, by omega, ?_⟩
    have hm : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    have hx : orderOf (g : P) = 2 * 2 ^ (k - 1) := by
      rw [hkx, ← pow_succ', show k - 1 + 1 = k by omega]
    obtain ⟨⟨e, -⟩, -⟩ := CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism hm hgen hx hyK
      hy2 hyx
    rw [show k + 1 - 2 = k - 1 by omega]
    exact ⟨e.symm⟩
  · rintro (hcyc | ⟨-, n, hn, ⟨e⟩⟩)
    · intro B _
      exact Subgroup.isCyclic_of_le le_top
    · intro B hB
      have hm : 2 ≤ 2 ^ (n - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hQ := (CFSG.GroupTheory.quaternion_centralizers hm).2.2.2 (B.map e.toMonoidHom)
        (by
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          have := hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
          simp only [MulEquiv.coe_toMonoidHom]
          rw [← map_mul, ← map_mul]
          exact congrArg e (congrArg Subtype.val this))
      exact isCyclic_of_surjective
        (B.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
        (B.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

end CFSG.LocalAnalysis.ComponentInitial
