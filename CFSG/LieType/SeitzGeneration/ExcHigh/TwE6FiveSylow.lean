module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoSpine

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open CFSG.Open

theorem exists_lift_of_le_range {G H : Type*} [Group G] [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker) {S : Subgroup G}
    (hS : S ≤ ψ.range) (hSe : IsElemAbelian p S) :
    ∃ S' : Subgroup H, IsElemAbelian p S' ∧ S'.map ψ = S ∧ Nat.card S' = Nat.card S := by
  have hker' : ¬ p ∣ Nat.card ψ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hS1 : IsElemAbelian p (S.subgroupOf ψ.range) := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => Subtype.ext (hSe.2 x.1 hx)⟩
    have h := congrArg Subtype.val (hSe.1.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨S', hS'map, hdis, hS'e⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ.rangeRestrict ψ.rangeRestrict_surjective hker' hS1
  refine ⟨S', hS'e, ?_, ?_⟩
  · rw [← MonoidHom.subtype_comp_rangeRestrict ψ, ← Subgroup.map_map, hS'map,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hS]
  · rw [← card_map_eq_of_disjoint_ker ψ.rangeRestrict hdis, hS'map]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

theorem exists_conj_lift_elemAbelian {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker)
    (hord : (Nat.card G).factorization p ≤ (Nat.card H).factorization p)
    (E₀ : Subgroup G) (hE₀ : IsElemAbelian p E₀) :
    ∃ (g : G) (E' : Subgroup H), IsElemAbelian p E' ∧
      E'.map ψ = E₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q⟩ : Nonempty (Sylow p H) := inferInstance
  have hdisj : Disjoint (Q : Subgroup H) ψ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxk
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨x, hxQ⟩
    have hm' : x ^ p ^ m = 1 := congrArg Subtype.val hm
    have hn : x ^ Nat.card ψ.ker = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ψ.ker) (x := ⟨x, hxk⟩))
    have hcop : Nat.Coprime (p ^ m) (Nat.card ψ.ker) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hker)
    have h1 : x ^ (p ^ m).gcd (Nat.card ψ.ker) = 1 := pow_gcd_eq_one.2 ⟨hm', hn⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
    exact h1
  obtain ⟨g, hg⟩ := exists_conj_le_map_sylow ψ Q hdisj hord E₀ hE₀.2
  have hE₁ : IsElemAbelian p (E₀.map (MulAut.conj g).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE₀ (MulAut.conj g).toMonoidHom
  have hle : E₀.map (MulAut.conj g).toMonoidHom ≤ ψ.range :=
    hg.trans (Subgroup.map_le_range ψ _)
  obtain ⟨S', hS'e, hS'map, -⟩ := exists_lift_of_le_range ψ hker hle hE₁
  exact ⟨g, S', hS'e, hS'map⟩

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
