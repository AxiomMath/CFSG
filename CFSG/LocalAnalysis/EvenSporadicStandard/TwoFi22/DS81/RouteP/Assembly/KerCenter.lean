module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem ker_le_center_of_totient_lt_card {Q S : Type*} [Group Q] [Group S] (f : Q →* S)
    [Finite f.ker] [IsCyclic f.ker] (hf : Function.Surjective f) (hS : IsSimpleGroup S)
    (h : Nat.totient (Nat.card f.ker) < Nat.card S) : f.ker ≤ Subgroup.center Q := by
  let φ : Q →* MulAut f.ker := MulAut.conjNormal
  have hKC : f.ker ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    ext x
    have hcomm : k * (x : Q) = (x : Q) * k :=
      congrArg Subtype.val (mul_comm' (⟨k, hk⟩ : f.ker) x)
    show (MulAut.conjNormal k x : Q) = x
    rw [MulAut.conjNormal_apply, hcomm, mul_inv_cancel_right]
  have hn : (φ.ker.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map f) with hbot | htop
  ·
    exfalso
    have hKeq : φ.ker = f.ker := le_antisymm ((Subgroup.map_eq_bot_iff _).1 hbot) hKC
    have hidx : f.ker.index = Nat.card S := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top]
    have hφ : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
    have hfin : Finite (MulAut f.ker) := by
      apply Nat.finite_of_card_ne_zero
      rw [IsCyclic.card_mulAut]
      exact (Nat.totient_pos.2 Nat.card_pos).ne'
    have hle : Nat.card φ.range ≤ Nat.card (MulAut f.ker) := Subgroup.card_le_card_group _
    rw [IsCyclic.card_mulAut] at hle
    rw [hKeq] at hφ
    omega
  ·
    have hC : φ.ker = ⊤ := by
      have := Subgroup.comap_map_eq_self hKC
      rw [htop, Subgroup.comap_top] at this
      exact this.symm
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : φ g = 1 := by rw [← MonoidHom.mem_ker, hC]; trivial
    have hgk := congrArg (fun a : MulAut f.ker => (a ⟨k, hk⟩ : Q)) hg
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at hgk
    calc g * k = g * k * g⁻¹ * g := (inv_mul_cancel_right (g * k) g).symm
      _ = k * g := by rw [hgk]

theorem ker_le_center_of_card_ker_eq_three {Q S : Type*} [Group Q] [Group S] (f : Q →* S)
    (hf : Function.Surjective f) (hS : IsSimpleGroup S) (hS2 : 2 < Nat.card S)
    (hk : Nat.card f.ker = 3) : f.ker ≤ Subgroup.center Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite f.ker := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsCyclic f.ker := isCyclic_of_prime_card hk
  refine ker_le_center_of_totient_lt_card f hf hS ?_
  rw [hk, Nat.totient_prime Nat.prime_three]
  exact hS2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
