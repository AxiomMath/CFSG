module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.QuasithinUnique.AppC

open Equiv
open scoped Pointwise

@[expose] def d4fun : DihedralGroup 4 → Perm (Fin 4)
  | DihedralGroup.r i => Equiv.subRight (show Fin 4 from i)
  | DihedralGroup.sr i => Equiv.subLeft (show Fin 4 from i)

theorem d4fun_mul : ∀ a b : DihedralGroup 4, d4fun (a * b) = d4fun a * d4fun b := by
  decide +kernel

theorem d4fun_injective : ∀ a b : DihedralGroup 4, d4fun a = d4fun b → a = b := by
  decide +kernel

@[expose] def d4 : DihedralGroup 4 →* Perm (Fin 4) := MonoidHom.mk' d4fun d4fun_mul

theorem d4_injective : Function.Injective d4 := fun a b h => d4fun_injective a b h

theorem card_range_d4 : Nat.card d4.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective d4_injective).toEquiv, DihedralGroup.nat_card]

theorem card_perm_four : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem card_le_eight {P : Subgroup (Perm (Fin 4))} (hP : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : Nat.card P ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card P
    rwa [card_perm_four] at this
  rw [hn] at hd ⊢
  by_contra hlt
  have h4 : 4 ≤ n := by
    by_contra h
    exact hlt (by interval_cases n <;> norm_num)
  have h16 : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 h4).trans hd
  norm_num at h16

theorem exists_mulEquiv_dihedral {P : Subgroup (Perm (Fin 4))} (hP : Nat.card P = 8) :
    Nonempty (DihedralGroup 4 ≃* P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hP0 : IsPGroup 2 d4.range := IsPGroup.of_card (n := 3) (by rw [card_range_d4]; norm_num)
  have hidx : ∀ Q : Subgroup (Perm (Fin 4)), Nat.card Q = 8 → ¬ 2 ∣ Q.index := by
    intro Q hQ h2
    have := Subgroup.card_mul_index Q
    rw [hQ, card_perm_four] at this
    have hi : Q.index = 3 := by omega
    rw [hi] at h2
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 4))
    (hP0.toSylow (hidx _ card_range_d4)) (hP'.toSylow (hidx _ hP))
  have hsub : MulAut.conj g • d4.range = P := by
    have := congrArg (fun Q : Sylow 2 (Perm (Fin 4)) => (Q : Subgroup (Perm (Fin 4)))) hg
    exact this
  rw [Subgroup.pointwise_smul_def] at hsub
  exact ⟨((MonoidHom.ofInjective d4_injective).trans
    (Subgroup.equivMapOfInjective d4.range _ (MulAut.conj g).injective)).trans
      (MulEquiv.subgroupCongr hsub)⟩

theorem pair_cases {c : Perm (Fin 4)} {a b : Fin 4} (hab : a ≠ b)
    (h1 : c a ∈ ({a, b} : Finset (Fin 4))) (h2 : c b ∈ ({a, b} : Finset (Fin 4))) :
    (c a = a ∧ c b = b) ∨ (c a = b ∧ c b = a) := by
  have hne : c a ≠ c b := fun h' => hab (c.injective h')
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem exists_pair_stabilizer {P : Subgroup (Perm (Fin 4))} (hP : Nat.card P = 8) {a b : Fin 4}
    (hab : a ≠ b) : ∃ g ∈ P, g ≠ 1 ∧ ((g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a)) := by
  by_contra hcon
  let φ : P → ↥(Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))) := fun g =>
    ⟨{(g : Perm (Fin 4)) a, (g : Perm (Fin 4)) b}, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair fun h => hab ((g : Perm (Fin 4)).injective h)⟩⟩
  have hφ : Function.Injective φ := by
    intro g h hgh
    have hset : ({(g : Perm (Fin 4)) a, (g : Perm (Fin 4)) b} : Finset (Fin 4)) =
        {(h : Perm (Fin 4)) a, (h : Perm (Fin 4)) b} := congrArg Subtype.val hgh
    have hc : (h : Perm (Fin 4))⁻¹ * (g : Perm (Fin 4)) ∈ P := mul_mem (inv_mem h.2) g.2
    have m1 : (g : Perm (Fin 4)) a ∈
        ({(h : Perm (Fin 4)) a, (h : Perm (Fin 4)) b} : Finset (Fin 4)) := by
      rw [← hset]; simp
    have m2 : (g : Perm (Fin 4)) b ∈
        ({(h : Perm (Fin 4)) a, (h : Perm (Fin 4)) b} : Finset (Fin 4)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have hca : ((h : Perm (Fin 4))⁻¹ * (g : Perm (Fin 4))) a ∈ ({a, b} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Perm.mul_apply]
      rcases m1 with m1 | m1
      · left; rw [m1]; simp
      · right; rw [m1]; simp
    have hcb : ((h : Perm (Fin 4))⁻¹ * (g : Perm (Fin 4))) b ∈ ({a, b} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Perm.mul_apply]
      rcases m2 with m2 | m2
      · left; rw [m2]; simp
      · right; rw [m2]; simp
    have hdisj := pair_cases hab hca hcb
    have hc1 : (h : Perm (Fin 4))⁻¹ * (g : Perm (Fin 4)) = 1 := by
      by_contra hc1
      exact hcon ⟨_, hc, hc1, hdisj⟩
    exact Subtype.ext (inv_mul_eq_one.1 hc1).symm
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [hP, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard] at h1
  have h6 : Nat.choose (Finset.univ : Finset (Fin 4)).card 2 = 6 := by decide
  omega

end CFSG.QuasithinUnique.AppC
