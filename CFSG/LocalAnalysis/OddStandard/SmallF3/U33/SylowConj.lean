module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open scoped Pointwise

theorem exists_conj_mem_sylow {G : Type*} [Group G] (Γ Q : Subgroup G) [Finite Γ] {p a m : ℕ}
    [Fact p.Prime] (hΓ : Nat.card Γ = p ^ a * m) (hm : ¬ p ∣ m) (hQΓ : Q ≤ Γ)
    (hQ : Nat.card Q = p ^ a) {g : G} (hgΓ : g ∈ Γ) (hg : g ^ p = 1) :
    ∃ c ∈ Γ, c * g * c⁻¹ ∈ Q := by
  have hp : p.Prime := Fact.out
  have hpne : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hmne : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hfac : (Nat.card Γ).factorization p = a := by
    rw [hΓ, Nat.factorization_mul hpne hmne]
    simp only [Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  let Q' : Subgroup Γ := Q.subgroupOf Γ
  have hQ'card : Nat.card Q' = p ^ a := by
    dsimp only [Q']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv, hQ]
  have hQ'fac : Nat.card Q' = p ^ (Nat.card Γ).factorization p := by
    rw [hfac]
    exact hQ'card
  let S : Sylow p Γ := Sylow.ofCard Q' hQ'fac
  have hS : (S : Subgroup Γ) = Q' := Sylow.coe_ofCard Q' hQ'fac
  let g' : Γ := ⟨g, hgΓ⟩
  have hg'pow : g' ^ p = 1 := Subtype.ext (by simpa [g'] using hg)
  have hP : IsPGroup p (Subgroup.zpowers g') := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hg'pow
  obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hP
  haveI : Finite (Sylow p Γ) := Sylow.finite_of_finiteIndex S
  obtain ⟨c', hc'⟩ := MulAction.exists_smul_eq Γ S R
  have hg'R : g' ∈ (R : Subgroup Γ) := hR (Subgroup.mem_zpowers g')
  have hg'mem : g' ∈ MulAut.conj c' • (S : Subgroup Γ) := by
    rw [← Sylow.coe_subgroup_smul (g := c') (P := S), hc']
    exact hg'R
  have hthis : (MulAut.conj c')⁻¹ • g' ∈ (S : Subgroup Γ) :=
    (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj c')
      (S := (S : Subgroup Γ)) (x := g')).mp hg'mem
  have hsmul : (MulAut.conj c')⁻¹ • g' = c'⁻¹ * g' * c' := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  have hmemQ : c'⁻¹ * g' * c' ∈ Q' := by
    rw [← hsmul, ← hS]
    exact hthis
  refine ⟨((c'⁻¹ : Γ) : G), (c'⁻¹ : Γ).2, ?_⟩
  simpa [Subgroup.coe_inv, g'] using (Subgroup.mem_subgroupOf.mp hmemQ)

end CFSG.OddStandard.SmallF3.HarrisU33
