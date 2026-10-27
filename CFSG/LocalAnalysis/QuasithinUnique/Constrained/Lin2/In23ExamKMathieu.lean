module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Unc25G2.M2x

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem false_of_twoE (hT : TwoE X) {A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hcard : 32 ≤ Nat.card A) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := by
    intro x
    refine ⟨1, ?_⟩
    have := hA.2 (x : X) x.2
    exact Subtype.ext (by simpa using this)
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hat := hT.exists_at P.isPGroup' P.not_dvd_index
  obtain ⟨Ea, Eb, -, -, hEaP, hEbP, hne, hEa, hEb, hca, hcb, hcl, -, -, -, -⟩ := hat
  obtain ⟨j, hj⟩ := hAp.exists_card_eq
  have hj5 : 5 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16A : 2 ^ 4 ∣ Nat.card A := by
    rw [hj]; exact pow_dvd_pow 2 (by omega)
  have hcover : ∀ x ∈ A, x ∈ Ea ∨ x ∈ Eb := by
    intro x hx
    have hord : Nat.card (Subgroup.zpowers x) ∣ 2 ^ 4 := by
      rw [Nat.card_zpowers]
      have h2 : x ^ 2 = 1 := hA.2 x hx
      exact (orderOf_dvd_of_pow_eq_one h2).trans (by norm_num)
    obtain ⟨K, hKc, hxK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hord
      h16A (Subgroup.zpowers_le.mpr hx)
    have hKe : ElemAb K := by
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · have := hA.1.is_comm.comm ⟨a, hKA ha⟩ ⟨b, hKA hb⟩
        exact congrArg Subtype.val this
      · have := hA.2 a (hKA ha)
        rwa [sq] at this
    have hKP : K ≤ P := hKA.trans hAP
    have hxK' : x ∈ K := hxK (Subgroup.mem_zpowers x)
    have hKc16 : Nat.card K = 16 := by rw [hKc]; norm_num
    rcases hcl K hKP hKe hKc16 with rfl | rfl
    · exact Or.inl hxK'
    · exact Or.inr hxK'
  have hnEa : ¬ A ≤ Ea := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  have hnEb : ¬ A ≤ Eb := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨x, hxA, hxEa⟩ := Set.not_subset.mp hnEa
  obtain ⟨y, hyA, hyEb⟩ := Set.not_subset.mp hnEb
  have hxEb : x ∈ Eb := (hcover x hxA).resolve_left hxEa
  have hyEa : y ∈ Ea := (hcover y hyA).resolve_right hyEb
  rcases hcover (x * y) (A.mul_mem hxA hyA) with hxy | hxy
  · exact hxEa (by simpa using Ea.mul_mem hxy (Ea.inv_mem hyEa))
  · exact hyEb (by simpa using Eb.mul_mem (Eb.inv_mem hxEb) hxy)

end Abstract

section Config

theorem examExcludes_sporadic_M2x
    (s : TauCeti.SporadicName) (hs : s = .M22 ∨ s = .M23) :
    ExamExcludes (FamSporadic s) := by
  rintro G _ _ K B B' P R m h ⟨e⟩
  obtain ⟨Ab, hAb, hcard⟩ := h.toAbs.exists_bar_elem
  have hT : TwoE (↥K ⧸ Subgroup.center ↥K) := by
    rcases hs with rfl | rfl
    · exact twoE_M22.of_equiv e.symm
    · exact twoE_M23.of_equiv e.symm
  have hm := h.two_le
  have h6 : 2 ^ 6 ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact false_of_twoE hT hAb (by omega)

end Config

end CFSG.QuasithinUnique.Lin2
