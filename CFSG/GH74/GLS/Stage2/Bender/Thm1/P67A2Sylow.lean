module

public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem factorization_three_g2_eq_sl3 {q : ℕ} (h3 : 3 ∣ q - 1) (hq : 2 ≤ q) :
    (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 =
      (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))).factorization 3 := by
  have hq3 : q % 3 = 1 := by omega
  have h1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have h2 : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  have h6 : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have e : q ^ 6 = (q ^ 3) ^ 2 := by ring
    rw [e]
    obtain ⟨a, ha⟩ : ∃ a, q ^ 3 = a + 1 := ⟨q ^ 3 - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  have hdecomp : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) =
      (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) * (q ^ 3 * (q ^ 3 + 1)) := by
    rw [h6]
    have e : q ^ 6 = q ^ 3 * q ^ 3 := by ring
    rw [e]
    ring
  have hnd : ¬ 3 ∣ q ^ 3 * (q ^ 3 + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · have hp : q ^ 3 % 3 = 1 := by
        rw [Nat.pow_mod, hq3]
      omega
  have hA : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 0 := by
    have : 0 < q ^ 2 - 1 := by omega
    have : 0 < q ^ 3 - 1 := by omega
    positivity
  have hB : q ^ 3 * (q ^ 3 + 1) ≠ 0 := by positivity
  rw [hdecomp, Nat.factorization_mul hA hB, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

open scoped Pointwise in
theorem exists_conj_le_sylow_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G) (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ y : G, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, ?_⟩
  have hgS : (g • S : Sylow p G).toSubgroup = S.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgS
  rw [hgS]
  exact Subgroup.map_mono hES

open scoped MatrixGroups in
theorem exists_conj_le_range_of_three_dvd_sub_one {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1)
    (ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K))
    (hι : Function.Injective ι)
    (E : Subgroup ↥(adjointGroup .G2 K)) (hE : IsPGroup 3 E) :
    ∃ y : ↥(adjointGroup .G2 K), E.map (MulAut.conj y).toMonoidHom ≤ ι.range := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order K rfl
  have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [LinearFlag.card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
      Finset.prod_pair (by norm_num)]
  obtain ⟨P⟩ : Nonempty (Sylow 3 (Matrix.SpecialLinearGroup (Fin 3) K)) := inferInstance
  let Q : Sylow 3 ↥(adjointGroup .G2 K) := Sylow.ofCard ((P : Subgroup _).map ι) (by
    rw [Subgroup.card_map_of_injective hι, Sylow.card_eq_multiplicity P, hC, hS,
      factorization_three_g2_eq_sl3 h3 hq])
  obtain ⟨y, hy⟩ := exists_conj_le_sylow_of_isPGroup Q E hE
  refine ⟨y, hy.trans ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_le_range ι _

end CFSG.GH74.GLS.Stage2.Bender.Thm1
