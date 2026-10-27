module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.EqTwoRank
public import CFSG.LieType.SeitzGeneration.ExcOuterSplit
import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6Three
import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix

public section

namespace CFSG.AGLEmbedding.SeitzEqTwo

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Chevalley TauCeti CFSG.TauCetiBridge
open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube (dvd_sq_add_add_one_of_orderOf_eq_three
  dvd_sq_sub_add_one_of_orderOf_eq_six)

theorem not_dvd_of_five_le {p m : ℕ} (hp5 : 5 ≤ p) (hm : m = 1 ∨ m = 2 ∨ m = 3) : ¬ p ∣ m := by
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

section Plane


theorem exists_plane_F4 {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcnt : degCount Tag.F4 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ A : Subgroup (adjointGroup .F4 k), IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  rcases degCount_F4_eq_two hcnt with h3 | h4 | h6
  · exact (sylowTorus_F4_three k hp hp3
      (dvd_sq_add_add_one_of_orderOf_eq_three hp h3).1).exists_elemAbelian
  · exact (sylowTorus_F4_four k hp hp3 (dvd_sq_add_one_of_orderOf_eq_four hp h4)).exists_elemAbelian
  · exact (sylowTorus_F4_six k hp hp3
      (dvd_sq_sub_add_one_of_orderOf_eq_six hp h6).1).exists_elemAbelian

theorem exists_plane_E6 {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E6 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ A : Subgroup (adjointGroup .E6 k), IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  rcases degCount_E6_eq_two hcnt with h4 | h6
  · exact (sylowTorus_E6_four k hp h4).exists_elemAbelian
  · exact (sylowTorus_E6_six k hp h6).exists_elemAbelian

theorem exists_plane_E7 {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ A : Subgroup (adjointGroup .E7 k), IsElemAbelian p A ∧ Nat.card A = p ^ 2 :=
  (sylowTorus_E7_four k hp (degCount_E7_eq_two hcnt)).exists_elemAbelian

theorem exists_plane_E8 {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ A : Subgroup (adjointGroup .E8 k), IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  rcases degCount_E8_eq_two hcnt with h5 | h8 | h10 | h12
  · exact (sylowTorus_E8_five k hp h5).exists_elemAbelian
  · exact (sylowTorus_E8_eight k hp h8).exists_elemAbelian
  · exact (sylowTorus_E8_ten k hp h10).exists_elemAbelian
  · exact (sylowTorus_E8_twelve k hp h12).exists_elemAbelian

end Plane

section Residuals


theorem seitzExcOuterNarrowF4EqTwo_holds : SeitzExcOuterNarrowF4EqTwo := by
  rintro ⟨d, hv⟩ p hp hp2 - - E hE - ⟨hout, ⟨-, hnar⟩, -, hp5, q, rfl, -, hcnt⟩
  exfalso
  have hp3 : 3 < p := by omega
  rcases hnar with hR1 | hPR
  · exact SeitzCyc.not_rankLE1_cat_F4_of_eqTwo q hv hp hp3 hcnt hR1
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
    have hq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
    refine not_planeRank2_of_fieldDescent q.prime_p q.exponent_pos hq hp
      (fieldDescentAt_F4 q.prime_p q.exponent_pos hq hp hp2) (fun k hk => ?_) e hE hout hPR
    refine exists_plane_F4 hp hp3 ?_
    rw [hk, hK]
    exact hcnt

theorem seitzExcOuterNarrowE6EqTwo_holds : SeitzExcOuterNarrowE6EqTwo := by
  rintro ⟨d, hv⟩ p hp hp2 - - E hE - ⟨hout, ⟨-, hnar⟩, -, hp5, q, rfl, -, hcnt⟩
  exfalso
  rcases hnar with hR1 | hPR
  · exact SeitzCyc.not_rankLE1_cat_E6_of_eqTwo q hv hp hcnt hR1
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    have hq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hdet : ¬ p ∣ Tag.E6.cartan.det.natAbs := by
      rw [det_cartan_E6]
      exact not_dvd_of_five_le hp5 (by decide)
    refine not_planeRank2_of_fieldDescent q.prime_p q.exponent_pos hq hp
      (fieldDescentAt_E (Or.inl rfl) q.exponent_pos hq hp hp2 hdet) (fun k hk => ?_) e hE hout hPR
    refine exists_plane_E6 hp ?_
    rw [hk, hK]
    exact hcnt

theorem seitzExcOuterNarrowE7EqTwo_holds : SeitzExcOuterNarrowE7EqTwo := by
  rintro ⟨d, hv⟩ p hp hp2 - - E hE - ⟨hout, ⟨-, hnar⟩, -, hp5, q, rfl, -, hcnt⟩
  exfalso
  rcases hnar with hR1 | hPR
  · exact SeitzCyc.not_rankLE1_cat_E7_of_eqTwo q hv hp hcnt hR1
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
    have hq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hdet : ¬ p ∣ Tag.E7.cartan.det.natAbs := by
      rw [det_cartan_E7]
      exact not_dvd_of_five_le hp5 (by decide)
    refine not_planeRank2_of_fieldDescent q.prime_p q.exponent_pos hq hp
      (fieldDescentAt_E (Or.inr (Or.inl rfl)) q.exponent_pos hq hp hp2 hdet) (fun k hk => ?_) e
      hE hout hPR
    refine exists_plane_E7 hp ?_
    rw [hk, hK]
    exact hcnt

theorem seitzExcOuterNarrowE8EqTwo_holds : SeitzExcOuterNarrowE8EqTwo := by
  rintro ⟨d, hv⟩ p hp hp2 - - E hE - ⟨hout, ⟨-, hnar⟩, -, hp5, q, rfl, -, hcnt⟩
  exfalso
  rcases hnar with hR1 | hPR
  · exact SeitzCyc.not_rankLE1_cat_E8_of_eqTwo q hv hp hcnt hR1
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
    have hq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hdet : ¬ p ∣ Tag.E8.cartan.det.natAbs := by
      rw [det_cartan_E8]
      exact not_dvd_of_five_le hp5 (by decide)
    refine not_planeRank2_of_fieldDescent q.prime_p q.exponent_pos hq hp
      (fieldDescentAt_E (Or.inr (Or.inr rfl)) q.exponent_pos hq hp hp2 hdet) (fun k hk => ?_) e
      hE hout hPR
    refine exists_plane_E8 hp ?_
    rw [hk, hK]
    exact hcnt

end Residuals

end CFSG.AGLEmbedding.SeitzEqTwo
