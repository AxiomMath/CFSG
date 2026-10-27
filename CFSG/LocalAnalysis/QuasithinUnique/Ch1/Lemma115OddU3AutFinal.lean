module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL2Aut

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank

theorem oddAutInner_psu3 {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel K .PSU 3 p 1) (β : K ≃* K) (hβ : ∀ x, β (β x) = x)
    (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by rw [hcard]; ring⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let ψ : K ≃* hypPSU h 1 1 := e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  have hα2 : transAut ψ β * transAut ψ β = 1 := transAut_mul_self ψ β hβ
  by_cases hα1 : transAut ψ β = 1
  · refine ⟨1, fun x => ?_⟩
    have hx : β x = x := by
      apply ψ.injective
      rw [← transAut_apply, hα1]
      rfl
    rw [hx, inv_one, one_mul, mul_one]
  · have hord : orderOf (transAut ψ β) = 2 := orderOf_eq_prime (by rwa [sq]) hα1
    obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ :=
      (odd_unitary_automorphism_semilinear_representation h hp2 (le_refl 1) (le_refl 1)
        (by norm_num)).2.2.2 _ hord
    rcases hσ with rfl | hσ
    · have hin := inner_of_sigma_id h hA hx (hid rfl)
      rw [hΦ] at hin
      exact isInnerAut_of_transAut_mem_inner ψ β hin
    · exfalso
      obtain ⟨c, hc0, hAc⟩ := hbar hσ
      obtain ⟨P, hP⟩ := hP
      obtain ⟨P', hP'coe⟩ : ∃ P' : Sylow 2 (hypPSU h 1 1),
          (P' : Subgroup (hypPSU h 1 1)) = (P : Subgroup K).map ψ.toMonoidHom :=
        ⟨P.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, rfl⟩
      refine not_card_dvd_of_sylow_hyp h hp2 P' (card_dvd_of_fixed h hp2 hA hc0 hAc hσ hx
        (P' : Subgroup (hypPSU h 1 1)) fun y hy => ?_)
      rw [hΦ]
      rw [hP'coe] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      change transAut ψ β (ψ s) = ψ s
      rw [transAut_apply, hP s hs]

theorem oddDegreeThreeAutInner : OddDegreeThreeAutInner := by
  intro K _ _ p hp hp2 hm β hβ hP _
  rcases hm with hm | hm
  · exact oddAutInner_psl3 hp hp2 hm β hβ hP
  · exact oddAutInner_psu3 hp hp2 hm β hβ hP

end CFSG.QuasithinUnique.Ch1
