module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXUI
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXUG
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXT

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedLayer P211
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

variable {Q : ℕ → Prop}

theorem compOrd_psu5 {J : Type} [Group J] {p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU 5 p f) (hm : Blueprint.LieModel J .PSU 5 p f)
    (hQ2 : Q (Open.ordA 1 (p ^ f))) (hQ3 : Q (Open.ordTwistedA 2 (p ^ f)))
    (hQ4 : Q (Open.ordTwistedA 3 (p ^ f))) (hQS : Q (Open.ordBC 2 (p ^ f))) {α : MulAut J}
    (hα : orderOf α = 2) : CompOrd Q (fixedSubgroup α) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hq : ¬(5 = 3 ∧ p ^ f = 2) := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC (by norm_num) hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC (by norm_num) hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  refine CompOrd.of_mulEquiv (CatLeafProof.fixedSubgroupCongrEquiv ψ α) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact CompOrd.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (compOrd_inner_psu h hp2 A hord hQ2 hQ3 hQ4)
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact CompOrd.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (compOrd_graph_psu rfl h hp2 A φ hφ hord hQS)

theorem p211For_U5 :
    P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
      Blueprint.LieModel G .PSU 5 p f := by
  intro X _ _ hsimp hC ⟨p', f', hp', hf', hq4, hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  exfalso
  have hp2' : p' ≠ 2 := by
    rintro rfl
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod] at hq4
    have : 2 ^ g % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : 2 ^ g % 4 <;> omega
  have hstated := GH74.statedClassicalModel_of_lieModel (by norm_num) hLie
  obtain ⟨-, hsolv⟩ := unitary_classical_model_schreier hstated
  obtain ⟨N, hN⟩ := exists_derivedSeries_le_of_isSolvable (OuterAutomorphisms.inner _) hsolv
  have hKF : K ≤ generalizedFitting X :=
    le_fstar_of_perfect hC (MulEquiv.refl _) hN (commutator_eq_of_isPComp hKC hK)
  obtain ⟨-, hKv, hFv⟩ := p211_two_adic hp hp2 hf hJt hDJ hDsyl hbound hKt
  have hq'odd : Odd (p' ^ f') := ⟨p' ^ f' / 2, by omega⟩
  have hq'5 : 5 ≤ p' ^ f' := by
    have h3 : 3 ≤ p' ^ f' := le_trans (by have := hp'.two_le; omega)
      (Nat.le_self_pow (by omega) p')
    omega
  have hF : padicValNat 2 (Nat.card (generalizedFitting X)) =
      2 * padicValNat 2 ((p' ^ f') ^ 2 - 1) + 3 := by
    rw [GH74.card_of_lieModel_PSU (by norm_num) hp2' hLie]
    exact v2_ordTwistedA_four hq4 hq'5
  have hQS := CatLeaf.fixedTwoComponentsQuasisimple_psu hp2' hstated
  obtain ⟨β, hβ, L, hL, hLv⟩ := exists_fixed_component hC hQS hb hb1 hKC hK hKF
    (center_socle_eq_bot hp hp2 hf hKt)
  have h1 := v2_ordA_one hq'odd (by omega)
  have h2 := v2_ordTwistedA_two hq4 hq'5
  have h3 := v2_ordTwistedA_three hq4 hq'5
  have h4 := v2_ordBC hq'odd (by omega)
  have hcls := compOrd_psu5 (Q := fun v => ∀ m', padicValNat 2 ((p' ^ f') ^ 2 - 1) + 1 ≤ m' →
      padicValNat 2 v ≠ 2 * m') hp2' hstated.1 hLie
    (fun m' hm' => by omega) (fun m' hm' => by omega) (fun m' hm' => by omega)
    (fun m' hm' => by omega) hβ
  exact hcls L hL (padicValNat 2 ((p ^ f) ^ 2 - 1)) (by omega) (by rw [hLv, hKv])

end P211X

end CFSG.ComponentClassification.GSThmB
