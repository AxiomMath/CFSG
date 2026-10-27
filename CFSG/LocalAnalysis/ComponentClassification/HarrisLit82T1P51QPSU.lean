module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUPairThm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_separatingLeft)

variable {K : Type} [Field K]

theorem eigP_neg {n : ℕ} (l : K) (A : Module.End K (Fin n → K)) : eigP (-l) A = eigM l A := by
  ext v
  simp only [eigP, eigM, LinearMap.mem_ker, invSMulOp, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, inv_neg, neg_smul]
  rw [← neg_add', neg_eq_zero]

theorem eigM_neg {n : ℕ} (l : K) (A : Module.End K (Fin n → K)) : eigM (-l) A = eigP l A := by
  ext v
  simp only [eigP, eigM, LinearMap.mem_ker, invSMulOp, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, inv_neg, neg_smul]
  rw [neg_add_eq_sub, ← neg_sub, neg_eq_zero]

theorem fAt_psu {p f n : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f)
    (hn : 3 ≤ n) {X : Type} [Group X] (e₀ : X ≃* primeFormP h (idGram K n)) {z : X}
    (hz : orderOf z = 2) : FAt X z := by
  have htwo := two_ne_zero_of_odd h hp2
  have hπ := psuCover_surjective h e₀
  have hker := psuCover_eq_one_iff h e₀
  obtain ⟨a, rfl⟩ := hπ z
  have ha2 : a * a ∈ normOneScalars h (gramSU h (idGram K n)) n := (hker _).mp (by
    rw [map_mul, ← pow_two, ← hz, pow_orderOf_eq_one])
  have ha1 : a ∉ normOneScalars h (gramSU h (idGram K n)) n := fun h1 => by
    rw [(hker a).mpr h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Fin n → K) := Function.nontrivial
  obtain ⟨⟨l, hl0, hAA, hlN⟩, hA⟩ := involution_lift_sq hp2 (idForm_separatingLeft h n)
    (orderOf_mk_suOp h a ha2 ha1)
  set A := unitaryOp (suOp h a) with hAdef
  rcases hlN with hlN | hlN
  · have hc := isCompl_ker_sub_one_ker_add_one htwo (invSMulOp_mul_self hl0 hAA)
    have hsum : finrank K (eigP l A) + finrank K (eigM l A) = n := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      rwa [Module.finrank_fin_fun] at this
    obtain ⟨hP, hM⟩ := eigen_ne_bot htwo hl0 hAA hA
    have hr : 1 ≤ finrank K (eigP l A) :=
      Nat.one_le_iff_ne_zero.mpr fun h0 => hP (Submodule.finrank_eq_zero.mp h0)
    have hs : 1 ≤ finrank K (eigM l A) :=
      Nat.one_le_iff_ne_zero.mpr fun h0 => hM (Submodule.finrank_eq_zero.mp h0)
    by_cases hs2 : 2 ≤ finrank K (eigM l A)
    · obtain ⟨h1, h2⟩ := evenCent_unitary_split h hp2 hq (psuCover h e₀) hπ hker a hl0 hAA hlN
        hr hs2
      exact fAt_of_evenCent h1 h2
    · have hAA' : A * A = ((-l) ^ 2) • 1 := by rw [neg_sq]; exact hAA
      have hlN' : h.norm (-l) = 1 := by
        rw [UnitaryFieldData.norm, map_neg, neg_mul_neg]
        exact hlN
      have hr' : 1 ≤ finrank K (eigP (-l) A) := by rw [eigP_neg]; exact hs
      have hs' : 2 ≤ finrank K (eigM (-l) A) := by rw [eigM_neg]; omega
      obtain ⟨h1, h2⟩ := evenCent_unitary_split h hp2 hq (psuCover h e₀) hπ hker a
        (neg_ne_zero.mpr hl0) hAA' hlN' hr' hs'
      exact fAt_of_evenCent h1 h2
  · obtain ⟨h1, h2⟩ := evenCent_unitary_paired h hp2 hq (psuCover h e₀) hπ hker a hl0 hAA hlN
      hn
    exact fAt_of_evenCent h1 h2

theorem famF_psu : FamF .PSU := by
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  have hadm : StatedLieAdmissible .PSU n p f := by
    rcases hX with ⟨-, h⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
    · exact h.1
    all_goals exact absurd hc (by decide)
  obtain ⟨K, _, h, ⟨e₀⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hX
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h5 : 5 ≤ p ^ f := by
    have h3 : 3 ≤ p ^ f := (show 3 ≤ p by have := hp.two_le; omega).trans
      (Nat.le_self_pow (by omega) p)
    obtain ⟨t, ht⟩ : Odd (p ^ f) := hpodd.pow
    omega
  exact fAt_psu h hp2 (by omega) hn e₀ hz

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
