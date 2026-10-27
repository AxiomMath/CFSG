module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore


theorem psl34_autModel : AutModel PSL3Four.S PSL3Four.R := by
  obtain ⟨φ, hφ, -⟩ := PSL3Four.full_automorphism_action
  exact autModel_of_equiv PSL3Four.S_le_R φ hφ

theorem psl34_coset {t : Equiv.Perm (Fin 42)} (ht : t ∈ PSL3Four.R) (ht2 : orderOf t = 2)
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ PSL3Four.S) (hts : orderOf (t * s) = 2) :
    ∃ c ∈ PSL3Four.S, c⁻¹ * t * c = t * s := by
  have h1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have h2 : t * s * (t * s) = 1 := by rw [← pow_two, ← hts, pow_orderOf_eq_one]
  have h3 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; omega
  have h4 : t * s ≠ 1 := fun h => by rw [h, orderOf_one] at hts; omega
  obtain ⟨y, hy, hyt⟩ := CatFactsL4U4.conj_of_mul_mem_S ht
    (PSL3Four.R.mul_mem ht (PSL3Four.S_le_R hs)) h1 h2 h3 h4 (by rwa [inv_mul_cancel_left])
  exact ⟨y⁻¹, PSL3Four.S.inv_mem hy, by rw [inv_inv]; exact hyt⟩

theorem l34 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 3 2 2 := by
  intro G _ _ N hN hC hY α J hα hJN hJα _ _ _ hZ _
  have := hN
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  have hM := psl34_autModel
  obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC θ hα
  exact concl_of_coset hα hJN hJα hZ
    (coset_of_autModel hM hC θ fun _ hs hts => psl34_coset hmem hord hs hts)

end CFSG.ComponentClassification.GSThmB.CF23I
