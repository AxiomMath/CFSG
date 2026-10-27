module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ZCenterB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.FinalAa
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG3
public import Certificates.Certificate24215

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier
open scoped Matrix commutatorElement

theorem _root_.CFSG.EvenSporadicStandard.ThStd.ThLocalWitness2.toIn2 {G : Type} [Group G]
    {B A Aa : Subgroup G} {b : G} (W : ThLocalWitness2 B A Aa b) : ThLocalIn2 B A Aa b :=
  ⟨W.Aa_le, W.Aa_comm, W.Aa_card, W.Aa_exp, W.A_eq_sq, W.Aa_unique, W.b_mem, W.b_not_mem,
    W.b_sq, W.b_inv⟩

theorem mem_comm_of_mem {F : Type*} [Group F] {H : Subgroup F} {a b : F}
    (h : a * b * a⁻¹ * b⁻¹ ∈ H) : ⁅a, b⁆ ∈ H := h

section Elements


theorem nf_inj_zero {s : ZMod 2} {v : Vec} (h : nf s v = 1) : v = 0 := by
  rw [← nf_zero_zero] at h
  exact congrArg Prod.snd (nf_injective (a₁ := (s, v)) (a₂ := (0, 0)) h)

theorem rho_nf (s : ZMod 2) (v : Vec) : rho (nf s v) = 1 :=
  (rho_eq_one_iff (Q_le_M (nf_mem_Q s v))).2 (nf_mem_Q s v)

theorem gA_mem_M (i : Fin 4) : gA i ∈ M := by
  have h : ∀ (s : ZMod 2) (v : Vec), nf s v ∈ M := fun s v => Q_le_M (nf_mem_Q s v)
  fin_cases i
  · exact M.mul_mem (h _ _) (wordProd_mem_M _)
  · exact h _ _
  · exact M.mul_mem (M.mul_mem (h _ _) (wordProd_mem_M _)) (h _ _)
  · exact M.mul_mem (M.mul_mem (h _ _) (wordProd_mem_M _)) (h _ _)

theorem rho_gA (i : Fin 4) : rho (gA i) = rhoG i := by
  have hw : ∀ w : List Gen, rho (wordProd w) = matOfCols 8 (wordCols w) := fun w =>
    (rho_wordProd w).trans (matOfCols_wordCols w).symm
  fin_cases i
  · show rho (nf 1 (codeVec 8 50) * wordProd wG1) = matOfCols 8 (wordCols wG1)
    rw [rho_mul (Q_le_M (nf_mem_Q _ _)) (wordProd_mem_M _), rho_nf, one_mul, hw]
  · show rho (nf 0 (codeVec 8 45)) = matOfCols 8 (idCols 8)
    rw [rho_nf, matOfCols_idCols]
  · show rho (nf 1 (codeVec 8 243) * wordProd wG3 * nf 0 (codeVec 8 2)) =
      matOfCols 8 (wordCols wG3)
    rw [rho_mul (M.mul_mem (Q_le_M (nf_mem_Q _ _)) (wordProd_mem_M _)) (Q_le_M (nf_mem_Q _ _)),
      rho_mul (Q_le_M (nf_mem_Q _ _)) (wordProd_mem_M _), rho_nf, rho_nf, one_mul, mul_one, hw]
  · show rho (nf 0 (codeVec 8 73) * wordProd wG4 * nf 0 (codeVec 8 10)) =
      matOfCols 8 (wordCols wG4)
    rw [rho_mul (M.mul_mem (Q_le_M (nf_mem_Q _ _)) (wordProd_mem_M _)) (Q_le_M (nf_mem_Q _ _)),
      rho_mul (Q_le_M (nf_mem_Q _ _)) (wordProd_mem_M _), rho_nf, rho_nf, one_mul, mul_one, hw]

end Elements

section Certified


theorem exists_noncentral (hZ : HZFacts) : ∃ t ∈ S, ⁅nf 0 vZ, t⁆ ∉ AaJ := by
  obtain ⟨a, ha, i, hi⟩ := hZ.2.2.2
  obtain ⟨t, htS, ht⟩ := mem_Pt_iff_exists_S.1 (mem_Pt_iff.2 ⟨a, ha, rfl⟩)
  refine ⟨t, htS, fun hmem => ?_⟩
  obtain ⟨t', ht'⟩ := comm_nf' htS.1 0 vZ
  rw [ht'] at hmem
  have hcomm := AaJ_comm aaRel _ hmem _ (gA_mem i)
  have h1 := comm_eq_one_iff.2 hcomm
  obtain ⟨t'', ht''⟩ := comm_nf' (gA_mem_M i) t' ((rho t + 1) *ᵥ vZ)
  rw [ht''] at h1
  have h2 := nf_inj_zero h1
  rw [rho_gA, ht] at h2
  exact hi h2

theorem center_quotient_J :
    ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ AaJ) → s ∈ B := by
  have hZ : HZFacts := of_decide_eq_true Certificates.certificate24215
  intro s hs hsc
  have W := thLocalWitness_J.toLocalIn_top
  have W2 := thLocalWitness2_J.toIn2
  have hSB : ∀ x ∈ S, ⁅s, x⁆ ∈ B := fun x hx => AaJ_le_B aaRel (mem_comm_of_mem (hsc x hx))
  rcases center_mod_B hZ hs hSB with h | h
  · exact h
  · exfalso
    obtain ⟨t, htS, hnot⟩ := exists_noncentral hZ
    have hβ := ThLocalIn2.comm_mem_Aa W W2 h htS
    have hst : ⁅s, t⁆ ∈ AaJ := mem_comm_of_mem (hsc t htS)
    have hcS : nf 0 vZ ∈ S := nf_mem_S 0 vZ
    have hconj : ∀ x ∈ AaJ, nf 0 vZ * x * (nf 0 vZ)⁻¹ ∈ AaJ := fun x hx =>
      W2.conj_mem_of_conj_B (W.conj_mem_B_of_normalizes_S (mem_iff_conj_of_mem hcS)) x hx
    have e : ⁅s, t⁆ = nf 0 vZ * ⁅(nf 0 vZ)⁻¹ * s, t⁆ * (nf 0 vZ)⁻¹ * ⁅nf 0 vZ, t⁆ := by
      have h := comm_mul_left_eq (nf 0 vZ) ((nf 0 vZ)⁻¹ * s) t
      rwa [mul_inv_cancel_left] at h
    apply hnot
    have h3 : nf 0 vZ * ⁅(nf 0 vZ)⁻¹ * s, t⁆ * (nf 0 vZ)⁻¹ ∈ AaJ := hconj _ hβ
    rw [e] at hst
    have := AaJ.mul_mem (AaJ.inv_mem h3) hst
    rwa [inv_mul_cancel_left] at this

end Certified

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
