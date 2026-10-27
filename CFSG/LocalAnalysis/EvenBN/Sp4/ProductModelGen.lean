module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase
public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace ProductModel

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterWeyl
  (weylElt weylMat diagSL coe_diagSL glMat_sHom_one glMat_sHom_two)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
  (weylSL2 upperSL2 sHom_weylSL2 sHom_upper_le_antiUnipotent upperSL2_sup_conj_weyl)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rootA_le_antiUnipotent (i : Axis) : rootA K i ≤ antiUnipotent K := by
  cases i
  · exact radA1_le_antiUnipotent
  · exact radA2_le_antiUnipotent

theorem mem_rootC_one_iff {g : antiSp K} :
    g ∈ rootC K Axis.one ↔ (minorAut K).symm g ∈ rootC K Axis.two := by
  have h := mem_centralizer_map (minorAut K) (rootU₂ K) g
  rw [← rootU₁_eq_map] at h
  exact h

theorem rootC_decomp (i : Axis) {g : antiSp K} (hg : g ∈ rootC K i) :
    ∃ a ∈ rootA K i, ∃ M : SL₂ K, g = a * sHom K i M := by
  cases i
  · obtain ⟨v, c, M, hgM⟩ := exists_aElt_mul_sElt (mem_rootC_one_iff.1 hg)
    refine ⟨minorAut K (aElt v c), ?_, M, ?_⟩
    · show minorAut K (aElt v c) ∈ radA1 K
      rw [radA1_eq_map]
      exact ⟨aElt v c, aElt_mem_radA2 v c, rfl⟩
    · calc g = minorAut K ((minorAut K).symm g) := ((minorAut K).apply_symm_apply g).symm
        _ = minorAut K (aElt v c) * sHom K Axis.one M := by rw [hgM, map_mul]; rfl
  · obtain ⟨v, c, M, hgM⟩ := exists_aElt_mul_sElt hg
    exact ⟨aElt v c, aElt_mem_radA2 v c, M, hgM⟩

theorem rootC_le_antiUnipotent_sup (i : Axis) :
    rootC K i ≤ antiUnipotent K ⊔ (antiUnipotent K).map (MulAut.conj (weylElt K i)).toMonoidHom := by
  intro g hg
  obtain ⟨a, ha, M, rfl⟩ := rootC_decomp i hg
  refine mul_mem (mem_sup_left (rootA_le_antiUnipotent i ha)) ?_
  have hle : upperSL2 K ⊔ (upperSL2 K).map (MulAut.conj (weylSL2 K)).toMonoidHom ≤
      (antiUnipotent K ⊔
        (antiUnipotent K).map (MulAut.conj (weylElt K i)).toMonoidHom).comap (sHom K i) := by
    refine sup_le (fun x hx => mem_sup_left (sHom_upper_le_antiUnipotent i ⟨x, hx, rfl⟩)) ?_
    rintro _ ⟨x, hx, rfl⟩
    have e : sHom K i ((MulAut.conj (weylSL2 K)).toMonoidHom x) =
        (MulAut.conj (weylElt K i)).toMonoidHom (sHom K i x) := by
      simp [MulAut.conj_apply, map_mul, map_inv, sHom_weylSL2]
    rw [Subgroup.mem_comap, e]
    exact mem_sup_right ⟨sHom K i x, sHom_upper_le_antiUnipotent i ⟨x, hx, rfl⟩, rfl⟩
  refine hle ?_
  rw [upperSL2_sup_conj_weyl]
  exact mem_top M

theorem dElt_eq_sHom_mul (l : Kˣ) :
    dElt l = sHom K Axis.one (diagSL l) * sHom K Axis.two (diagSL l) := by
  apply antiSp_ext
  have hl : (l : K) * ((l⁻¹ : Kˣ) : K) = 1 := Units.mul_inv l
  change glMat (dElt l : GL (Fin 4) K) = glMat (sHom K Axis.one (diagSL l) : GL (Fin 4) K) *
    glMat (sHom K Axis.two (diagSL l) : GL (Fin 4) K)
  rw [glMat_dElt, glMat_sHom_one, glMat_sHom_two, coe_diagSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, sMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem firstCol_inv_mul {g q : antiSp K} {c : K} (h : ∀ j, mat g j 0 = c * mat q j 0) :
    FirstCol (q⁻¹ * g) := by
  have key : ∀ i, mat (q⁻¹ * g) i 0 = c * (1 : Matrix (Fin 4) (Fin 4) K) i 0 := fun i => by
    have e1 : mat (q⁻¹ * g) i 0 = ∑ j, mat q⁻¹ i j * mat g j 0 := by
      rw [mat_mul, Matrix.mul_apply]
    have e2 : (1 : Matrix (Fin 4) (Fin 4) K) i 0 = ∑ j, mat q⁻¹ i j * mat q j 0 := by
      rw [← Matrix.mul_apply, ← mat_mul, inv_mul_cancel, mat_one]
    rw [e1, e2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h j]; ring
  exact ⟨by rw [key]; simp, by rw [key]; simp, by rw [key]; simp⟩

theorem mem_of_firstCol_proportional {H : Subgroup (antiSp K)} (hH : ∀ g, FirstCol g → g ∈ H)
    {g q : antiSp K} (hq : q ∈ H) (c : K) (h : ∀ j, mat g j 0 = c * mat q j 0) : g ∈ H := by
  have := mul_mem hq (hH _ (firstCol_inv_mul h))
  rwa [mul_inv_cancel_left] at this

theorem rootC_sup_rootC (hK : 4 ≤ Nat.card K) : rootC K Axis.one ⊔ rootC K Axis.two = ⊤ := by
  set H := rootC K Axis.one ⊔ rootC K Axis.two
  have hC1 : rootC K Axis.one ≤ H := le_sup_left
  have hC2 : rootC K Axis.two ≤ H := le_sup_right
  have hS : ∀ (i : Axis) (M : SL₂ K), sHom K i M ∈ H := fun i M => by
    cases i
    · exact hC1 ((rootAxisStructure_one hK).s_mem_C M)
    · exact hC2 ((rootAxisStructure_two hK).s_mem_C M)
  have hW : ∀ i : Axis, weylElt K i ∈ H := fun i => by
    rw [← sHom_weylSL2 i]
    exact hS i _
  have hA1 : radA1 K ≤ H := fun x hx => hC1 ((rootAxisStructure_one hK).A_le_C hx)
  have hA2 : radA2 K ≤ H := fun x hx => hC2 ((rootAxisStructure_two hK).A_le_C hx)
  have hline : ∀ g : antiSp K, FirstCol g → g ∈ H := by
    intro g hg
    obtain ⟨v, c, l, M, rfl⟩ := exists_normalForm hg
    refine mul_mem (hA2 (aElt_mem_radA2 v c)) (mul_mem ?_ (hS Axis.two M))
    rw [dElt_eq_sHom_mul]
    exact mul_mem (hS Axis.one _) (hS Axis.two _)
  refine eq_top_iff.2 fun g _ => ?_
  by_cases h3 : mat g 3 0 = 0
  · by_cases h2 : mat g 2 0 = 0
    · by_cases h1 : mat g 1 0 = 0
      · exact hline g ⟨h1, h2, h3⟩
      ·
        refine mem_of_firstCol_proportional hline
          (q := uElt (mat g 0 0 / mat g 1 0) 0 0 0 * weylElt K Axis.one)
          (mul_mem (hA2 ⟨_, 0, 0, rfl⟩) (hW Axis.one)) (mat g 1 0) ?_
        intro j
        fin_cases j <;> simp [mat_mul, mat, weylElt, glMat_uElt, weylMat, uMat, Matrix.mul_apply,
          Fin.sum_univ_four, h2, h3] <;> field_simp
    ·
      refine mem_of_firstCol_proportional hline
        (q := uElt 0 (mat g 0 0 / mat g 2 0) 0 (mat g 1 0 / mat g 2 0) *
          (weylElt K Axis.two * weylElt K Axis.one))
        (mul_mem (hA1 ⟨_, 0, _, rfl⟩) (mul_mem (hW Axis.two) (hW Axis.one))) (mat g 2 0) ?_
      intro j
      fin_cases j <;> simp [mat_mul, mat, weylElt, glMat_uElt, weylMat, uMat, Matrix.mul_apply,
        Fin.sum_univ_four, h3] <;> field_simp
  ·
    refine mem_of_firstCol_proportional hline
      (q := uElt (mat g 2 0 / mat g 3 0) (mat g 1 0 / mat g 3 0) (mat g 0 0 / mat g 3 0) 0 *
        (weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one))
      (mul_mem (hA2 ⟨_, _, _, rfl⟩) (mul_mem (mul_mem (hW Axis.one) (hW Axis.two)) (hW Axis.one)))
      (mat g 3 0) ?_
    intro j
    fin_cases j <;> simp [mat_mul, mat, weylElt, glMat_uElt, weylMat, uMat, Matrix.mul_apply,
      Fin.sum_univ_four] <;> field_simp

end ProductModel

end CFSG.LocalAnalysis.EvenBN.Sp4
