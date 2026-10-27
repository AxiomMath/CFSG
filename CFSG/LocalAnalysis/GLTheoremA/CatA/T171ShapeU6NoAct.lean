module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Frame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType CFSG.StandardType.TableBUE
open Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)

theorem u6NoActModel_holds : U6NoActModel := by
  intro n K _ _ h hpq Ab hAb hAbD hcard ⟨a, ha, M, hM, l, hM3, hl, haM⟩ V hV hAV
  by_contra hVne
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, Nat.mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro he
    exact absurd (congrArg Prod.fst he) (by norm_num)
  obtain ⟨P, -, hPd⟩ :=
    LID63.exists_unitary_frame63 (n := n) hK hpq hAb hAbD hcard ⟨V, hVne, hV, hAV⟩
  obtain ⟨M', hM', hMd, haM'⟩ := hPd a ha
  have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer (d := 6) h hM
  have hM'N : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer (d := 6) h hM'
  have hEq : TableB.projConj (unitarySU 2 n K 6) ⟨M', hM'N⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ := haM'.symm.trans haM
  have hproj : TableB.projConj (unitarySU 2 n K 6)
      ((⟨M', hM'N⟩ : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))))⁻¹ *
        ⟨M, hMN⟩) = 1 := by
    rw [map_mul, map_inv, hEq, inv_mul_cancel]
  have hscalar := mem_scalars_of_projConj_eq_one h hK (d := 6) (by norm_num) hdq
    Nat.prime_three hpq hproj
  obtain ⟨c, hc⟩ := hscalar
  have hc' : M'⁻¹ * M = GeneralLinearGroup.scalar (Fin 6) c := by
    simpa using hc.symm
  have hM_eq : M = M' * GeneralLinearGroup.scalar (Fin 6) c := by
    calc M = M' * (M'⁻¹ * M) := by group
      _ = M' * GeneralLinearGroup.scalar (Fin 6) c := by rw [hc']
  have hcube : (M' * GeneralLinearGroup.scalar (Fin 6) c) ^ 3 =
      M' ^ 3 * GeneralLinearGroup.scalar (Fin 6) (c ^ 3) := by
    rw [(commute_scalar c M').mul_pow, map_pow]
  have hM'3 : M' ^ 3 = GeneralLinearGroup.scalar (Fin 6) (l * (c ^ 3)⁻¹) := by
    have h1 : GeneralLinearGroup.scalar (Fin 6) l =
        M' ^ 3 * GeneralLinearGroup.scalar (Fin 6) (c ^ 3) := by
      rw [← hcube, ← hM_eq, hM3]
    calc M' ^ 3 = (M' ^ 3 * GeneralLinearGroup.scalar (Fin 6) (c ^ 3)) *
          (GeneralLinearGroup.scalar (Fin 6) (c ^ 3))⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 6) l *
          (GeneralLinearGroup.scalar (Fin 6) (c ^ 3))⁻¹ := by rw [← h1]
      _ = GeneralLinearGroup.scalar (Fin 6) (l * (c ^ 3)⁻¹) := by
        rw [← map_inv, ← map_mul]
  obtain ⟨σ, hDσ⟩ := exists_diagHom_of_isDiag hMd
  have hD3 : (P⁻¹ * M' * P : GL (Fin 6) K) ^ 3 =
      GeneralLinearGroup.scalar (Fin 6) (l * (c ^ 3)⁻¹) := by
    have hconj : (P⁻¹ * M' * P : GL (Fin 6) K) ^ 3 = P⁻¹ * M' ^ 3 * P := by
      simpa only [inv_inv] using conj_pow (a := P⁻¹) (b := M') (i := 3)
    rw [hconj, hM'3, mul_assoc, (commute_scalar (l * (c ^ 3)⁻¹) P).eq.symm,
      ← mul_assoc, inv_mul_cancel, one_mul]
  have hdiag3 : diagHom 6 (σ ^ 3) =
      GeneralLinearGroup.scalar (Fin 6) (l * (c ^ 3)⁻¹) := by
    have h := hD3
    rw [hDσ, ← map_pow] at h
    exact h
  have hconst : GeneralLinearGroup.scalar (Fin 6) (l * (c ^ 3)⁻¹) =
      diagHom 6 (fun _ => l * (c ^ 3)⁻¹) := by
    apply Units.ext
    rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hσ3 : σ ^ 3 = fun _ => l * (c ^ 3)⁻¹ :=
    diagHom_injective (K := K) 6 (hdiag3.trans hconst)
  have hunit : (σ ⟨0, by norm_num⟩) ^ 3 = l * (c ^ 3)⁻¹ := by
    have h := congrFun hσ3 ⟨0, by norm_num⟩
    simpa only [Pi.pow_apply] using h
  exact hl (σ ⟨0, by norm_num⟩ * c) (by
    rw [mul_pow, hunit, mul_assoc, inv_mul_cancel, mul_one])

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
