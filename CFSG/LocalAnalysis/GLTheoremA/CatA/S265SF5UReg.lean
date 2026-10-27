module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5URegDiag
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_unitary det_permGL permGL_mul_diagHom_mul_inv)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {m : ℕ} {F : Type} [Field F]

theorem exists_conj_mem_ne_one (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))}
    (hXD : X ≤ primeFormD hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
    (hcard : Nat.card X = 5 ^ 2) :
    ∃ r : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F), r ≠ 1 ∧
      MulAut.conj r ∈ X := by
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  have hDI := (unitary_full_diagonal_outer_order hF (n := 5) (by norm_num) hne).2.2.1
  rw [Nat.gcd_eq_left h5] at hDI
  set D := primeFormD hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
  by_contra hall
  push Not at hall
  set φ := (QuotientGroup.mk' ((inner (primeFormP hF
    ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))).subgroupOf D)).comp
      (Subgroup.inclusion hXD)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hx
    obtain ⟨r, hr⟩ : (x : MulAut (primeFormP hF ((1 : GL (Fin 5) F) :
        Matrix (Fin 5) (Fin 5) F))) ∈ (MulAut.conj : _ →* MulAut _).range := hx
    rw [Subgroup.mem_bot]
    by_cases hr1 : r = 1
    · subst hr1
      exact Subtype.ext (by rw [← hr, map_one, Subgroup.coe_one])
    · exact (hall r hr1 (hr ▸ x.2)).elim
  haveI : Finite (D ⧸ (inner (primeFormP hF
      ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))).subgroupOf D) :=
    Nat.finite_of_card_ne_zero (by rw [hDI]; norm_num)
  have h1 := Nat.card_le_card_of_injective φ hinj
  rw [hcard, hDI] at h1
  norm_num at h1

theorem exists_inv_of_conj_mem (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))}
    (hX : IsElemAbelian 5 X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer 5 (fixSubgroup α) = ⊥)
    {r : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)}
    (hr : MulAut.conj r ∈ X) : r ^ 5 = 1 ∧ ∃ w, w * r * w⁻¹ = r⁻¹ := by
  haveI := hF.charP
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  have hZ : ∀ T : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) ⟨T, T.2.1⟩ = 1 →
        (T : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) = 1 := by
    intro T hT
    obtain ⟨c, hcN, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 hT
    have hc' : (T : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c := hc
    have hc5 : c ^ 5 = 1 := by
      have h1 : GeneralLinearGroup.det (T : GL (Fin 5) F) = 1 :=
        Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact T.2.2)
      rwa [hc', GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact (QuotientGroup.eq_one_iff _).2 ⟨c, (pow_succ_eq_one_iff_norm hF c).1 hcN, hc5, hc'⟩
  obtain ⟨S, rfl⟩ := QuotientGroup.mk_surjective r
  have hρ := primeFormConjHom_eq_conj hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) S
  have hr5 : (S : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    refine hZ _ ?_
    rw [primeFormConjHom_eq_conj, QuotientGroup.mk_pow, map_pow]
    exact hX.2 _ hr
  refine ⟨hr5, ?_⟩
  by_cases h1 : MulAut.conj (S : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) = 1
  · exact ⟨1, by rw [hZ S (hρ.trans h1)]; simp⟩
  obtain ⟨P, hP, t, htinj, ht5, hNt⟩ := exists_unitary_diag_injective hF h5 hX hnl
    (A := ⟨S, S.2.1⟩) S.2.2 (by rw [hρ]; exact hr) (by rw [hρ]; exact h1)
  obtain ⟨τ, hτ⟩ := exists_perm_apply_eq_inv htinj ht5
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by simpa [h0] using ht5 i
  have hN : (P⁻¹ * (S : GL (Fin 5) F) * P : GL (Fin 5) F) =
      diagHom 5 (fun i => Units.mk0 (t i) (ht0 i)) :=
    Units.ext (by rw [coe_diagHom]; exact hNt)
  have hdτ : (fun i => Units.mk0 (t i) (ht0 i)) ∘ τ.symm.symm =
      (fun i => Units.mk0 (t i) (ht0 i))⁻¹ := by
    funext i
    refine Units.ext ?_
    simp only [Function.comp_apply, Equiv.symm_symm, Units.val_mk0, Pi.inv_apply,
      Units.val_inv_eq_inv_val, hτ]
  have key : (permGL τ.symm : GL (Fin 5) F) * (P⁻¹ * (S : GL (Fin 5) F) * P) *
      (permGL τ.symm : GL (Fin 5) F)⁻¹ = (P⁻¹ * (S : GL (Fin 5) F) * P)⁻¹ := by
    rw [hN, permGL_mul_diagHom_mul_inv, hdτ, map_inv]
  have hM : (permGL τ.symm : GL (Fin 5) F) ∈
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    refine ⟨by rw [Units.val_one, Matrix.mul_one]; exact permGL_unitary hF τ.symm, ?_⟩
    rw [det_permGL]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> rw [h]
    · rw [Units.val_one, Int.cast_one]
    · rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have hW := conj_mem_gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) hP hM
  have hWS : (⟨_, hW⟩ : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) * S *
      (⟨_, hW⟩ : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))⁻¹ = S⁻¹ := by
    refine Subtype.ext ?_
    change P * permGL τ.symm * P⁻¹ * (S : GL (Fin 5) F) * (P * permGL τ.symm * P⁻¹)⁻¹ =
      (S : GL (Fin 5) F)⁻¹
    calc _ = P * ((permGL τ.symm : GL (Fin 5) F) * (P⁻¹ * (S : GL (Fin 5) F) * P) *
          (permGL τ.symm : GL (Fin 5) F)⁻¹) * P⁻¹ := by group
      _ = (S : GL (Fin 5) F)⁻¹ := by rw [key]; group
  refine ⟨((⟨_, hW⟩ : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
    primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)), ?_⟩
  have e := congrArg (fun g : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =>
    (g : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))) hWS
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using e

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
