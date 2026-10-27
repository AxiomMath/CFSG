module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalMax
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSolv
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLTwoEight
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeAltSix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem alternating_catalog_facts {n : ℕ} (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) ∧
      (∃ a b : alternatingGroup (Fin n), a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (alternatingGroup (Fin n))) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  refine ⟨inferInstance, nonabelian_of_simple_of_sq_dvd Nat.prime_two ?_, ?_⟩
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial (show 4 ≤ n by omega)
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin, hm, h4,
      show (4 : ℕ).factorial = 24 from rfl]
    exact ⟨3 * m, by omega⟩
  · have h4 : Nat.card (Outer (alternatingGroup (Fin n))) ∣ 2 ^ 2 := by
      simpa using CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    haveI : Finite (Outer (alternatingGroup (Fin n))) :=
      Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
    haveI := (IsPGroup.of_card hk).isNilpotent
    infer_instance

theorem altSix_isSolvable_of_sylow_le (T : Sylow 3 (alternatingGroup (Fin 6)))
    (H : Subgroup (alternatingGroup (Fin 6))) (hTH : (T : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hK : IsAltTwoP 3 (alternatingGroup (Fin 6)) := ⟨MulEquiv.refl _⟩
  haveI := CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltSix.isSolvable_normalizer hK T
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective
    (CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltSix.le_normalizer_of_le hK T hTH hH))

theorem threeFourTwoNoneAt_altSix (h : 5 ≤ 6) :
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.alternating 6 h).Group := by
  obtain ⟨hs, hnab, hout⟩ := alternating_catalog_facts h
  exact threeFourTwoNoneAt_of_sylow_le_isSolvable hs hnab hout altSix_isSolvable_of_sylow_le

section AltNine

open CFSG.AGLEmbedding.A9Local

private theorem card_sylow_altNine (T : Sylow 3 (alternatingGroup (Fin 9))) :
    Nat.card (T : Subgroup (alternatingGroup (Fin 9))) = 81 := by
  have hA : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hf : (Nat.card (alternatingGroup (Fin 9))).factorization 3 = 4 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hA, Nat.factorization_def _ Nat.prime_three,
      show (181440 : ℕ) = 3 ^ 4 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [Sylow.card_eq_multiplicity, hf]
  norm_num

theorem altNine_isSolvable_of_sylow_le (T : Sylow 3 (alternatingGroup (Fin 9)))
    (H : Subgroup (alternatingGroup (Fin 9))) (hTH : (T : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  classical
  let φ₀ : alternatingGroup (Fin 9) →* Perm Pt :=
    eqPt.permCongrHom.toMonoidHom.comp (alternatingGroup (Fin 9)).subtype
  have hφ₀ : Function.Injective φ₀ := fun x y hxy =>
    Subtype.ext (eqPt.permCongrHom.injective hxy)
  obtain ⟨g, hg⟩ := exists_conj_le_sylowT (T.isPGroup'.map φ₀)
  let φ : alternatingGroup (Fin 9) →* Perm Pt := (MulAut.conj g).toMonoidHom.comp φ₀
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hφ₀
  have hφA : ∀ x, φ x ∈ alternatingGroup Pt := by
    intro x
    have h1 : Perm.sign (φ₀ x) = 1 := by
      show Perm.sign (eqPt.permCongr (x : Perm (Fin 9))) = 1
      rw [Perm.sign_permCongr]
      exact Perm.mem_alternatingGroup.mp x.2
    rw [Perm.mem_alternatingGroup]
    show Perm.sign (g * φ₀ x * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  have hTle : (T : Subgroup (alternatingGroup (Fin 9))).map φ ≤ sylowT := by
    rintro _ ⟨t, ht, rfl⟩
    exact hg _ (mem_map_of_mem φ₀ ht)
  have hTeq : (T : Subgroup (alternatingGroup (Fin 9))).map φ = sylowT :=
    eq_of_le_of_card_ge hTle (by rw [card_sylowT, card_map_of_injective hφ, card_sylow_altNine])
  have hTH' : sylowT ≤ H.map φ := hTeq ▸ map_mono hTH
  have hB : baseGroup ≤ H.map φ := baseGroup_le_sylowT.trans hTH'
  have hτ : blockShift ∈ H.map φ := hTH' (affPerm_mem_sylowT 1 0)
  by_cases hprim : MulAction.IsPreprimitive (H.map φ) Pt
  · exfalso
    have hA := Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
      NrmMax.isThreeCycle_shiftPerm_single (hB (shiftPerm_mem_baseGroup _))
    refine hH (eq_top_iff.mpr fun x _ => ?_)
    obtain ⟨y, hy, hyx⟩ := mem_map.mp (hA (hφA x))
    rw [← hφ hyx]
    exact hy
  · haveI := isSolvable_of_le_nrm (NrmMax.le_nrm_of_not_isPreprimitive hB hτ hprim)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (equivMapOfInjective H φ hφ).toMonoidHom) (equivMapOfInjective H φ hφ).injective

end AltNine

theorem threeFourTwoNoneAt_altNine (h : 5 ≤ 9) :
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.alternating 9 h).Group := by
  obtain ⟨hs, hnab, hout⟩ := alternating_catalog_facts h
  exact threeFourTwoNoneAt_of_sylow_le_isSolvable hs hnab hout altNine_isSolvable_of_sylow_le

theorem threeFourTwoThreeAlt_holds : ThreeFourTwoThreeAlt := by
  rintro n h (rfl | rfl)
  · exact threeFourTwoNoneAt_altSix h
  · exact threeFourTwoNoneAt_altNine h

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
