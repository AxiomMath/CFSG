module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutFixed
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnClassical
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.TriD4 CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

theorem not_isD42Type_projectiveSL {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (h4 : n = 2 → 4 ≤ Nat.card K) :
    ¬ IsCatalogLieIso (projectiveSL n K) IsD42Index := by
  intro h
  have he : ProjectiveSpecialLinearGroup (Fin n) K ≃* projectiveSL n K :=
    LinearCover.projectiveSpecialLinearEquivProjectiveSL n K
  have hcard : Nat.card (ProjectiveSpecialLinearGroup (Fin n) K) = 174182400 := by
    rw [Nat.card_congr he.toEquiv]
    exact card_of_isD42Type h
  exact card_centerQuot_sl_ne hn hf hK h4 (MulEquiv.refl _) hcard

theorem not_upD42Pumpup_conjAut_linear {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) :
    ¬ UpD42Pumpup (projectiveSL n K) (conjAut n K A) := by
  intro h
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have h3K : ((3 : ℕ) : K) ≠ 0 := fun h0 => by
    have h23 := (CharP.cast_eq_zero_iff K 2 3).1 h0
    omega
  have hlayer := perfectInLayer_projectiveSL hn Nat.prime_three (by norm_num) h3K
    (conjAut n K A) h.1
  exact not_upD42Pumpup_of_componentsNoD4 hlayer
    (componentsNoD4_conjAut (by omega) hf hK A h.1) h

theorem not_upD42Pumpup_fieldAut_psl {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ¬ UpD42Pumpup (projectiveSL n K) (fieldAut n K σ) := by
  intro h
  let k := semilinearFixedSubfield σ
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let J : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range
  let eJ : ↥J ≃* projectiveSL n ↥k := (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have hnc := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn
    push Not at hnc
    exact hnc
  have hsJ : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hnabJ : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    refine ⟨eJ.symm a, eJ.symm b, fun he => hab ?_⟩
    have he' := congrArg eJ he
    simpa only [map_mul, MulEquiv.apply_symm_apply] using he'
  have hJC : J ≤ fixSubgroup (fieldAut n K σ) := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y
  have hcomm : ⁅fixSubgroup (fieldAut n K σ), fixSubgroup (fieldAut n K σ)⁆ ≤ J :=
    Subgroup.commutator_le.2 fun a ha b hb => commutator_fixed_mem_range (by omega) ha hb
  have hD := isD42Type_of_upD42Pumpup_of_simple_normal_comm h J hJC hcomm hsJ hnabJ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have h3 : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  exact not_isD42Type_projectiveSL (by omega) hf0 hkcard (fun h2 => by omega)
    (IsCatalogLieIso.of_mulEquiv eJ hD)

theorem not_upD42Pumpup_projectiveSL {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (projectiveSL n K)) : ¬ UpD42Pumpup (projectiveSL n K) α := by
  intro h
  by_cases hdiag : α ∈ linearAutGroup n K
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hdiag
    exact not_upD42Pumpup_conjAut_linear hn hf hK A h
  · obtain ⟨σ, hσ, H, hα⟩ := linear_order_three_field_descent hn α h.1 hdiag
    let γ := conjAut n K H
    have he : MulAut.congr γ⁻¹ α = fieldAut n K σ := by
      rw [hα]
      ext x
      simp [γ, MulAut.congr_apply, MulAut.mul_apply]
    have h' := h.congr γ⁻¹
    rw [he] at h'
    exact not_upD42Pumpup_fieldAut_psl hn hf hK hσ h'

theorem upD42Chev2Out_linear_rank_ge_two_holds : UpD42Chev2Out
    (fun d => match d with | .A r _ => 2 ≤ r | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hF hc ⟨e⟩ α _ h
  cases d with
  | A r q =>
    have hp : q.p = 2 := hc
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let e' : S ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
    have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp]
    exact (not_upD42Pumpup_projectiveSL (by omega) q.exponent_pos hK
      (MulAut.congr e' α) (h.congr e')).elim
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
