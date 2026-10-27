module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGLS3
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Mult

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowLie

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixedSubgroup_conj_eq {S : Type*} [Group S] (t : S) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set S) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change t * x * t⁻¹ = x ↔ x * t = t * x
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

section Certified


theorem exists_lieModel_of_lieChar_odd {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {r : ℕ} (hr2 : r ≠ 2) (hS : LieChar r S) {t : S}
    (ht : orderOf t = 2) {J : Subgroup S} (hJC : J ≤ centralizer {t})
    (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal) (htJ : t ∈ J)
    (hJq : IsTwoQuasisimple ↥J) :
    ∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' r f' ∧
      Blueprint.LieModel (↥J ⧸ Open.fusionZStar ↥J) τ' n' r f' := by
  obtain ⟨τ, n, f, hm⟩ := hS
  have hadm := N36.admissible_of_lieModel' hm
  have hr : r.Prime := hadm.1
  have hB : CatLeaf.FixedTwoComponentsQuasisimple S :=
    CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨τ, n, r, f, hr, hr2, hadm, hm⟩
  have hG := GrSLit.gls3OddLieAutComponentsInput_holds
  have hZS : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hα2 : MulAut.conj t * MulAut.conj t = 1 := by rw [← map_mul, htt, map_one]
  have hα1 : MulAut.conj t ≠ 1 := by
    intro h
    have hc : t ∈ center S := by
      rw [mem_center_iff]
      intro g
      have hg : t * g * t⁻¹ = g := congrArg (fun β : MulAut S => β g) h
      calc g * t = t * g * t⁻¹ * t := by rw [hg]
        _ = t * g := by group
    rw [hZS, mem_bot] at hc
    rw [hc, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hαo : orderOf (MulAut.conj t) = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer {t})) :=
    (isTwoComponentIn_iff hJC).mp ⟨hJC, hJs, hJq⟩
  rw [← fixedSubgroup_conj_eq t] at hJpc hJC
  have hKq := hB (MulAut.conj t) hα2 hα1 _ hJpc
  obtain ⟨-, -, hKs, -⟩ := hJpc
  rcases hG S τ n r f hr hr2 hadm hm (MulAut.conj t) hαo _ ⟨hKq, hKs⟩ with hK | ⟨-, -, hαr, -⟩
  swap
  · exact absurd ⟨t, rfl⟩ hαr
  let eK : ↥J ≃* ↥(J.subgroupOf (fixedSubgroup (MulAut.conj t))) := (subgroupOfEquivOfLe hJC).symm
  obtain ⟨τ', n', f', hadm', hL⟩ := CatLeafProof.oddLieCentralQuotient_of_mulEquiv eK hK
  have hJqs : IsQuasisimple ↥J := LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq
  have heven : 2 ∣ Nat.card ↥J := by
    have h1 := orderOf_dvd_natCard (⟨t, htJ⟩ : ↥J)
    rwa [Subgroup.orderOf_mk, ht] at h1
  have : Group.IsPerfect ↥J := hJqs.1
  have hZ : Open.fusionZStar ↥J = center ↥J := OddStandard.fusionZStar_eq_center_of_perfect
    (OddStandard.Residual.pPrimeCore_le_center_of_quasisimple hJqs heven)
  exact ⟨τ', n', f', hadm', GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientMulEquivOfEq hZ.symm) hL⟩

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.RowLie
