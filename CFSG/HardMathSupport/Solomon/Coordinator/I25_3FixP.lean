module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

section Elem

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem i253_exists_pElem_slPi (hK : PiField π p f K) :
    ∃ x : ↥(slPi π 3 (p ^ f) K), orderOf x = p := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have hd : p ∣ Nat.card ↥(slPi π 3 (p ^ f) K) := by
    rw [card_slPi_three hK]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (dvd_pow (dvd_pow_self p (by have := hK.one_le; omega)) (by norm_num)) _) _
  exact exists_prime_orderOf_dvd_card' p hd

theorem i253_fixP_frobSL (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ x ∈ fixSub (frobSL hK σ), orderOf x = p := by
  obtain ⟨d⟩ := exists_frobData hK hσ
  obtain ⟨y, hy⟩ := i253_exists_pElem_slPi d.hP
  refine ⟨d.incl y, ?_, ?_⟩
  · rw [d.fixSub_eq]
    exact ⟨y, rfl⟩
  · exact (orderOf_injective d.incl d.incl_injective y).trans hy

end Elem

theorem i253_fixP_cover {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (e : Y ≃* ↥(slPi π 3 (p ^ f) K))
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α)
    (h8 : α ≠ 1 → π = false → p ^ f ≠ 8) : ∃ x ∈ fixSub α, orderOf x = p := by
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_cases hα : α = 1
  · subst hα
    obtain ⟨y, hy⟩ := i253_exists_pElem_slPi hK
    refine ⟨e.symm y, ?_, ?_⟩
    · rw [fixSub_one]; exact Subgroup.mem_top _
    · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective y).trans hy
  have hζ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ3 with ⟨y, hy, hS⟩ | ⟨σ, hσ, H, hH, hζ⟩
  · exfalso
    apply hα
    refine eq_one_of_inndiag_model hY pkg.good ((barEquiv e).trans pkg.η) ?_ hf
    rw [congr_trans', congr_barEquiv]
    exact pkg.conj_mem _ y hy (semiAct_one_iff.1 hS)
  · have hc : MulAut.congr (conjSL' hπ hH) (MulAut.congr e α) = frobSL hK σ := by
      refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [coe_frobSL]
      have h1 : (((conjSL' hπ hH).symm s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H * s * H⁻¹ := rfl
      have h2 : ((conjSL' hπ hH ((MulAut.congr e α) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H⁻¹ * (((MulAut.congr e α) ((conjSL' hπ hH).symm s) : ↥(slPi π 3 (p ^ f) K)) :
            GL (Fin 3) K) * H := rfl
      show ((conjSL' hπ hH ((MulAut.congr e α) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = _
      rw [h2, hζ, h1]
      have h3 : H⁻¹ * (H * (s : GL (Fin 3) K) * H⁻¹) * H = s := by group
      rw [h3]
      group
    obtain ⟨x, hx, hxo⟩ := i253_fixP_frobSL hK hσ
    set e' : Y ≃* ↥(slPi π 3 (p ^ f) K) := e.trans (conjSL' hπ hH) with he'
    have hcα : MulAut.congr e' α = frobSL hK σ := by rw [he', congr_trans', hc]
    have hF := fixSub_congr e' α
    rw [hcα] at hF
    refine ⟨e'.symm x, ?_, ?_⟩
    · have : x ∈ (fixSub α).map e'.toMonoidHom := by rw [← hF]; exact hx
      obtain ⟨z, hz, hzx⟩ := this
      have : e'.symm x = z := by rw [← hzx]; simp
      rw [this]; exact hz
    · exact (orderOf_injective e'.symm.toMonoidHom e'.symm.injective x).trans hxo

end CFSG.HardMathSupport.Solomon.Coordinator
