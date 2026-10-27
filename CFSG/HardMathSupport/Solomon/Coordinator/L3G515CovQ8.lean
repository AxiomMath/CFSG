module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem isSolvable_of_commutator_le {H : Type*} [Group H] (C T : Subgroup H)
    [Group.IsSolvable ↥T] (h : ⁅C, C⁆ ≤ T) : Group.IsSolvable ↥C := by
  let S' : Subgroup ↥C := (⁅C, C⁆).subgroupOf C
  let ψ : ↥S' →* ↥T :=
    { toFun := fun x => ⟨(x.1 : H), h (Subgroup.mem_subgroupOf.1 x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (Subtype.ext (show (ψ x).1 = (ψ y).1 from congrArg Subtype.val hxy))
  have : Group.IsSolvable ↥S' := Group.isSolvable_of_isSolvable_injective hψ
  refine Group.isSolvable_of_ker_le_range S'.subtype (Abelianization.of : ↥C →* Abelianization ↥C) ?_
  rw [Abelianization.ker_of, Subgroup.range_subtype]
  refine Subgroup.commutator_le.2 fun a _ b _ => ?_
  exact Subgroup.mem_subgroupOf.2 (Subgroup.commutator_mem_commutator a.2 b.2)

theorem eq_two_of_pow_three_eq_eight {a : ℕ} (h : a ^ 3 = 8) : a = 2 :=
  Nat.pow_left_injective (n := 3) (by norm_num) (h.trans (by norm_num : (8 : ℕ) = 2 ^ 3))

section Cover

variable {p f : ℕ} {K : Type} [Field K]

theorem isSolvable_fix_frobSL_proj (hK : PiField false p f K) (h8 : p ^ f = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    Group.IsSolvable ↥(fixSub (centerDescend ↥(slPi false 3 (p ^ f) K) (frobSL hK σ))) := by
  obtain ⟨d⟩ := exists_frobData hK hσ
  have h2 : p ^ d.f₀ = 2 := eq_two_of_pow_three_eq_eight (by rw [← d.pow_eq]; exact h8)
  have hq : ModThree false (p ^ f) := by rw [h8]; rfl
  set G := ↥(slPi false 3 (p ^ f) K) with hG
  let pm : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  have hsurj : Function.Surjective pm := QuotientGroup.mk'_surjective _
  have hker : ∀ c, pm c = 1 → c ∈ Subgroup.center G := fun c h => (QuotientGroup.eq_one_iff c).1 h
  have hc : ∀ x, pm (frobSL hK σ x) = centerDescend G (frobSL hK σ) (pm x) := fun x => rfl
  have hS0 : Group.IsSolvable ↥(slPi false 3 (p ^ d.f₀) d.K₀) :=
    (isSolvable_slPi_false_two d.hP h2).1
  have hS : Group.IsSolvable ↥(fixSub (frobSL hK σ)) :=
    Group.isSolvable_of_isSolvable_injective (f := d.fixEquiv.toMonoidHom) d.fixEquiv.injective
  have hT : Group.IsSolvable ↥((fixSub (frobSL hK σ)).map pm) :=
    Group.isSolvable_of_surjective (f := pm.subgroupMap (fixSub (frobSL hK σ)))
      (pm.subgroupMap_surjective _)
  exact isSolvable_of_commutator_le _ _ (fixSub_commutator_le_map hsurj hker hc)

theorem eq_one_or_isSolvable_fix_q8 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (hK : PiField false p f K) (h8 : p ^ f = 8)
    (e : (Y ⧸ Subgroup.center Y) ≃*
      (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)))
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) :
    α = 1 ∨ Group.IsSolvable ↥(fixSub α) := by
  have hq2 : 2 < p ^ f := by rw [h8]; norm_num
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  set ε : (Y ⧸ Subgroup.center Y) ≃* pkg.M := e.trans pkg.η with hε
  have hβ3 : MulAut.congr ε (centerDescend Y α) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  rcases pkg.dich _ hβ3 with hin | ⟨σ, hσ, κ, hκ, hβ⟩
  · exact Or.inl (eq_one_of_inndiag_model hY pkg.good ε hin hf)
  · right
    let e2 : (Y ⧸ Subgroup.center Y) ≃*
        (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)) :=
      (ε.trans κ⁻¹).trans pkg.η.symm
    have hc : MulAut.congr e2 (centerDescend Y α) =
        centerDescend _ (frobSL hK σ) := by
      have h1 : MulAut.congr e2 (centerDescend Y α) =
          MulAut.congr pkg.η.symm (MulAut.congr κ⁻¹ (MulAut.congr ε (centerDescend Y α))) := by
        rw [congr_trans', congr_trans']
      rw [h1, hβ, congr_self, inv_inv]
      have h2 : κ⁻¹ * (κ * MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) * κ⁻¹) * κ =
          MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) := by group
      rw [h2]
      ext x
      simp [MulAut.congr_apply]
    have hsolE : Group.IsSolvable ↥(fixSub (MulAut.congr e2 (centerDescend Y α))) := by
      rw [hc]
      exact isSolvable_fix_frobSL_proj hK h8 hσ
    have hsol : Group.IsSolvable ↥(fixSub (centerDescend Y α)) := by
      rw [fixSub_congr e2 (centerDescend Y α)] at hsolE
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective (fixSub (centerDescend Y α)) e2.toMonoidHom
          e2.injective).toMonoidHom) (Subgroup.equivMapOfInjective _ _ e2.injective).injective
    exact isSolvable_fixSub_of_descend α hsol

end Cover

end CFSG.HardMathSupport.Solomon.Coordinator
