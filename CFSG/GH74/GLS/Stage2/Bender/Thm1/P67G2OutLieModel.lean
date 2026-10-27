module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2OutInv

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem g2_outer_involution_fixed_simple {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) {Y : Type} [Group Y] [Finite Y] (hY : LieModel Y .G2 0 p f) (α : MulAut Y)
    (hα : α * α = 1) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ L0 : Subgroup Y, L0 ≤ fixSub α ∧ (L0.subgroupOf (fixSub α)).Normal ∧
      (∀ a ∈ fixSub α, ∀ b ∈ fixSub α, ⁅a, b⁆ ∈ L0) ∧ IsSimpleGroup ↥L0 ∧
        ∃ e : ℕ, 1 ≤ e ∧ LieModel ↥L0 .G2 0 p e := by
  classical
  have hY' : ChevalleyExceptionalModel Y .G2 p f := by
    rcases hY with ⟨hc, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd hc (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨ψ⟩⟩ := hY'
  have hcenter : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  let ψ' : Y ≃* ↥(adjointGroup Tag.G2 K) :=
    ψ.trans ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)
  let α' : MulAut ↥(adjointGroup Tag.G2 K) := MulAut.congr ψ' α
  have hα1 : α ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  have hα'1 : α' ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ').injective (h.trans (map_one (MulAut.congr ψ')).symm))
  have hα'2 : α' ^ 2 = 1 := by
    rw [pow_two]
    change MulAut.congr ψ' α * MulAut.congr ψ' α = 1
    rw [← map_mul, hα, map_one]
  have hα'ord : orderOf α' = 2 := orderOf_eq_prime hα'2 hα'1
  have hα'out : ¬ IsInnerAut α' := by
    rintro ⟨g', hg'⟩
    apply hout
    refine ⟨ψ'.symm g', MulEquiv.ext fun y => ?_⟩
    have h1 : α' (ψ' y) = ψ' (α y) := by
      change ψ' (α (ψ'.symm (ψ' y))) = ψ' (α y)
      rw [MulEquiv.symm_apply_apply]
    rw [← hg', MulAut.conj_apply] at h1
    have h2 := congrArg ψ'.symm h1
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
    rw [MulAut.conj_apply]
    exact h2
  obtain ⟨e, he1, hfe, k, hkf, hkfin, hkcard, ⟨eqv⟩, hsimple, -⟩ :=
    g2_fixSub_outer_involution hp hp2 hp3 hf K hKcard hα'ord hα'out
  have hmap : (fixSub α).map ψ'.toMonoidHom = fixSub α' := by
    ext x
    rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
    change α (ψ'.symm x) = ψ'.symm x ↔ ψ' (α (ψ'.symm x)) = x
    constructor
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
    · intro h
      apply ψ'.injective
      rw [h, MulEquiv.apply_symm_apply]
  let e0 : ↥(fixSub α) ≃* ↥(fixSub α') :=
    (Subgroup.equivMapOfInjective (fixSub α) ψ'.toMonoidHom ψ'.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hck : Subgroup.center ↥(adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
  have h5 := five_le_of_ne_three hp hp2 hp3
  have h3 : 3 ≤ p ^ e := by
    calc 3 ≤ p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  have := hsimple
  refine ⟨fixSub α, le_rfl, ?_, fun a ha b hb => ?_, e0.isSimpleGroup, e, he1, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, he1, rfl, h3⟩, k, hkf, hkfin, hkcard,
      ⟨(e0.trans eqv).trans
        ((QuotientGroup.quotientMulEquivOfEq hck).trans QuotientGroup.quotientBot).symm⟩⟩)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
