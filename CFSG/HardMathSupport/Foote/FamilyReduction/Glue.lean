module

public import CFSG.HardMathSupport.Foote.FamilyReduction.Abstract
public import CFSG.HardMathSupport.Foote.Coordinator.Component
public import CFSG.Sporadic.HeldB.FixedTransport

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG CFSG.HardMathSupport.Foote.Coordinator
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Glue

variable {Q : Type} [Group Q]

theorem center_eq_bot_of_simple_nonabelian [IsSimpleGroup Q] (hna : ∃ x y : Q, x * y ≠ y * x) :
    Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)

theorem compIn5_of_innerComp5 [IsSimpleGroup Q] (hna : ∃ x y : Q, x * y ≠ y * x) {w : Q}
    {K : Subgroup Q} (h : InnerComp5 Q w K) : CompIn5 Q := by
  have hc := center_eq_bot_of_simple_nonabelian hna
  have hα1 : MulAut.conj w ≠ 1 := by
    intro h1
    apply h.ne_one
    have hw : w ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun ψ : MulAut Q => ψ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hc] at hw
    exact Subgroup.mem_bot.mp hw
  have hord : orderOf (MulAut.conj w) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, h.invol, map_one]) hα1
  obtain ⟨e⟩ := h.sl5
  let C : Subgroup Q := Subgroup.centralizer ({w} : Set Q)
  have heq : fixedSubgroup (MulAut.conj w) = C := CFSG.Sporadic.HeldB.fixedSubgroup_conj w
  let ε : ↥C ≃* ↥(fixedSubgroup (MulAut.conj w)) := MulEquiv.subgroupCongr heq.symm
  let K₀ : Subgroup ↥C := K.subgroupOf C
  refine ⟨MulAut.conj w, w, rfl, hord, K₀.map ε.toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv ε h.comp,
    ⟨(K₀.equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe h.le).trans e)⟩, ?_⟩
  have hwF : w ∈ fixedSubgroup (MulAut.conj w) := by
    rw [heq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨hwF, ⟨⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, h.mem, Subtype.ext rfl⟩⟩

variable {V : Type} [CommGroup V] [Finite V] {L Y : Subgroup (MulAut V)} {z : MulAut V}
  {π : ↥L →* Q}

noncomputable def quotEquivOfFooteK (h : FooteK Q L Y z π) : (↥L ⧸ Subgroup.center ↥L) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq h.ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π h.surj)

theorem finite_of_footeK (h : FooteK Q L Y z π) : Finite Q :=
  Finite.of_surjective π h.surj

theorem isSimpleGroup_of_footeK (h : FooteK Q L Y z π) : IsSimpleGroup Q := by
  have := h.quasi.2
  exact (quotEquivOfFooteK h).symm.isSimpleGroup

theorem nonabelian_of_footeK (h : FooteK Q L Y z π) : ∃ x y : Q, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := (CFSG.CGT.PushingUpLit.CGT6M.isQuasisimple_of_open h.quasi).2.2
  exact ⟨quotEquivOfFooteK h a, quotEquivOfFooteK h b, fun h1 => hab ((quotEquivOfFooteK h).injective (by
    rw [map_mul, map_mul, h1]))⟩

end Glue

theorem end415K_of_not_compIn5 {Q : Type} [Group Q]
    (h : ∀ [Finite Q] [IsSimpleGroup Q], (∃ x y : Q, x * y ≠ y * x) → ¬ CompIn5 Q) :
    End415K Q := by
  intro V _ _ L Y z π hK
  have := finite_of_footeK hK
  have := isSimpleGroup_of_footeK hK
  exact h (nonabelian_of_footeK hK) (compIn5_of_innerComp5 (nonabelian_of_footeK hK) (FooteK.innerComp5 hK))

end CFSG.HardMathSupport.Foote.FamilyReduction
