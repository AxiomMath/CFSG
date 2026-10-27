module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallB2Root
public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem isQuasisimple_of_simple_of_card_not_prime {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ¬ (Nat.card Q).Prime) : CFSG.IsQuasisimple Q := by
  have hL : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := h }
    exact hQ (IsSimpleGroup.prime_card (α := Q))
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hQ' : IsSimpleGroup (Q ⧸ Subgroup.center Q) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  refine ⟨?_, hQ', ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact ⟨h⟩
  · by_contra h
    push Not at h
    let _ : CommGroup (Q ⧸ Subgroup.center Q) :=
      { (inferInstance : Group (Q ⧸ Subgroup.center Q)) with mul_comm := h }
    have hp := IsSimpleGroup.prime_card (α := Q ⧸ Subgroup.center Q)
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv] at hp
    exact hQ hp

theorem b2_two_derived_quasisimple {K : Type} [Field K] (hK2 : ∀ x : K, x = 0 ∨ x = 1)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {s l : Fin Tag.F4.rank → ℤ}
    (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2)
    (hΨ : componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}) :
    CFSG.IsQuasisimple
      ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ : Subgroup (ModGL Tag.F4 K)) := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases hK2 (1 + 1) with h | h
    · rwa [one_add_one_eq_two] at h
    · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hΨc := isRootComponent_componentRoots (χ := χ) i
  have hs : IsRoot .F4 s := hΨc.isRoot s (by rw [hΨ]; simp)
  have hl : IsRoot .F4 l := hΨc.isRoot l (by rw [hΨ]; simp)
  have hrel := b2Rel_F4 (K := K) hs hl hss hll hsl
  obtain ⟨-, hb, -⟩ := f4_commutator_mixed hs hl hss hll hsl
  set S := componentRootSpan K χ i with hSdef
  have hSgen : S = Subgroup.closure ({xr K s, xr K (-s), xr K l, xr K (-l), xr K (s + l),
      xr K (-(s + l)), xr K (2 • s + l), xr K (-(2 • s + l))} : Set (ModGL Tag.F4 K)) := by
    apply le_antisymm
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rcases hK2 c with rfl | rfl
      · rw [pinnedX_zero]
        exact one_mem _
      · apply Subgroup.subset_closure
        have hα' : α ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)} :
            Set (Fin Tag.F4.rank → ℤ)) := hΨ ▸ hα
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα' ⊢
        rcases hα' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [xr]
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hmem : ∀ γ : Fin Tag.F4.rank → ℤ, γ ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l,
          -(2 • s + l)} : Set (Fin Tag.F4.rank → ℤ)) → γ ∈ componentRoots χ i :=
        fun γ h => hΨ ▸ h
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact pinnedX_mem_rootSpan (hmem _ (by simp)) 1
  have hcox := b2_isCoxeterA hrel
  have h01 : b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
      (xr K (2 • s + l)) (xr K (-(2 • s + l))) 0 ≠
      b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
        (xr K (2 • s + l)) (xr K (-(2 • s + l))) 1 :=
    fun h => xr_ne_xr_neg hb (by simpa [b2t] using h.symm)
  obtain ⟨e, -⟩ := exists_mulEquiv_closure_five hcox h01
  have hS : S = Subgroup.closure (b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l))
      (xr K (s + l)) (xr K (-(s + l))) (xr K (2 • s + l)) (xr K (-(2 • s + l))) ''
      Set.Iio 5) := hSgen.trans (b2_closure_eq hrel)
  let Φ : ↥S ≃* Equiv.Perm (Fin 6) := (MulEquiv.subgroupCongr hS).trans e.symm
  have hle : ⁅S, S⁆ ≤ S := Subgroup.commutator_le_self S
  have himg := CFSG.LargeExtraspecial.S45Q.img_commutator Φ
  let ψ : ↥⁅S, S⁆ ≃* alternatingGroup (Fin 6) :=
    (CFSG.LargeExtraspecial.S45Q.imgEquiv Φ hle).trans (MulEquiv.subgroupCongr himg)
  have hsimple : IsSimpleGroup ↥⁅S, S⁆ := by
    have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_alternatingGroup_six
    exact ψ.isSimpleGroup
  have hcard : Nat.card ↥⁅S, S⁆ = 360 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.LargeExtraspecial.S45Q.card_alternatingGroup_six]
  exact isQuasisimple_of_simple_of_card_not_prime (by rw [hcard]; norm_num)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
