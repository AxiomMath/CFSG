module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldCentral
import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.PartTwo.KFacts

theorem l3bf_core_layer {Y P : Type*} [Group Y] [Finite Y] [Group P]
    (hcore : GLAPPrimeCore 3 Y = ⊥) (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y)
    {ψ : MulAut P} (hψ : MulAut.congr e (centerDescend Y α) = ψ) (h : L3BFixData ψ) :
    GLAPPrimeCore 3 ↥(LocalBalance.Lemma53Ns.fixSub α) = ⊥ ∧
      ∃ L : Subgroup Y, L ≤ LocalBalance.Lemma53Ns.fixSub α ∧ CFSG.Open.IsQuasisimple ↥L ∧
        L.map ((e : _ →* P).comp (QuotientGroup.mk' (Subgroup.center Y))) =
          ⁅l3bFix ψ, l3bFix ψ⁆ ∧
        (∀ J : Subgroup Y, GLAPComponent 3 (LocalBalance.Lemma53Ns.fixSub α) J ↔ J = L) ∧
        GLAPLayer 3 (LocalBalance.Lemma53Ns.fixSub α) = L := by
  have hZ : ∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1 := by
    intro z hz
    obtain ⟨n, hn⟩ := isPGroup_center Nat.prime_three hcore ⟨z, hz⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have := h.simple
  obtain ⟨h1, L, h2, h3, h4, h5, h6⟩ := l3bf_central_fixed
    (π := (e : _ →* P).comp (QuotientGroup.mk' (Subgroup.center Y)))
    (by
      intro p
      obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨y, rfl⟩)
    (by
      intro y hy
      have : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := e.injective (by simpa using hy)
      exact QuotientGroup.eq_one_iff y |>.1 this)
    hZ (α := α) (ψ := ψ)
    (by
      intro y
      rw [← hψ]
      exact (descend_compat e α y).symm ▸ rfl)
    (C := LocalBalance.Lemma53Ns.fixSub α) (fun y => Iff.rfl)
    (D := l3bFix ψ) (fun x => Iff.rfl)
    (S := ⁅l3bFix ψ, l3bFix ψ⁆)
    (by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (l3bFix ψ).mul_mem ((l3bFix ψ).mul_mem ((l3bFix ψ).mul_mem ha hb) ((l3bFix ψ).inv_mem ha))
        ((l3bFix ψ).inv_mem hb))
    h.nonab h.three_dvd le_rfl h.cube
  exact ⟨h1, L, h2, h3, h4, h5, h6⟩

theorem l3bf_layer_bot_of_descent {Y P : Type*} [Group Y] [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) {ψ : MulAut P}
    (hψ : MulAut.congr e (centerDescend Y α) = ψ) (hs : Group.IsSolvable ↥(l3bFix ψ)) :
    GLAPLayer 3 (LocalBalance.Lemma53Ns.fixSub α) = ⊥ :=
  l3bf_layer_bot (π := (e : _ →* P).comp (QuotientGroup.mk' (Subgroup.center Y)))
    (by
      intro y hy
      have : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := e.injective (by simpa using hy)
      exact QuotientGroup.eq_one_iff y |>.1 this)
    (α := α) (ψ := ψ)
    (by
      intro y
      rw [← hψ]
      exact (descend_compat e α y).symm ▸ rfl)
    (C := LocalBalance.Lemma53Ns.fixSub α) (fun y => Iff.rfl) hs

theorem l3bf_core_of_descent {Y P : Type*} [Group Y] [Finite Y] [Group P]
    (hcore : GLAPPrimeCore 3 Y = ⊥) (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y)
    {ψ : MulAut P} (hψ : MulAut.congr e (centerDescend Y α) = ψ)
    (hD : GLAPPrimeCore 3 ↥(l3bFix ψ) = ⊥) :
    GLAPPrimeCore 3 ↥(LocalBalance.Lemma53Ns.fixSub α) = ⊥ := by
  have hZ : ∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1 := by
    intro z hz
    obtain ⟨n, hn⟩ := isPGroup_center Nat.prime_three hcore ⟨z, hz⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  refine l3bf_core_of_fixed_core (π := (e : _ →* P).comp (QuotientGroup.mk' (Subgroup.center Y)))
    (by
      intro p
      obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨y, rfl⟩)
    (by
      intro y hy
      have : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := e.injective (by simpa using hy)
      exact QuotientGroup.eq_one_iff y |>.1 this)
    hZ (α := α) (ψ := ψ)
    (by
      intro y
      rw [← hψ]
      exact (descend_compat e α y).symm ▸ rfl)
    (C := LocalBalance.Lemma53Ns.fixSub α) (fun y => Iff.rfl) hD

end CFSG.HardMathSupport.Solomon.Coordinator
