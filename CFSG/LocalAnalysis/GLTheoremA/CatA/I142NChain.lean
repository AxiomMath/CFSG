module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NG5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

theorem fixA_subtype_eq_centFix {S : Type} [Group S] (E : Subgroup (MulAut S)) :
    fixA E.subtype = I142.centFix E := by
  ext x
  rw [mem_fixA, I142.mem_centFix]
  constructor
  · intro h e he
    exact h ⟨e, he⟩
  · intro h a
    exact h a a.2

theorem goodA_subtype_top_of_centFix {S : Type} [Group S] (E : Subgroup (MulAut S))
    (h : ∀ P : Subgroup S, P ≤ I142.centFix E → ⁅P, P⁆ = P →
      P ≤ GLALayer (I142.centFix E)) :
    GoodA E.subtype ⊤ := by
  intro P hP hPp
  rw [inf_top_eq, fixA_subtype_eq_centFix] at hP
  rw [inf_top_eq, fixA_subtype_eq_centFix]
  exact h P hP hPp

theorem fixA_eq_range {A G : Type*} [Group A] [Group G] (σ : A →* MulAut G) :
    fixA σ = fixA σ.range.subtype := by
  ext x
  rw [mem_fixA, mem_fixA]
  constructor
  · intro h e
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 e.2
    have hx : σ a x = x := h a
    have he : (e : MulAut G) = σ a := ha.symm
    show (e : MulAut G) x = x
    rw [he]
    exact hx
  · intro h a
    exact h ⟨σ a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩

theorem quotAct_mk {A S : Type*} [Group A] [Group S] (ρ : A →* MulAut S) (K₀ : Subgroup S)
    (hinv : ∀ a, K₀.map (ρ a).toMonoidHom = K₀) (a : A) (x : ↥K₀) :
    QuotientGroup.mk' (Subgroup.center ↥K₀) (restrictAct ρ K₀ hinv a x) =
      quotAct ρ K₀ hinv a (QuotientGroup.mk' (Subgroup.center ↥K₀) x) := by
  simp only [quotAct, MonoidHom.mk'_apply, quotActFun, QuotientGroup.mk'_apply]
  rw [QuotientGroup.congr_mk]
  rfl

theorem goodA_of_component {A S : Type*} [Group A] [Group S] (ρ : A →* MulAut S)
    (K₀ : Subgroup S) (hinv : ∀ a, K₀.map (ρ a).toMonoidHom = K₀)
    (hq : CFSG.Open.IsQuasisimple ↥K₀)
    (hsig : ∀ P : Subgroup (↥K₀ ⧸ Subgroup.center ↥K₀),
      P ≤ fixA (quotAct ρ K₀ hinv) → ⁅P, P⁆ = P →
        P ≤ GLALayer (fixA (quotAct ρ K₀ hinv))) :
    GoodA ρ K₀ :=
  good_of_restrict ρ hinv
    (sigma_of_quasisimple_mod_center hq (restrictAct ρ K₀ hinv) (quotAct ρ K₀ hinv)
      (fun a x => quotAct_mk ρ K₀ hinv a x) hsig)

end CFSG.LocalAnalysis.GLTheoremA.I142N
