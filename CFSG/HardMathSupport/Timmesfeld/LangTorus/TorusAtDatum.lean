module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] noncomputable def LangDatum.ofFrobenius {τ : Tag} {L : Type} [Field L] (Fr : L →+* L)
    (q : ℕ) (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup τ) {g0 : ModGL τ L}
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w) :
    LangDatum τ L where
  Φ := Units.map (entrywiseHom Fr)
  q := q
  n := canonicalRep (coxeterSystem τ) L w
  g0 := g0
  steinberg := ⟨Fr, hFr, 1, Or.inl rfl, fun g => by simp⟩
  n_weyl := ⟨w, rfl⟩
  g0_mem := hg0C
  lang := hg0

@[expose] noncomputable def LangDatum.ofTwist (t : TwistTag) {L : Type} [Field L] (Fr : L →+* L)
    (q : ℕ) (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup t.tag) {g0 : ModGL t.tag L}
    (hg0C : g0 ∈ adjointGroup t.tag L)
    (hg0 : twistHom t L Fr g0 = g0 * canonicalRep (coxeterSystem t.tag) L w) :
    LangDatum t.tag L where
  Φ := twistHom t L Fr
  q := q
  n := canonicalRep (coxeterSystem t.tag) L w
  g0 := g0
  steinberg := ⟨Fr, hFr, diagramMap t L, Or.inr ⟨t, rfl, rfl⟩, fun g => by
    simp [twistHom, MulAut.conj_apply]⟩
  n_weyl := ⟨w, rfl⟩
  g0_mem := hg0C
  lang := hg0

section Finite

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

theorem finite_of_entries_mem_range (S : Subgroup (ModGL τ L))
    (h : ∀ g ∈ S, ∀ a b : Label τ, ∃ x : K, algebraMap K L x =
      ((g : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a) :
    Finite S := by
  classical
  choose φ hφ using fun (g : S) (a b : Label τ) => h g g.2 a b
  refine Finite.of_injective φ fun g g' hgg' => Subtype.ext (Units.ext ?_)
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [← hφ, ← hφ, hgg']

end Finite

end CFSG.HardMathSupport.Timmesfeld.LangTorus
