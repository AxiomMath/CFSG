module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoToralCoords
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem
public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE8F

theorem TwE6ToralCoords.famKernel_ggHyperplane
    {n : ℕ} {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ)
    {r : MulAut Bs} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hHr : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    famKernel (Set.range fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
      zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ (b : Bs)))) = {γ, -γ} := by
  let V : Set (Fin Tag.E6.rank → ZMod 3) :=
    {v | Multiplicative.ofAdd v ∈ κ.range}
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) := by
    rcases hκ.range_eq_top_or with htop | hhyp
    · left
      apply Set.eq_univ_of_forall
      intro v
      change Multiplicative.ofAdd v ∈ κ.range
      rw [htop]
      exact Subgroup.mem_top _
    · right
      ext v
      exact hhyp v
  let aH := fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
    zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ (b : Bs)))
  let aV := fun v : {v : Fin Tag.E6.rank → ZMod 3 //
      v ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ v = v} =>
    zetaVec (τ := Tag.E6) ζ hζ v.1
  have hRange : Set.range aH = Set.range aV := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      have hbf : r (b : Bs) = (b : Bs) := b.2
      have hbH := (mem_ggHyperplane_iff' (b : Bs)).2 hbf
      have hb0 := (hHr (b : Bs)).1 hbH
      have hbV : Multiplicative.toAdd (κ (b : Bs)) ∈ V := ⟨(b : Bs), rfl⟩
      have hbr := (ExcSplitRootGen.excRefl_eq_self_iff (p := 3)
        (by decide) hγ (Multiplicative.toAdd (κ (b : Bs)))).2 hb0
      exact ⟨⟨Multiplicative.toAdd (κ (b : Bs)), hbV, hbr⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨b, hb⟩ := v.2.1
      have hbv : Multiplicative.toAdd (κ b) = v.1 := congrArg Multiplicative.toAdd hb
      have hb0 : ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0 := by
        rw [hbv]
        exact (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by decide) hγ v.1).1 v.2.2
      have hbf : r b = b := (mem_ggHyperplane_iff' b).1 ((hHr b).2 hb0)
      refine ⟨⟨b, hbf⟩, ?_⟩
      exact congrArg (zetaVec (τ := Tag.E6) ζ hζ) hbv
  calc
    famKernel (Set.range aH) = famKernel (Set.range aV) := congrArg famKernel hRange
    _ = familyKernel aV := by
      ext δ
      simp only [famKernel, familyKernel, Set.mem_setOf_eq, Set.forall_mem_range]
    _ = {γ, -γ} := TwE6ThreeRootGen.familyKernel_zetaVec_eq hζ hζo hV hγ

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
