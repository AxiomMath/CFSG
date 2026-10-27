module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Fintype.Pi

public section

namespace CFSG.HardMathSupport.Curtis.Proving

theorem commute_of_mem_centralizer_of_irreducible
    {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Finite V] [Nontrivial V]
    {T : Set (Module.End F V)}
    (hirr : ∀ W : Submodule F V, (∀ t ∈ T, ∀ w ∈ W, t w ∈ W) → W = ⊥ ∨ W = ⊤)
    {f g : Module.End F V} (hf : ∀ t ∈ T, t * f = f * t) (hg : ∀ t ∈ T, t * g = g * t) :
    f * g = g * f := by
  classical
  have inj : ∀ x ∈ Subring.centralizer T, x ≠ 0 → Function.Injective x := by
    intro x hx hx0
    have hxT : ∀ t ∈ T, t * x = x * t := Subring.mem_centralizer_iff.1 hx
    have hinv : ∀ t ∈ T, ∀ v ∈ LinearMap.ker x, t v ∈ LinearMap.ker x := by
      intro t ht v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have h := congrArg (fun φ : Module.End F V => φ v) (hxT t ht)
      simp only [Module.End.mul_apply] at h
      rw [hv, map_zero] at h
      exact h.symm
    rcases hirr (LinearMap.ker x) hinv with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      apply hx0
      ext v
      have hv : v ∈ LinearMap.ker x := by rw [h]; exact Submodule.mem_top
      simpa using hv
  have : Fintype V := Fintype.ofFinite V
  have : Finite (V → V) := Finite.of_fintype (V → V)
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun φ : Module.End F V => (φ : V → V))
      (fun a b h => LinearMap.ext fun v => congrFun h v)
  have : Nontrivial (Subring.centralizer T) :=
    ⟨⟨1, Subring.one_mem _⟩, ⟨0, Subring.zero_mem _⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩
  have : NoZeroDivisors (Subring.centralizer T) :=
    ⟨fun {a b} hab => by
      by_cases ha : (a : Module.End F V) = 0
      · exact Or.inl (Subtype.ext ha)
      · refine Or.inr (Subtype.ext ?_)
        have hab' : (a : Module.End F V) * (b : Module.End F V) = 0 := by
          have h := congrArg Subtype.val hab
          simpa using h
        apply LinearMap.ext
        intro v
        apply inj a a.2 ha
        have h := congrArg (fun φ : Module.End F V => φ v) hab'
        simpa [Module.End.mul_apply] using h⟩
  have : IsDomain (Subring.centralizer T) := NoZeroDivisors.to_isDomain _
  have hfield : IsField (Subring.centralizer T) := Finite.isDomain_to_isField _
  let _ : Field (Subring.centralizer T) := hfield.toField
  have hfC : f ∈ Subring.centralizer T := Subring.mem_centralizer_iff.2 hf
  have hgC : g ∈ Subring.centralizer T := Subring.mem_centralizer_iff.2 hg
  have h := congrArg Subtype.val (mul_comm (⟨f, hfC⟩ : Subring.centralizer T) ⟨g, hgC⟩)
  simpa using h

end CFSG.HardMathSupport.Curtis.Proving

end
