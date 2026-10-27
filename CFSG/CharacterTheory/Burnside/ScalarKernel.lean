module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace Burnside.ScalarKernel

universe u v

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

def projectiveKernel (ρ : Representation ℂ G V) : Subgroup G :=
  Subgroup.comap ρ.asGroupHom (Subgroup.center ((Module.End ℂ V)ˣ))

instance (ρ : Representation ℂ G V) : (projectiveKernel ρ).Normal :=
  Subgroup.normal_comap ρ.asGroupHom

private theorem mem_projectiveKernel_of_eq_smul_id (ρ : Representation ℂ G V)
    {g : G} {c : ℂ} (hg : ρ g = c • LinearMap.id) :
    g ∈ projectiveKernel ρ := by
  change ρ.asGroupHom g ∈ Subgroup.center ((Module.End ℂ V)ˣ)
  rw [Subgroup.mem_center_iff]
  intro A
  apply Units.ext
  change (A : Module.End ℂ V) * ρ g = ρ g * (A : Module.End ℂ V)
  rw [hg]
  ext x
  simp

theorem no_nonidentity_scalar_of_isSimpleGroup
    [Finite G] [IsSimpleGroup G]
    (ρ : Representation ℂ G V)
    (hρ : ρ ≠ 1) (hnoncomm : ¬ ∀ x y : G, x * y = y * x) :
    ∀ {g : G}, g ≠ 1 → ¬ ∃ c : ℂ, ρ g = c • LinearMap.id := by
  have hker_ne_top : ρ.asGroupHom.ker ≠ ⊤ := by
    intro hker
    apply hρ
    ext x v
    have hxmem : x ∈ ρ.asGroupHom.ker := by rw [hker]; trivial
    have hxunit : ρ.asGroupHom x = 1 := hxmem
    have hxend := congrArg (fun A : (Module.End ℂ V)ˣ => (A : Module.End ℂ V)) hxunit
    have hxmap : ρ x = 1 := by
      simpa only [Representation.asGroupHom_apply, Units.val_one] using hxend
    simp only [hxmap, MonoidHom.one_apply]
  have hker_bot : ρ.asGroupHom.ker = ⊥ := by
    rcases (haveI := (MonoidHom.normal_ker ρ.asGroupHom); IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.asGroupHom.ker) with h | h
    · exact h
    · exact (hker_ne_top h).elim
  have hρinj : Function.Injective ρ.asGroupHom :=
    (MonoidHom.ker_eq_bot_iff ρ.asGroupHom).mp hker_bot
  intro g hg ⟨c, hc⟩
  have hgmem : g ∈ projectiveKernel ρ :=
    mem_projectiveKernel_of_eq_smul_id ρ hc
  have hprojective_ne_bot : projectiveKernel ρ ≠ ⊥ := by
    intro hbot
    have : g ∈ (⊥ : Subgroup G) := hbot ▸ hgmem
    exact hg (Subgroup.mem_bot.mp this)
  have hprojective_top : projectiveKernel ρ = ⊤ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (projectiveKernel ρ)) with h | h
    · exact (hprojective_ne_bot h).elim
    · exact h
  apply hnoncomm
  intro x y
  apply hρinj
  rw [map_mul, map_mul]
  have hxcenter : ρ.asGroupHom x ∈ Subgroup.center ((Module.End ℂ V)ˣ) := by
    have hxmem : x ∈ projectiveKernel ρ := by rw [hprojective_top]; trivial
    exact hxmem
  exact ((Subgroup.mem_center_iff.mp hxcenter) (ρ.asGroupHom y)).symm

end Burnside.ScalarKernel

end CFSG
