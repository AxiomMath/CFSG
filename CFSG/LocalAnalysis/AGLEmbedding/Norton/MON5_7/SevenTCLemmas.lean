module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

variable {G : Type*} [Group G]

theorem conj_mem_closure_pair {a b g : G} (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) :
    ∀ u ∈ Subgroup.closure ({a, b} : Set G), g * u * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

theorem mem_normalizer_closure_pair [Finite G] {a b g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
  set U := Subgroup.closure ({a, b} : Set G) with hU
  have h1 := conj_mem_closure_pair ha hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hgh => ?_⟩
  let φ : U → U := fun u => ⟨g * u * g⁻¹, h1 u u.2⟩
  have hinj : Function.Injective φ := by
    intro u v huv
    have h2 := congrArg Subtype.val huv
    simp only [φ] at h2
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hinj ⟨g * h * g⁻¹, hgh⟩
  have h3 := congrArg Subtype.val hu
  simp only [φ] at h3
  have h4 : (u : G) = h := mul_left_cancel (mul_right_cancel h3)
  rw [← h4]
  exact u.2

theorem commute_of_closure_pair {a b g : G} (ha : a * g = g * a) (hb : b * g = g * b) :
    ∀ u ∈ Subgroup.closure ({a, b} : Set G), u * g = g * u := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    have hxc : Commute x g := hx
    exact hxc.inv_left.eq

theorem mem_centralizer_closure_pair {a b g : G} (ha : a * g = g * a) (hb : b * g = g * b) :
    g ∈ Subgroup.centralizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  exact fun u hu => commute_of_closure_pair ha hb u hu

end CFSG.AGLEmbedding.Norton.MON5_7
