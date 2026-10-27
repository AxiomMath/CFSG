module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Descent

variable {G : Type*} [Group G] {K : Type*} [AddCommGroup K]

theorem coord_inv_mul_eq_zero {X : Subgroup G} {l : G → K}
    (hl : ∀ x ∈ X, ∀ x' ∈ X, l (x * x') = l x + l x') {g x : G} (hg : g ∈ X) (hx : x ∈ X)
    (hgx : l g = l x) : l (g⁻¹ * x) = 0 := by
  have h1 := hl g hg (g⁻¹ * x) (mul_mem (inv_mem hg) hx)
  rw [mul_inv_cancel_left, hgx] at h1
  exact add_eq_left.mp h1.symm

theorem exists_biadditive_of_descends {X Y : Subgroup G} {l r : G → K} {P : G → G → K}
    (hl : ∀ x ∈ X, ∀ x' ∈ X, l (x * x') = l x + l x') (hls : ∀ w, ∃ x ∈ X, l x = w)
    (hr : ∀ y ∈ Y, ∀ y' ∈ Y, r (y * y') = r y + r y') (hrs : ∀ z, ∃ y ∈ Y, r y = z)
    (hP1 : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, P (x * x') y = P x y + P x' y)
    (hP2 : ∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, P x (y * y') = P x y + P x y')
    (hPl : ∀ x ∈ X, l x = 0 → ∀ y ∈ Y, P x y = 0)
    (hPr : ∀ y ∈ Y, r y = 0 → ∀ x ∈ X, P x y = 0) :
    ∃ B : K → K → K, (∀ w w' z, B (w + w') z = B w z + B w' z) ∧
      (∀ w z z', B w (z + z') = B w z + B w z') ∧ ∀ x ∈ X, ∀ y ∈ Y, P x y = B (l x) (r y) := by
  choose sl hslX hsl using hls
  choose sr hsrY hsr using hrs
  have key : ∀ x ∈ X, ∀ y ∈ Y, P x y = P (sl (l x)) (sr (r y)) := by
    intro x hx y hy
    have hmx : (sl (l x))⁻¹ * x ∈ X := mul_mem (inv_mem (hslX _)) hx
    have hmy : (sr (r y))⁻¹ * y ∈ Y := mul_mem (inv_mem (hsrY _)) hy
    have h0x := coord_inv_mul_eq_zero hl (hslX _) hx (hsl _)
    have h0y := coord_inv_mul_eq_zero hr (hsrY _) hy (hsr _)
    calc P x y = P (sl (l x) * ((sl (l x))⁻¹ * x)) y := by rw [mul_inv_cancel_left]
      _ = P (sl (l x)) y := by rw [hP1 _ (hslX _) _ hmx y hy, hPl _ hmx h0x y hy, add_zero]
      _ = P (sl (l x)) (sr (r y) * ((sr (r y))⁻¹ * y)) := by rw [mul_inv_cancel_left]
      _ = P (sl (l x)) (sr (r y)) := by
          rw [hP2 _ (hslX _) _ (hsrY _) _ hmy, hPr _ hmy h0y _ (hslX _), add_zero]
  refine ⟨fun w z => P (sl w) (sr z), fun w w' z => ?_, fun w z z' => ?_, key⟩
  · show P (sl (w + w')) (sr z) = P (sl w) (sr z) + P (sl w') (sr z)
    have h1 := key _ (mul_mem (hslX w) (hslX w')) _ (hsrY z)
    rw [hl _ (hslX w) _ (hslX w'), hsl, hsl, hsr] at h1
    rw [← h1, hP1 _ (hslX w) _ (hslX w') _ (hsrY z)]
  · show P (sl w) (sr (z + z')) = P (sl w) (sr z) + P (sl w) (sr z')
    have h1 := key _ (hslX w) _ (mul_mem (hsrY z) (hsrY z'))
    rw [hr _ (hsrY z) _ (hsrY z'), hsl, hsr, hsr] at h1
    rw [← h1, hP2 _ (hslX w) _ (hsrY z) _ (hsrY z')]

theorem exists_additive_of_descends {X : Subgroup G} {l F : G → K}
    (hl : ∀ x ∈ X, ∀ x' ∈ X, l (x * x') = l x + l x') (hls : ∀ w, ∃ x ∈ X, l x = w)
    (hF : ∀ x ∈ X, ∀ x' ∈ X, F (x * x') = F x + F x') (hF0 : ∀ x ∈ X, l x = 0 → F x = 0) :
    ∃ S : K → K, (∀ w w', S (w + w') = S w + S w') ∧ ∀ x ∈ X, F x = S (l x) := by
  choose sl hslX hsl using hls
  have key : ∀ x ∈ X, F x = F (sl (l x)) := by
    intro x hx
    have hm : (sl (l x))⁻¹ * x ∈ X := mul_mem (inv_mem (hslX _)) hx
    have h0 := coord_inv_mul_eq_zero hl (hslX _) hx (hsl _)
    calc F x = F (sl (l x) * ((sl (l x))⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = F (sl (l x)) := by rw [hF _ (hslX _) _ hm, hF0 _ hm h0, add_zero]
  refine ⟨fun w => F (sl w), fun w w' => ?_, key⟩
  show F (sl (w + w')) = F (sl w) + F (sl w')
  have h1 := key _ (mul_mem (hslX w) (hslX w'))
  rw [hl _ (hslX w) _ (hslX w'), hsl, hsl] at h1
  rw [← h1, hF _ (hslX w) _ (hslX w')]

end Descent

section ClassTwo

variable {G : Type*} [Group G]

theorem sq_mul_sq_comm {M N A : Subgroup G}
    (hMN : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hN2 : ∀ n ∈ N, n ^ 2 = 1)
    (hNA : ∀ m ∈ M, ∀ n ∈ N, n⁻¹ * (m * n * m⁻¹) ∈ A)
    (hA : ∀ m ∈ M, ∀ b ∈ A, m * b * m⁻¹ = b) (hA2 : ∀ b ∈ A, b ^ 2 = 1)
    {x y : G} (hx : x ∈ M) (hy : y ∈ M) : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
  have hn := hMN x hx y hy
  have hnn : x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hN2 _ hn)
  have hc : x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹ ∈ A := by
    have e : x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * y * x⁻¹ * y⁻¹) * y⁻¹) := by simp only [sq]; group
    rw [e]
    nth_rewrite 1 [hnn]
    exact hNA y hy _ hn
  have hcc := hA x hx _ hc
  have h1 : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ = 1 := by
    calc x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ =
        (x * (x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹) * x⁻¹) * (x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹) := by
          simp only [sq]; group
      _ = (x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹) ^ 2 := by rw [hcc]; exact (sq _).symm
      _ = 1 := hA2 _ hc
  calc x ^ 2 * y ^ 2 = x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ * (y ^ 2 * x ^ 2) := by group
    _ = y ^ 2 * x ^ 2 := by rw [h1, one_mul]

end ClassTwo

end CFSG.SeitzReduction.RankOne
