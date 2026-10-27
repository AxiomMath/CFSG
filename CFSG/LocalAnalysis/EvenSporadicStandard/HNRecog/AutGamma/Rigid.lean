module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.SixA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem isConjOrbit_orb2A (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb2A a a) :=
  hL.tableV.self.partition.orbit 0

theorem isConjOrbit_orb3A (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb3A a a) :=
  hL.tableVII.self.partition.orbit 0

theorem act_fix_of_fix_mul (hF : IsF5Type a z) (hL : F5Local G a z) (τ : Gamma a ≃g Gamma a)
    {x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) (hfy : act τ y = y)
    (hfxy : act τ (x * y) = x * y) : act τ x = x := by
  have hyy : y * y = 1 := mul_self_of_isConj hF hy
  have hx' : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
  have hxy2 : IsConj a (x * y * y) := by rw [hx']; exact hx
  have h := act_fix_mul hF hL.lines.self τ hxy hy hxy2 hfxy hfy
  rwa [hx'] at h

theorem act_base_of_fix_two (hF : IsF5Type a z) (hL : F5Local G a z) (τ : Gamma a ≃g Gamma a)
    (h2 : ∀ x ∈ orb2A a a, act τ x = x) : act τ a = a := by
  obtain ⟨b, hb⟩ := (isConjOrbit_orb2A hL).nonempty
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  have hab : a * b ∈ orb2A a a := by
    refine ⟨hb.2, ?_⟩
    rw [← mul_assoc, haa, one_mul]
    exact hb.1
  exact act_fix_of_fix_mul hF hL τ (IsConj.refl a) hb.1 hb.2 (h2 b hb) (h2 _ hab)

theorem eq_one_of_fix_two_three (hF : IsF5Type a z) (hL : F5Local G a z)
    (hlines : LinesThrough a z) (τ : Gamma a ≃g Gamma a) (h2 : ∀ x ∈ orb2A a a, act τ x = x)
    (h3 : ∀ x ∈ orb3A a a, act τ x = x) : τ = 1 := by
  have ha : act τ a = a := act_base_of_fix_two hF hL τ h2
  have hfix : ∀ {x y : G}, IsConj a x → IsConj a y → IsConj a (x * y) → act τ y = y →
      act τ (x * y) = x * y → act τ x = x :=
    fun hx hy hxy hfy hfxy => act_fix_of_fix_mul hF hL τ hx hy hxy hfy hfxy
  have f2B : ∀ x ∈ orb2B a z a, act τ x = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hlines.two_B x hx
    exact hfix hx.1 hy.1 hxy.1 (h2 y hy) (h2 _ hxy)
  have f6A : ∀ x ∈ orb6A a a, act τ x = x := by
    intro x hx
    have hb := sixA_pow_mem_orb2A hF hx
    have hc := sixA_mul_mem_orb3A hF hL hx
    have hbb : (a * x) ^ 3 * (a * x) ^ 3 = 1 := mul_self_of_isConj hF hb.1
    have hx' : (a * x) ^ 3 * ((a * x) ^ 3 * x) = x := by rw [← mul_assoc, hbb, one_mul]
    have hxc : IsConj a ((a * x) ^ 3 * ((a * x) ^ 3 * x)) := by rw [hx']; exact hx.1
    have h := act_fix_mul hF hL.lines.self τ hb.1 hc.1 hxc (h2 _ hb) (h3 _ hc)
    rwa [hx'] at h
  have f4B : ∀ x ∈ orb4B a a, act τ x = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hlines.four_B x hx
    exact hfix hx.1 hy.1 hxy.1 (h3 y hy) (h3 _ hxy)
  have f5A : ∀ x ∈ orb5A a a, act τ x = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hlines.five_A x hx
    exact hfix hx.1.1 hy.1 hxy.1 (f4B y hy) (f6A _ hxy)
  have f5E : ∀ x ∈ orb5E a a, act τ x = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hlines.five_E x hx
    exact hfix hx.1.1 hy.1 hxy.1 (f4B y hy) (f6A _ hxy)
  have f4A : ∀ x ∈ orb4A a z a, act τ x = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hlines.four_A x hx
    exact hfix hx.1 hy.1 hxy.1 (f4B y hy) (f4B _ hxy)
  refine eq_one_of_act τ fun x hx => ?_
  have hg : x ∈ gammaSet a z a := hL.gamma.self.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hg
  rcases hg with ((((((((h1 | h2') | h3') | h4) | h5) | h6) | h7) | h8) | h9)
  · rw [h1]; exact ha
  · exact h2 x h2'
  · exact f2B x h3'
  · exact h3 x h4
  · exact f4A x h5
  · exact f4B x h6
  · exact f5A x h7
  · exact f5E x h8
  · exact f6A x h9

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
