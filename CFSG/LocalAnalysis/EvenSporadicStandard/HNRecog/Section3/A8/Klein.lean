module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma mem_alt_mul_swap (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

private lemma mem_alt_mul_swap_four (a b c d e f g h : Fin 8) (hab : a ≠ b) (hcd : c ≠ d)
    (hef : e ≠ f) (hgh : g ≠ h) :
    Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h ∈
      alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd, Equiv.Perm.sign_swap hef, Equiv.Perm.sign_swap hgh]
  decide

private lemma cycleType_mul_four_swap (a b c d e f g h : Fin 8)
    (habcd : [a, b, c, d].Nodup) (hefgh : [e, f, g, h].Nodup)
    (h1 : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap e f))
    (h2 : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap g h))
    (h3 : Equiv.Perm.Disjoint (Equiv.swap c d) (Equiv.swap e f))
    (h4 : Equiv.Perm.Disjoint (Equiv.swap c d) (Equiv.swap g h)) :
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h).cycleType =
      {2, 2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap a b * Equiv.swap c d)
      (Equiv.swap e f * Equiv.swap g h) :=
    (h1.mul_left h3).mul_right (h2.mul_left h4)
  rw [show Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h =
      (Equiv.swap a b * Equiv.swap c d) * (Equiv.swap e f * Equiv.swap g h) by group]
  rw [hd.cycleType_mul, Equiv.Perm.cycleType_swap_mul_swap_of_nodup habcd,
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup hefgh]
  decide

private def kx : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, mem_alt_mul_swap 0 1 2 3 (by decide) (by decide)⟩

private def kTwoTwoY : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, mem_alt_mul_swap 0 2 1 3 (by decide) (by decide)⟩

private def kTwoFourY : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5 * Equiv.swap 6 7,
    mem_alt_mul_swap_four 0 2 1 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide)⟩

theorem exists_klein_two_two : ∃ x y : alternatingGroup (Fin 8),
    (x : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧ (y : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
    ((x * y : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧ x * y = y * x := by
  refine ⟨kx, kTwoTwoY, ?_, ?_, ?_, ?_⟩
  · exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
  · exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (x := 0) (y := 2) (z := 1) (t := 3) (by decide)
  · have h : ((kx * kTwoTwoY : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        Equiv.swap 0 3 * Equiv.swap 1 2 := by decide +kernel
    rw [h]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (x := 0) (y := 3) (z := 1) (t := 2) (by decide)
  · decide +kernel

theorem exists_klein_two_two_four : ∃ x y : alternatingGroup (Fin 8),
    (x : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧ (y : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} ∧
    ((x * y : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} ∧
      x * y = y * x := by
  refine ⟨kx, kTwoFourY, ?_, ?_, ?_, ?_⟩
  · exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
  · exact cycleType_mul_four_swap 0 2 1 3 4 5 6 7 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · have h : ((kx * kTwoFourY : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 4 5 * Equiv.swap 6 7 := by decide +kernel
    rw [h]
    exact cycleType_mul_four_swap 0 3 1 2 4 5 6 7 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · decide +kernel

private lemma exists_involution_centralizing {G : Type} [Group G] {a w : G} {K : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥K) {x y : alternatingGroup (Fin 8)}
    (hx : IsConj a ((φ x : ↥K) : G)) (hy : IsConj w ((φ y : ↥K) : G))
    (hxy : IsConj w ((φ (x * y) : ↥K) : G))
    (hysq : y ^ 2 = 1) (hcomm : x * y = y * x) :
    ∃ b₀ : G, b₀ ∈ Gx a ∧ b₀ ^ 2 = 1 ∧ IsConj w b₀ ∧ IsConj w (a * b₀) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  let g' : G := g⁻¹
  have hg' : g' * ((φ x : ↥K) : G) * g'⁻¹ = a := by
    show g⁻¹ * ((φ x : ↥K) : G) * (g⁻¹)⁻¹ = a
    rw [← hg]
    group
  let b₀ : G := g' * ((φ y : ↥K) : G) * g'⁻¹
  have hb0def : b₀ = g' * ((φ y : ↥K) : G) * g'⁻¹ := rfl
  have hcommφ : ((φ x : ↥K) : G) * ((φ y : ↥K) : G) =
      ((φ y : ↥K) : G) * ((φ x : ↥K) : G) := by
    have h := congrArg (fun t : alternatingGroup (Fin 8) => ((φ t : ↥K) : G)) hcomm
    simpa [map_mul] using h
  have hφmul : ((φ (x * y) : ↥K) : G) =
      ((φ x : ↥K) : G) * ((φ y : ↥K) : G) := by
    rw [map_mul]
    rfl
  refine ⟨b₀, ?_, ?_, ?_, ?_⟩
  · rw [mem_Gx]
    have h1 : a * b₀ = g' * (((φ x : ↥K) : G) * ((φ y : ↥K) : G)) * g'⁻¹ := by
      rw [hb0def, ← hg']
      group
    have h2 : b₀ * a = g' * (((φ x : ↥K) : G) * ((φ y : ↥K) : G)) * g'⁻¹ := by
      rw [hb0def, ← hg', hcommφ]
      group
    rw [h1, h2]
  · have hysq' : ((φ y : ↥K) : G) ^ 2 = 1 := by
      have h := congrArg (fun t : alternatingGroup (Fin 8) => ((φ t : ↥K) : G)) hysq
      simpa [map_pow] using h
    rw [hb0def, conj_pow, hysq']
    simp
  · exact hy.trans (isConj_iff.2 ⟨g', by rw [hb0def]⟩)
  · have hab0 : a * b₀ = g' * ((φ (x * y) : ↥K) : G) * g'⁻¹ := by
      rw [hb0def, ← hg', hφmul]
      group
    exact hxy.trans (isConj_iff.2 ⟨g', by rw [hab0]⟩)

theorem exists_two_A_two_B {G : Type} [Group G] {a z : G} (hA8 : A8Shapes a z) {K : Subgroup G}
    (hK : K ≤ Gx a) (φ : alternatingGroup (Fin 8) ≃* ↥K) :
    ∃ b₀ u₀ : G, b₀ ∈ Gx a ∧ u₀ ∈ Gx a ∧ b₀ ^ 2 = 1 ∧ u₀ ^ 2 = 1 ∧
      IsConj a b₀ ∧ IsConj a (a * b₀) ∧ IsConj z u₀ ∧ IsConj z (a * u₀) := by
  obtain ⟨x₁, y₁, hx₁, hy₁, hxy₁, hcomm₁⟩ := exists_klein_two_two
  obtain ⟨x₂, y₂, hx₂, hy₂, hxy₂, hcomm₂⟩ := exists_klein_two_two_four
  have hy₁sq : y₁ ^ 2 = 1 := (sq_eq_one_of_cycleType_two_two hy₁).1
  have hy₂sq : y₂ ^ 2 = 1 := (sq_eq_one_of_cycleType_two_two_two_two hy₂).1
  obtain ⟨b₀, hb0mem, hb0sq, hb0A, hab0A⟩ :=
    exists_involution_centralizing φ (hA8.shape_2211 K hK φ x₁ hx₁)
      (hA8.shape_2211 K hK φ y₁ hy₁) (hA8.shape_2211 K hK φ (x₁ * y₁) hxy₁) hy₁sq hcomm₁
  obtain ⟨u₀, hu0mem, hu0sq, hu0B, hau0B⟩ :=
    exists_involution_centralizing φ (hA8.shape_2211 K hK φ x₂ hx₂)
      (hA8.shape_2222 K hK φ y₂ hy₂) (hA8.shape_2222 K hK φ (x₂ * y₂) hxy₂) hy₂sq hcomm₂
  exact ⟨b₀, u₀, hb0mem, hu0mem, hb0sq, hu0sq, hb0A, hab0A, hu0B, hau0B⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
