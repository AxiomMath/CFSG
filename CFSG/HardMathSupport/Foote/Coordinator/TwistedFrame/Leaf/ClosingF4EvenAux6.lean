module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux5

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Abelian

variable {L : Type} [Field L] [CharP L 2]

@[expose] def R5 : List (Fin Tag.F4.rank → ℤ) := [g5, x1110n, z0122, w1221n, v0100n]

theorem R5_data : ∀ r ∈ R5, r ∈ rootFinset Tag.F4 := by decide +kernel

theorem R5_nil : ∀ r ∈ R5, ∀ r' ∈ R5, r ≠ r' → r ≠ -r' ∧
    ∀ p ∈ commCandidates, p.1 • r + p.2 • r' ∉ rootFinset Tag.F4 := by decide +kernel

theorem R5_commute : ∀ r ∈ R5, ∀ r' ∈ R5, ∀ c d : L,
    Commute (pinnedX Tag.F4 L r c) (pinnedX Tag.F4 L r' d) := by
  intro r hr r' hr' c d
  by_cases h : r = r'
  · subst h
    show pinnedX Tag.F4 L r c * pinnedX Tag.F4 L r d = pinnedX Tag.F4 L r d * pinnedX Tag.F4 L r c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · obtain ⟨hne', hn⟩ := R5_nil r hr r' hr' h
    refine commute_pinnedX_of_commPairs_nil Tag.F4 L (mem_rootFinset.1 (R5_data r hr))
      (mem_rootFinset.1 (R5_data r' hr')) h hne' ?_ c d
    apply List.eq_nil_iff_forall_not_mem.2
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_commPairs.1 hp
    exact hn p hp1 (mem_rootFinset.2 hp2)

@[expose] def S5 : Set (ModGL Tag.F4 L) := {y | ∃ r ∈ R5, ∃ d : L, y = pinnedX Tag.F4 L r d}

theorem S5_comm : ∀ x ∈ S5 (L := L), ∀ y ∈ S5 (L := L), x * y = y * x := by
  rintro _ ⟨r, hr, c, rfl⟩ _ ⟨r', hr', d, rfl⟩
  exact (R5_commute r hr r' hr' c d).eq

theorem cg_helper {G : Type*} [CommGroup G] (a1 a2 a3 a4 a5 b1 b3 b5 : G) :
    (a1 * a2 * a3 * a4 * a5) * (b1 * a2 * b3 * a4 * b5)⁻¹ =
      (a1 * b1⁻¹) * (a3 * b3⁻¹) * (a5 * b5⁻¹) := by
  have e : (a1 * a2 * a3 * a4 * a5) * (b1 * a2 * b3 * a4 * b5)⁻¹ =
      (a1 * b1⁻¹) * (a2 * a2⁻¹) * (a3 * b3⁻¹) * (a4 * a4⁻¹) * (a5 * b5⁻¹) := by
    simp only [mul_inv_rev]
    ac_rfl
  rw [e]
  simp

theorem five_cancel (d₁ d₁' x d₃ d₃' w d₅ d₅' : L) :
    (pinnedX Tag.F4 L g5 d₁ * pinnedX Tag.F4 L x1110n x * pinnedX Tag.F4 L z0122 d₃ *
        pinnedX Tag.F4 L w1221n w * pinnedX Tag.F4 L v0100n d₅) *
      (pinnedX Tag.F4 L g5 d₁' * pinnedX Tag.F4 L x1110n x * pinnedX Tag.F4 L z0122 d₃' *
        pinnedX Tag.F4 L w1221n w * pinnedX Tag.F4 L v0100n d₅')⁻¹ =
      pinnedX Tag.F4 L g5 (d₁ - d₁') * pinnedX Tag.F4 L z0122 (d₃ - d₃') *
        pinnedX Tag.F4 L v0100n (d₅ - d₅') := by
  letI : CommGroup (Subgroup.closure (S5 (L := L))) := Subgroup.closureCommGroupOfComm (fun x hx y hy _ => S5_comm x hx y hy)
  have mem : ∀ r ∈ R5, ∀ d : L, pinnedX Tag.F4 L r d ∈ Subgroup.closure (S5 (L := L)) :=
    fun r hr d => Subgroup.subset_closure ⟨r, hr, d, rfl⟩
  have h1 : g5 ∈ R5 := by simp [R5]
  have h2 : x1110n ∈ R5 := by simp [R5]
  have h3 : z0122 ∈ R5 := by simp [R5]
  have h4 : w1221n ∈ R5 := by simp [R5]
  have h5 : v0100n ∈ R5 := by simp [R5]
  have key := cg_helper (⟨pinnedX Tag.F4 L g5 d₁, mem _ h1 _⟩ : Subgroup.closure (S5 (L := L)))
    ⟨pinnedX Tag.F4 L x1110n x, mem _ h2 _⟩ ⟨pinnedX Tag.F4 L z0122 d₃, mem _ h3 _⟩
    ⟨pinnedX Tag.F4 L w1221n w, mem _ h4 _⟩ ⟨pinnedX Tag.F4 L v0100n d₅, mem _ h5 _⟩
    ⟨pinnedX Tag.F4 L g5 d₁', mem _ h1 _⟩ ⟨pinnedX Tag.F4 L z0122 d₃', mem _ h3 _⟩
    ⟨pinnedX Tag.F4 L v0100n d₅', mem _ h5 _⟩
  have := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [this]
  simp only [pinnedX_neg, sub_eq_add_neg, pinnedX_add]


theorem comm_core {G : Type*} [Group G] (A B Y X Z W V P : G) (hAA : A * A = 1)
    (hYY : Y * Y = 1) (hAi : A⁻¹ = A) (hBi : B⁻¹ = B) (hYi : Y⁻¹ = Y) (hXi : X⁻¹ = X)
    (hBY : B * Y * B * Y = X * Z) (hAY : A * Y * A * Y = W * V) (hAX : A * X * A * X = P)
    (hAZ : A * Z = Z * A) :
    (A * B) * Y * (A * B)⁻¹ * Y⁻¹ = P * X * Z * W * V := by
  have hAXA : A * X * A = P * X := by
    calc A * X * A = (A * X * A * X) * X⁻¹ := by group
      _ = P * X := by rw [hAX, hXi]
  have e1 : (A * B) * Y * (A * B)⁻¹ * Y⁻¹ = A * (B * Y * B * Y) * Y * A * Y := by
    rw [mul_inv_rev, hAi, hBi, hYi]
    calc A * B * Y * (B * A) * Y = A * B * Y * B * 1 * A * Y := by group
      _ = A * B * Y * B * (Y * Y) * A * Y := by rw [hYY]
      _ = _ := by group
  rw [e1, hBY]
  calc A * (X * Z) * Y * A * Y = A * X * Z * (A * A) * Y * A * Y := by rw [hAA]; group
    _ = (A * X * Z * A) * (A * Y * A * Y) := by group
    _ = (A * X * Z * A) * (W * V) := by rw [hAY]
    _ = ((A * X * A) * Z) * (W * V) := by
        congr 1
        calc A * X * Z * A = A * X * (Z * A) := by group
          _ = A * X * (A * Z) := by rw [← hAZ]
          _ = (A * X * A) * Z := by group
    _ = P * X * Z * W * V := by rw [hAXA]; group

theorem comm_vY (a b t : L) :
    (pinnedX Tag.F4 L rB23 a * pinnedX Tag.F4 L pB23 b) * pinnedX Tag.F4 L negT t *
        (pinnedX Tag.F4 L rB23 a * pinnedX Tag.F4 L pB23 b)⁻¹ * (pinnedX Tag.F4 L negT t)⁻¹ =
      pinnedX Tag.F4 L g5 (a * b * t) * pinnedX Tag.F4 L x1110n (b * t) *
        pinnedX Tag.F4 L z0122 (b ^ 2 * t) * pinnedX Tag.F4 L w1221n (a * t) *
        pinnedX Tag.F4 L v0100n (a ^ 2 * t) := by
  have hAX := rel_rB23_x1110n a (b * t)
  rw [show a * (b * t) = a * b * t by ring] at hAX
  exact comm_core _ _ _ _ _ _ _ _ (pinnedX_mul_self _ _) (pinnedX_mul_self _ _)
    (pinnedX_inv_self _ _) (pinnedX_inv_self _ _) (pinnedX_inv_self _ _) (pinnedX_inv_self _ _)
    (rel_pB23_negT b t) (rel_rB23_negT a t) hAX (commute_rB23_z0122 (L := L) a (b ^ 2 * t)).eq

end Abelian

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
