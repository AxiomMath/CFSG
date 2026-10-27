module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem q8_facts : (QuaternionGroup.a (1 : ZMod (2 * 2)) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2) ∧
    (QuaternionGroup.xa (0 : ZMod (2 * 2)) * QuaternionGroup.xa 0 = QuaternionGroup.a 2) ∧
    (QuaternionGroup.xa (0 : ZMod (2 * 2)) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a 1)⁻¹) ∧
    (∀ q : QuaternionGroup 2, ∃ k : Fin 4, q = QuaternionGroup.a 1 ^ (k : ℕ) ∨
      q = QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ (k : ℕ)) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem exists_quat_gens {G : Type} [Group G] {R : Subgroup G} {t : G}
    (e : ↥R ≃* QuaternionGroup 2) (hu : IsUniqueInvolution R t) :
    ∃ i j : G, i ∈ R ∧ j ∈ R ∧ i * i = t ∧ j * j = t ∧ j * i * j⁻¹ = i⁻¹ ∧
      ∀ r ∈ R, ∃ k : ℕ, r = i ^ k ∨ r = j * i ^ k := by
  obtain ⟨h1, h2, h3, h4⟩ := q8_facts
  set ι : ↥R := e.symm (QuaternionGroup.a 1) with hι
  set κ : ↥R := e.symm (QuaternionGroup.xa 0) with hκ
  have ht : e.symm (QuaternionGroup.a 2) = ⟨t, hu.mem⟩ := by
    set u := e.symm (QuaternionGroup.a 2) with hu'
    have hsq : u * u = 1 := by
      rw [hu', ← map_mul]
      have : QuaternionGroup.a (2 : ZMod (2 * 2)) * QuaternionGroup.a 2 = 1 := by decide
      rw [this, map_one]
    have hne : u ≠ 1 := by
      intro h
      have := congrArg e h
      rw [hu', MulEquiv.apply_symm_apply, map_one] at this
      exact absurd this (by decide)
    have := hu.unique (u : G) u.2 (by
      have := congrArg Subtype.val hsq
      simpa using this)
    rcases this with h | h
    · exact absurd (Subtype.ext h) hne
    · exact Subtype.ext h
  refine ⟨ι, κ, ι.2, κ.2, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (show ι * ι = ⟨t, hu.mem⟩ by rw [hι, ← map_mul, h1, ht])
    simpa using this
  · have := congrArg Subtype.val (show κ * κ = ⟨t, hu.mem⟩ by rw [hκ, ← map_mul, h2, ht])
    simpa using this
  · have := congrArg Subtype.val (show κ * ι * κ⁻¹ = ι⁻¹ by
      rw [hκ, hι, ← map_inv, ← map_mul, ← map_mul, h3, map_inv])
    simpa using this
  · intro r hr
    obtain ⟨k, hk⟩ := h4 (e ⟨r, hr⟩)
    refine ⟨k, ?_⟩
    rcases hk with hk | hk
    · left
      have : (⟨r, hr⟩ : ↥R) = ι ^ (k : ℕ) := by
        rw [hι, ← map_pow, ← hk]; simp
      simpa using congrArg Subtype.val this
    · right
      have : (⟨r, hr⟩ : ↥R) = κ * ι ^ (k : ℕ) := by
        rw [hι, hκ, ← map_pow, ← map_mul, ← hk]; simp
      simpa using congrArg Subtype.val this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
