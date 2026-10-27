module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y7c_seven_cube_of_indep {A : Type} [Group A] [Finite A] {u₁ u₂ u₃ : A}
    (h12 : u₁ * u₂ = u₂ * u₁) (h13 : u₁ * u₃ = u₃ * u₁) (h23 : u₂ * u₃ = u₃ * u₂)
    (h : ∀ a b c : ℤ, u₁ ^ a * u₂ ^ b * u₃ ^ c = 1 → 7 ∣ a ∧ 7 ∣ b ∧ 7 ∣ c) :
    7 ^ 3 ∣ Nat.card A := by
  classical
  set u : Fin 3 → A := ![u₁, u₂, u₃] with hu
  have huv : Pairwise (fun i j : Fin 3 => Commute (u i) (u j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hu] <;>
      first
        | exact h12 | exact h12.symm
        | exact h13 | exact h13.symm
        | exact h23 | exact h23.symm
        | exact Commute.refl _
  have hcomm : Pairwise fun i j : Fin 3 =>
      ∀ x y : Multiplicative ℤ,
        Commute ((fun k => zpowersHom A (u k)) i x) ((fun k => zpowersHom A (u k)) j y) :=
    fun i j hij x y => (huv hij).zpow_zpow x.toAdd y.toAdd
  set φ : (Fin 3 → Multiplicative ℤ) →* A :=
    MonoidHom.noncommPiCoprod (fun i => zpowersHom A (u i)) hcomm with hφdef
  have hφ_ms : ∀ i y, φ (Pi.mulSingle i y) = zpowersHom A (u i) y := by
    intro i y
    rw [hφdef]
    exact MonoidHom.noncommPiCoprod_mulSingle (fun i => zpowersHom A (u i)) i y
  have hφ : ∀ g : Fin 3 → Multiplicative ℤ,
      φ g = u 0 ^ (g 0).toAdd * u 1 ^ (g 1).toAdd * u 2 ^ (g 2).toAdd := by
    intro g
    have hg : g = (Pi.mulSingle 0 (g 0) * Pi.mulSingle 1 (g 1)) * Pi.mulSingle 2 (g 2) := by
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [hg]
    rw [map_mul, map_mul, hφ_ms, hφ_ms, hφ_ms]
    rfl
  set π : (Fin 3 → Multiplicative ℤ) →* Multiplicative (Fin 3 → ZMod 7) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (fun i => ((g i).toAdd : ZMod 7))) (by
      intro g₁ g₂
      apply Multiplicative.ext
      funext i
      simp [Int.cast_add]) with hπdef
  have hπ_apply : ∀ g, π g = Multiplicative.ofAdd (fun i => ((g i).toAdd : ZMod 7)) := by
    intro g
    rw [hπdef]
    rfl
  have hsurj : Function.Surjective π := by
    intro x
    refine ⟨fun i => Multiplicative.ofAdd ((x.toAdd i).val : ℤ), ?_⟩
    apply Multiplicative.ext
    funext i
    simp [hπ_apply, ZMod.natCast_zmod_val]
  have hker : φ.ker ≤ π.ker := by
    intro g hg
    change φ g = 1 at hg
    change π g = 1
    have hg' : u 0 ^ (g 0).toAdd * u 1 ^ (g 1).toAdd * u 2 ^ (g 2).toAdd = 1 := by
      rw [← hφ g]; exact hg
    have hg₁ : u₁ ^ (g 0).toAdd * u₂ ^ (g 1).toAdd * u₃ ^ (g 2).toAdd = 1 := by
      simpa [hu] using hg'
    obtain ⟨ha, hb, hc⟩ := h _ _ _ hg₁
    rw [hπ_apply]
    have hfun : (fun i : Fin 3 => ((g i).toAdd : ZMod 7)) = 0 := by
      funext i
      fin_cases i
      · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (g 0).toAdd 7).mpr ha
      · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (g 1).toAdd 7).mpr hb
      · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (g 2).toAdd 7).mpr hc
    rw [hfun]
    rfl
  have hpi : π.ker.index = 7 ^ 3 := by
    rw [Subgroup.index_ker π, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := Fin 3 → ZMod 7))]
    simp [Nat.card_fun]
  have hmain := Subgroup.index_dvd_of_le hker
  rw [hpi, Subgroup.index_ker φ] at hmain
  exact dvd_trans hmain (Subgroup.card_subgroup_dvd_card φ.range)

end CFSG.OddStandard.HigherRank.YamadaG23
