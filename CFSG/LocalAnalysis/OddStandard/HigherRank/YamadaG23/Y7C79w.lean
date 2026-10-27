module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open CFSG.LocalAnalysis.ComponentInitial.FourGroup

variable {G : Type} [Group G] [Finite G]

theorem y7c_order7_fpf {F : Subgroup G} (hF : Nat.card F = 8) {x : G} (hx : x ^ 7 = 1)
    (hn : ∀ f ∈ F, x * f * x⁻¹ ∈ F) (hnc : ∃ f ∈ F, x * f * x⁻¹ ≠ f) {f : G} (hf : f ∈ F)
    (hfx : x * f * x⁻¹ = f) : f = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Fintype ↥F := Fintype.ofFinite ↥F
  let g : Function.End ↥F := fun y => ⟨x * (y : G) * x⁻¹, hn (y : G) y.2⟩
  have hg_apply : ∀ y : ↥F, (g y : G) = x * (y : G) * x⁻¹ := fun _ => rfl
  have hiter : ∀ n : ℕ, ∀ y : ↥F, ((g^[n]) y : G) = x ^ n * (y : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; rw [Function.iterate_zero_apply, pow_zero]; simp
    | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', hg_apply (g^[n] y), ih y]
        group
  have hg7 : g ^ 7 = 1 := by
    funext y
    apply Subtype.ext
    show ((g^[7]) y : G) = (y : G)
    rw [hiter 7 y, hx]
    simp
  have hcardF : Fintype.card ↥F = 8 :=
    (Nat.card_eq_fintype_card (α := ↥F)).symm.trans hF
  have hmod : 8 ≡ Fintype.card g.fixedPoints [MOD 7] := by
    have h := Equiv.Perm.card_fixedPoints_modEq (f := g) (p := 7) (n := 1) hg7
    rwa [hcardF] at h
  obtain ⟨w, hwF, hwne⟩ := hnc
  have hw_notfix : ¬ (⟨w, hwF⟩ : ↥F) ∈ g.fixedPoints := by
    rw [Function.mem_fixedPoints_iff]
    intro h
    exact hwne (by
      have h' := congrArg (Subtype.val) h
      rwa [hg_apply ⟨w, hwF⟩] at h')
  have hk_lt : Fintype.card g.fixedPoints < 8 := by
    have h := Fintype.card_subtype_lt (p := fun y : ↥F => y ∈ g.fixedPoints)
      (x := (⟨w, hwF⟩ : ↥F)) hw_notfix
    rwa [hcardF] at h
  have hk_le : Fintype.card g.fixedPoints ≤ 7 := by omega
  have hk_mod : Fintype.card g.fixedPoints % 7 = 1 := by
    have h := hmod
    rw [Nat.ModEq] at h
    have h8 : 8 % 7 = 1 := by norm_num
    rw [h8] at h
    exact h.symm
  have hk_eq : Fintype.card g.fixedPoints = 1 := by
    have hlt7 : Fintype.card g.fixedPoints < 7 := by
      rcases lt_or_ge (Fintype.card g.fixedPoints) 7 with h | h
      · exact h
      · have h7 : Fintype.card g.fixedPoints = 7 := le_antisymm hk_le h
        rw [h7] at hk_mod
        norm_num at hk_mod
    rw [Nat.mod_eq_of_lt hlt7] at hk_mod
    exact hk_mod
  by_contra hfne
  have htwo : 2 ≤ Fintype.card g.fixedPoints := by
    let a : g.fixedPoints := ⟨1, by
      rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; rw [hg_apply]; simp⟩
    let b : g.fixedPoints := ⟨⟨f, hf⟩, by
      rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; rw [hg_apply]; exact hfx⟩
    have hab : a ≠ b := by
      intro hab
      apply hfne
      have h := congrArg (fun z : g.fixedPoints => ((z : ↥F) : G)) hab
      simpa [a, b] using h.symm
    have h1lt : 1 < Fintype.card g.fixedPoints := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    omega
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
