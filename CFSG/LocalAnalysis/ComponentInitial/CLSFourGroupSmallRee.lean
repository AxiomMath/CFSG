module

public import CFSG.LieType.Ree.SmallReeThreeDerived
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem small_Ree_prime_field_derived_fixed_four_group (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (k : Type) [Field k] [Finite k] [CharP k ReeTag.G2.prime]
    (hk : Nat.card k = 3) (ι : k →+* K) :
    Nat.card (⁅ReeTag.G2.reeGamma k 0, ReeTag.G2.reeGamma k 0⁆ :
      Subgroup (ModGL ReeTag.G2.tag k)) = 504 ∧
    Function.Injective (baseChangeGL (τ := ReeTag.G2.tag) ι) ∧
    ⁅ReeTag.G2.reeGamma k 0, ReeTag.G2.reeGamma k 0⁆.map (baseChangeGL ι) ≤
      ReeTag.G2.reeGamma K a ∧
    ∃ A : Subgroup (ModGL ReeTag.G2.tag K),
      A ≤ ⁅ReeTag.G2.reeGamma k 0, ReeTag.G2.reeGamma k 0⁆.map (baseChangeGL ι) ∧
      A ≤ ReeTag.G2.reeGamma K a ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  classical
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.G2.tag).length
  obtain ⟨-, -, -, hcard, -, hsimp, hnc, hder⟩ := small_Ree_three_derived_simple k hk w₀ hw₀
  rw [hder]
  set D := Subgroup.closure {ReeTag.g2U₀ k, canonicalRep (coxeterSystem ReeTag.G2.tag) k w₀}
    with hD
  have hinj := baseChangeGL_injective (τ := ReeTag.G2.tag) ι
  have hmap : D.map (baseChangeGL ι) ≤ ReeTag.G2.reeGamma K a := by
    rw [hD, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · rw [ReeTag.g2U₀, map_mul, baseChangeGL_pinnedX, baseChangeGL_pinnedX, map_one]
      exact ReeTag.g2U₀_mem_reeGamma K a
    · rw [baseChangeGL_canonicalRep]
      exact ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hZ : Odd (Nat.card (Subgroup.center D)) := by
    rw [center_eq_bot_of_isSimpleGroup hnc, Subgroup.card_bot]
    exact odd_one
  obtain ⟨A₀, ⟨hc, hp⟩, hcard₀⟩ := exists_four_group_of_two_le_pRank
    (two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hnc) hZ)
  set f : D →* ModGL ReeTag.G2.tag K := (baseChangeGL ι).comp D.subtype with hf
  have hfinj : Function.Injective f := hinj.comp D.subtype_injective
  have hfD : ∀ x : D, f x ∈ D.map (baseChangeGL ι) := fun x => ⟨x, x.2, rfl⟩
  refine ⟨hcard, hinj, hmap, A₀.map f, ?_, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hfD x
  · rintro _ ⟨x, -, rfl⟩
    exact hmap (hfD x)
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]
  · rw [Subgroup.card_map_of_injective hfinj, hcard₀]

end CFSG.LocalAnalysis.ComponentInitial
