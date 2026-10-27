module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitLargeEq
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairOddTau
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolIter
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepLarge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem exitLargeNat : ExitLargeNat := by
  intro V _ _ hV n hn H ψ hψ hAlt hT₁ A hA hmin ι R' hAK hC hnat htr
  classical
  have hKW := largeK_le_stabSub ψ ι R'
  set W := fixV (largeQ ψ ι R') with hW
  set κ := largeKappa ψ ι R' with hκ
  set ψW := autSubLift κ hKW hC with hψW
  have hker : ∀ k : ↥(largeK ψ ι R'), κ k = 1 → ∀ w ∈ W, (k : MulAut V) w = w :=
    fun k hk w hw => largeKappa_eq_one_fix hk hw
  have hψWinj : Function.Injective ψW := autSubLift_injective (hKW := hKW) (hC := hC) hker
  have hA'G : autSub A W ≤ autSub (largeK ψ ι R') W := autSub_mono hAK W
  have hBeq : ((autSub A W).subgroupOf (autSub (largeK ψ ι R') W)).map ψW =
      (A.subgroupOf (largeK ψ ι R')).map κ := by
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 (Subgroup.mem_subgroupOf.1 hφ)
      have hφ' : φ = autSubHom hKW ⟨g, hAK hg⟩ := Subtype.ext (by rw [← hgφ]; rfl)
      rw [hφ', hψW, autSubLift_apply]
      exact ⟨⟨g, hAK hg⟩, hg, rfl⟩
    · rintro _ ⟨k, hk, rfl⟩
      rw [← autSubLift_apply (hKW := hKW) (hC := hC)]
      exact ⟨autSubHom _ k, mem_autSub.2 ⟨Subgroup.inclusion hKW k, hk, rfl⟩, rfl⟩
  set B := (A.subgroupOf (largeK ψ ι R')).map κ with hB
  have hBexp : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hA.2.2.1.2 _ ha)
    rw [this, map_one]
  obtain ⟨a, ha, ha1⟩ : ∃ a : MulAut V, ∃ ha : a ∈ A, κ ⟨a, hAK ha⟩ ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_smul_eq B (0 : Fin 8) 1
    obtain ⟨k, hk, hkg⟩ := g.2
    refine ⟨k, hk, fun h => ?_⟩
    have h1 : κ k = 1 := h
    have h2 : (g : Perm (Fin 8)) 0 = 1 := hg
    rw [← hkg, h1, Perm.one_apply] at h2
    exact absurd h2 (by decide)
  have hΔ : ¬ IsMatchingGroup B := by
    rintro ⟨t, ht, ht2, hBt⟩
    have h2 := card_orbit_matchingGroup ht ht2 (0 : Fin 8)
    rw [← hBt, orbit_eq_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_fin] at h2
    omega
  have hle := natFF_le (by norm_num) hBexp hΔ
  obtain ⟨π, hπ, hkerπ, heqπ⟩ := hnat
  have hAB : ∀ b ∈ ((autSub A W).subgroupOf (autSub (largeK ψ ι R') W)).map ψW,
      ∃ a' ∈ autSub A W, ∀ u v : ↥(commV (autSub (largeK ψ ι R') W)), (v : ↥W) = a' u →
        Multiplicative.toAdd (π v) = altAct b (Multiplicative.toAdd (π u)) := by
    rintro _ ⟨a', ha', rfl⟩
    exact ⟨a', ha', fun u v huv => heqπ a' u v huv⟩
  have n1 := card_mul_card_inf_fixV_le (Y := ⊤) inf_le_left le_top π hπ hkerπ hAB
  rw [top_inf_eq, Subgroup.card_top, hBeq] at n1
  have hcardB : Nat.card B = Nat.card (autSub A W) := by
    rw [← hBeq, Subgroup.card_map_of_injective hψWinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'G).toEquiv
  have hAW : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W := fun b hb w hw => ((hKW (hAK hb)) w).2 hw
  have hWA : commSub W A ≠ ⊥ := fun hbot =>
    ha1 (hC ⟨a, hAK ha⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw a ha)
  have hoffW := isFFStarOffender_autSub hA hAW hWA hA'G
  have o1 : Nat.card W ≤ Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) := by
    have := hoffW.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  have o2 : Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) ≤ Nat.card W := by
    have hpos : 0 < Nat.card (altFix 8 B) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) * Nat.card (altFix 8 B)
        = Nat.card B * Nat.card (altFix 8 B) * Nat.card (fixV (autSub A W)) := by
          rw [hcardB]; ring
      _ ≤ Nat.card (altHeart 8) * Nat.card (fixV (autSub A W)) := Nat.mul_le_mul_right _ hle
      _ ≤ Nat.card W * Nat.card (altFix 8 B) := n1
  rcases natVia_or_altRho_altLift_mem_centQuot hV hψ hAlt (by norm_num) (by omega) hT₁ hA hAK hC
      ha ha1 (le_antisymm o1 o2) with h | hVE
  · exact h
  ·
    have hmemK : ∀ σ, ((altRho hψ hAlt).comp (altLift ι)) σ ∈ largeK ψ ι R' := fun σ =>
      altRho_altLift_mem_largeK hψ hAlt σ
    set e := ((altRho hψ hAlt).comp (altLift ι)).codRestrict _ hmemK with he_def
    have he : ∀ σ, κ (e σ) = σ := fun σ =>
      restrictHom_eq_of_eq_altLift (apply_altRho hψ hAlt _)
    have hshape := natShape_subtype_comp_of_natVia (by norm_num) κ hKW ψW
      (fun d => autSubLift_apply d) ⟨π, hπ, hkerπ, heqπ⟩ e he fun σ v => hVE σ v
    have heq : (largeK ψ ι R').subtype.comp e = (altRho hψ hAlt).comp (altLift ι) :=
      MonoidHom.ext fun _ => rfl
    rw [heq] at hshape
    exact natVia_commV_of_natShape (by omega) hψ hAlt
      (natShape_of_stab_lt hV (by norm_num) (by omega) ι _ hshape)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
