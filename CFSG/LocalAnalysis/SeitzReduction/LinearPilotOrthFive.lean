module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImagesConj

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Units

theorem exists_unit_pow_ne_one_of_not_dvd {K : Type*} [Field K] [Finite K] {n : ℕ}
    (h : ¬ (Nat.card K - 1) ∣ n) : ∃ κ : Kˣ, κ ^ n ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun hgn => h ?_⟩
  rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one hgn

theorem exists_unit_pow_five_ne_one {K : Type*} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : ∃ κ : Kˣ, κ ^ 5 ≠ 1 := by
  refine exists_unit_pow_ne_one_of_not_dvd ?_
  rw [hK]
  intro hdvd
  have hle : 2 ^ f - 1 ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
  have hf3 : f < 3 := by
    by_contra hf3
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases f
  norm_num at hdvd

theorem exists_unit_pow_four_ne_one {K : Type*} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : ∃ κ : Kˣ, κ ^ 4 ≠ 1 := by
  refine exists_unit_pow_ne_one_of_not_dvd ?_
  rw [hK]
  intro hdvd
  have hle : 2 ^ f - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hf3 : f < 3 := by
    by_contra hf3
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases f
  norm_num at hdvd

end Units

section Five

theorem linearOrthFiveInput_holds : LinearOrthFiveInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hR5 hrow
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hstd := hset.standardSetting
  have hOut := isSolvable_outer_of_mulEquiv (by norm_num : 3 ≤ 5) e
  have hκ := exists_unit_pow_five_ne_one hKc hf
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have h23 : (2 : Fin 5) ≠ 3 := by decide
  have h34 : (3 : Fin 5) ≠ 4 := by decide
  have hdisj : Disjoint ({0, 1} : Finset (Fin 5)) {2, 3} := by decide
  have hN : ({0, 1} : Finset (Fin 5)) ⊆ ({3, 4} : Finset (Fin 5))ᶜ := by decide
  have hN' : ({2, 3} : Finset (Fin 5)) ⊆ ({0, 1} : Finset (Fin 5))ᶜ := by decide
  have hk : (3 : Fin 5) ∉ ({3, 4} : Finset (Fin 5))ᶜ := by decide
  have hk' : (0 : Fin 5) ∉ ({0, 1} : Finset (Fin 5))ᶜ := by decide
  have hX : modelToG e (rootTorus (K := K) h34) ≤ modelToG e (blockTorus (K := K) {0, 1}) :=
    modelToG_rootTorus_le e h34 (by decide) (by decide)
  have hX' : modelToG e (rootTorus (K := K) h01) ≤ modelToG e (blockTorus (K := K) {2, 3}) :=
    modelToG_rootTorus_le e h01 (by decide) (by decide)
  rcases hrow with ⟨F, _, _, ι, σ, hσ1, hσσ, hfix, a, b, hab, hP⟩ | hswap
  · have hσι : ∀ c : K, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
    obtain ⟨P⟩ := nonempty_fieldNeighbourParam_rootTorus_of_nonempty htC hσι hab hP h34
    obtain ⟨P'⟩ := nonempty_fieldNeighbourParam_rootTorus_of_nonempty htC hσι hab hP h01
    exact pieceCore_le_centralizer_pieceCore_field hstd hOut hq (by norm_num) hκ e htC ht h01 hR5
      ι hσ1 hσσ hfix hN hk hX P h23 hdisj hN' hk' hX' P'
  · obtain ⟨P⟩ := hswap 3 4 h34
    obtain ⟨P'⟩ := hswap 0 1 h01
    exact pieceCore_le_centralizer_pieceCore_swap hstd hOut hq (by norm_num) hκ e htC ht h01 hR5
      hN hk hX P h23 hdisj hN' hk' hX' P'

end Five

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type*} [Field K] [Finite K]
  [CharP K 2]

theorem pieceCore_le_centralizer_four_levTorus_field
    (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {F : Type*} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a : Fin 4}
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ))) :
    pieceCore e ({0, 1} : Finset (Fin 4)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 4)) : Set G) := by
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have hσι : ∀ c : K, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨P⟩ := nonempty_fieldNeighbourParam_levTorus_of_nonempty htC hσι hP 3
  obtain ⟨P'⟩ := nonempty_fieldNeighbourParam_levTorus_of_nonempty htC hσι hP 0
  exact pieceCore_le_centralizer_pieceCore_field hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by norm_num : 3 ≤ 4) e) hq le_rfl
    (exists_unit_pow_four_ne_one hKc hf) e htC ht (by decide : (0 : Fin 4) ≠ 1) hR5 ι hσ1 hσσ hfix
    (by decide) (by decide : (3 : Fin 4) ∉ ({3} : Finset (Fin 4))ᶜ)
    (modelToG_levTorus_le e (by decide)) P (by decide : (2 : Fin 4) ≠ 3) (by decide) (by decide)
    (by decide : (0 : Fin 4) ∉ ({0} : Finset (Fin 4))ᶜ) (modelToG_levTorus_le e (by decide)) P'

theorem pieceCore_le_centralizer_four_levTorus_swap
    (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (hP₃ : Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) 3)) ({3}ᶜ)))
    (hP₀ : Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) 0)) ({0}ᶜ))) :
    pieceCore e ({0, 1} : Finset (Fin 4)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 4)) : Set G) := by
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  obtain ⟨P⟩ := hP₃
  obtain ⟨P'⟩ := hP₀
  exact pieceCore_le_centralizer_pieceCore_swap hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by norm_num : 3 ≤ 4) e) hq le_rfl
    (exists_unit_pow_four_ne_one hKc hf) e htC ht (by decide : (0 : Fin 4) ≠ 1) hR5
    (by decide) (by decide : (3 : Fin 4) ∉ ({3} : Finset (Fin 4))ᶜ)
    (modelToG_levTorus_le e (by decide)) P (by decide : (2 : Fin 4) ≠ 3) (by decide) (by decide)
    (by decide : (0 : Fin 4) ∉ ({0} : Finset (Fin 4))ᶜ) (modelToG_levTorus_le e (by decide)) P'

end Four

end CFSG.SeitzReduction.LinearPilot
