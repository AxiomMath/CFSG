module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourHR8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLiftLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)

section SwapRow

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def NeighbourSwapRow {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (Nb : Neighbour n) : Prop :=
  ∃ htX : t ∈ centralizer (modelToG e (Nb.torus K) : Set G),
    ∃ Kc : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G))),
      IsComponent Kc ∧
      ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
          (centralizer (modelToG e (Nb.torus K) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
          (centralizer (modelToG e (Nb.torus K) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))))

end SwapRow

theorem normalizerMonoidHom_mem_range_conj_of_mem_centralizer {Y : Type*} [Group Y]
    {H : Subgroup Y} {s : Y} (hsN : s ∈ normalizer (H : Set Y))
    (hs : s ∈ centralizer (H : Set Y)) :
    H.normalizerMonoidHom ⟨s, hsN⟩ ∈ (MulAut.conj : H →* MulAut H).range := by
  have hker : (⟨s, hsN⟩ : normalizer (H : Set Y)) ∈ H.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker, mem_subgroupOf]
    exact hs
  exact ⟨1, by rw [map_one, MonoidHom.mem_ker.1 hker]⟩

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_fieldNeighbourParam_levTorus_or_swapRow (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 3) (hdet : SLmEvenTypeDetAt 3) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (a : Fin 4) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)) ∨
      NeighbourSwapRow e t (.levi a) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have htX : t ∈ centralizer (modelToG e (levTorus (K := K) a) : Set G) :=
    mem_centralizer_map_symm e _ htC
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_levTorus_of_seitzSetting (X := modelToG e (levTorus (K := K) a))
      (D := modelToG e (blockSL (K := K) (({a} : Finset (Fin 4))ᶜ))) hset hKc e htC ht a rfl htX
      rfl
  obtain ⟨⟨Kc, hKcomp, hDKK, ⟨-, hDK, -, hsN, hτ, -, hmodel, -⟩ | hswap⟩, hZ⟩ :=
    neighbour_overgroup_levTorus_field (X := modelToG e (levTorus (K := K) a))
      (D := modelToG e (blockSL (K := K) (({a} : Finset (Fin 4))ᶜ))) hset hcat hdet hKc hf e htC
      ht hR5 a rfl htX rfl
  · left
    have hsC : QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (levTorus (K := K) a) : Set G))) ⟨t, htX⟩ ∉
          centralizer (Kc : Set (centralizer (modelToG e (levTorus (K := K) a) : Set G) ⧸
            oddCore (centralizer (modelToG e (levTorus (K := K) a) : Set G)))) := fun hc =>
      hτ (normalizerMonoidHom_mem_range_conj_of_mem_centralizer hsN hc)
    obtain ⟨-, -, hBl⟩ := bLift_neighbour_levTorus_of_seitzSetting hset hKc e htC ht a rfl htX rfl
    have hB : HasBLift Kc := hBl Kc (Subgroup.isPerfect_iff.mp hKcomp.1.1) hsN
      (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKcomp.1 hsN hsC)
    have hcard : Fintype.card ((Neighbour.levi a : Neighbour 4).index) = 3 := by
      rw [Fintype.card_coe, Neighbour.index_levi, Finset.card_compl, Fintype.card_fin,
        Finset.card_singleton]
    exact nonempty_fieldNeighbourParam_of_fieldRow e hKc hf htC ht ι hσ1 hσσ hfix (.levi a)
      (Fintype.equivFinOfCardEq hcard) le_rfl htX hcomp hsyl hZ hKcomp hDK.le hsN hτ hmodel hB
  · exact Or.inr ⟨htX, Kc, hKcomp, hDKK, hswap⟩

end Seitz

end CFSG.SeitzReduction.LinearPilot
