module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDStab
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDGroup
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDChar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.ShortNode
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Conj
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.FlagLinkM

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  Matrix

set_option linter.unusedSectionVars false

theorem perfect_pullback {X' G : Type*} [Group X'] [Group G] (e : X' ≃* G) (y : X')
    {V₀ : Subgroup G} (hC : V₀ ≤ Subgroup.centralizer ({e y} : Set G)) (hP : ⁅V₀, V₀⁆ = V₀)
    (hbot : V₀ ≠ ⊥) :
    ∃ V₁ : Subgroup X', V₁ ≤ Subgroup.centralizer ({y} : Set X') ∧ ⁅V₁, V₁⁆ = V₁ ∧ V₁ ≠ ⊥ := by
  refine ⟨V₀.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have := Subgroup.mem_centralizer_iff.mp (hC hw) (e z) (Set.mem_singleton _)
    apply e.injective
    simpa using this
  · rw [← Subgroup.map_commutator, hP]
  · intro hb
    apply hbot
    have := Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
      (hb.trans (Subgroup.map_bot _).symm)
    exact this


theorem false_of_centCycBar_pomegaMinus {n : ℕ} (hn : n = 4 ∨ n = 5) {F : Type} [Field F]
    [Finite F] [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : Nat.card F = 2)
    {J : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))}
    {v : StatedProj (StatedOmega (StatedQuadMinus n F b c))} (h : CentCycBar J 3 v) : False := by
  classical
  have hn4 : 4 ≤ n := by omega
  have : Fintype F := Fintype.ofFinite F
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  let Q : QuadraticForm F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := quadMinus n F b c
  have hQ0 : ⇑Q = StatedQuadMinus n F b c := coe_quadMinus n F b c
  have hB : (QuadraticMap.polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite n F hirr
  let e := CFSG.AGLEmbedding.ToralCensus.statedProjOmegaEquivDerivedCharTwo hQ0 hB
  have hdim : Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hS : ∑ w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F, chi (Q w) = -(2 : ℤ) ^ n := by
    have := charSum_statedQuadMinus hcard (by omega : 1 ≤ n) hirr
    simpa [hQ0] using this
  have hK2 : ∀ c : F, c = 0 ∨ c = 1 := eq_zero_or_eq_one_of_natCard_eq_two hcard
  obtain ⟨S₀, hNJ, hneJ⟩ := h.parab
  obtain ⟨g, π', hπ', hQb, hBJ⟩ := exists_conj_borelQuotient hirr hn4 S₀ J hNJ
  have hv3 : v ^ 3 = 1 := h.pow
  have hv1 : v ≠ 1 := h.ne_one
  have hvJ : v ∈ J := perfectJoin_le J h.join
  let s : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hn' : n = 4 ∨ n = 5 := hn
  by_cases hs : (rankOne (minusDatum n hirr).rootGroup s).map π' ≤ J
  ·
    obtain ⟨A, hAs, hAperf, x, hxA, hx3⟩ := exists_perfect_order_three_of_shortNode hirr hcard hQb
      s (by simp only [s]; omega)
    have hAJ : A ≤ J := hAs.trans hs
    have hxP : x ∈ perfectJoin J := le_perfectJoin hAJ hAperf hxA
    have hcycP : ∀ Q' : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c))),
        Q' ≤ perfectJoin J → IsPGroup 3 Q' → IsCyclic Q' :=
      h.cyc (perfectJoin J) (perfectJoin_le J) (perfectJoin_perfect J)
    obtain ⟨g', hg'P, hg'⟩ := CFSG.AGLEmbedding.ToralCensus.exists_conj_mem_zpowers_of_cyclic Nat.prime_three hcycP h.join hxP
      hv3 hx3
    obtain ⟨k, hk, hkx⟩ := hAs hxA
    obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective g
    obtain ⟨Ax, hAx⟩ := QuotientGroup.mk_surjective x
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx3
      omega
    have hk_stab : ∀ m ≤ n - 2, k ∈ stabEM (n := n) (b := b) (c := c) m := fun m hm =>
      rankOne_le_stabEM_short hirr (by simp only [s]; omega) (by simp only [s]; omega) hk
    have hgx : ((e x : ↥(OmegaOf Q)) : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F
          (Ax : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := by
      rw [← hAx]; rfl
    have hex3 : e x ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
    have hex1 : e x ≠ 1 := fun h1 => hx1 (e.injective (h1.trans (map_one e).symm))
    have hA3 : ∀ w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
        (e x : ↥(OmegaOf Q)).1 ((e x : ↥(OmegaOf Q)).1 ((e x : ↥(OmegaOf Q)).1 w)) = w := by
      intro w
      have := congrArg (fun y : ↥(OmegaOf Q) => (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)) w) hex3
      simpa [pow_succ] using this
    let S : ℕ → Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := fun m =>
      (eSpanM n (K := F) m).map (Matrix.mulVecLin
        ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
    have hS0 : S 0 = ⊥ := by simp [S, eSpanM_zero]
    have hSj : ∀ j < n - 2, ∃ u, S (j + 1) = S j ⊔ Submodule.span F {u} := by
      intro j hj
      refine ⟨Matrix.mulVecLin ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
        (eVec n (K := F) ⟨j, by omega⟩), ?_⟩
      simp only [S]
      rw [eSpanM_succ (by omega), Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    have hst : ∀ m ≤ n - 2, ∀ w ∈ S m, (e x : ↥(OmegaOf Q)).1 w ∈ S m := by
      intro m hm w hw
      have := hgx
      have h1 : (e x : ↥(OmegaOf Q)).1 w =
          ((Ax : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
            Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
            *ᵥ w := by
        rw [show (e x : ↥(OmegaOf Q)).1 w = ((e x : ↥(OmegaOf Q)) : _ ≃ₗ[F] _) w from rfl, hgx]
        rfl
      rw [h1]
      exact stab_of_map_stabEM hirr hn4 π' g hπ' (hk_stab m hm) Ag hAg Ax
        (by rw [hAx, hkx]) w hw
    have hfix : ∀ w ∈ S (n - 2), (e x : ↥(OmegaOf Q)).1 w = w :=
      fixed_of_flag hK2 (A := ((e x : ↥(OmegaOf Q)) : _ ≃ₗ[F] _)) hA3 S hS0 hSj hst
    have hWQ : ∀ w ∈ S (n - 2), Q w = 0 := fun w hw => by
      rw [show Q w = StatedQuadMinus n F b c w from congrFun hQ0 w]
      exact quad_map_eSpanM Ag w hw
    have hWdim : Module.finrank F (S (n - 2)) = n - 2 := finrank_map_eSpanM (by omega) Ag
    obtain ⟨V₀, hV₀C, hV₀P, hV₀bot⟩ := exists_perfect_of_fixes hcard hB hdim hn' hS hex3 hex1
      hWQ hWdim hfix
    obtain ⟨V₁, hV₁C, hV₁P, hV₁bot⟩ := perfect_pullback e x hV₀C hV₀P hV₀bot
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hg'
    apply hV₁bot
    refine h.triv_conj g' V₁ (fun z hz => ?_) hV₁P
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht, ← hm]
    have hz' := Subgroup.mem_centralizer_iff.mp (hV₁C hz) x (Set.mem_singleton _)
    exact (Commute.zpow_left (show Commute x z from hz') m).eq
  ·
    obtain ⟨W, hWQ, hWdim, hWstab⟩ := exists_stab_of_missing_node hirr hn4 π' g hπ' hQb hBJ hs
    have hWdim' : Module.finrank F W = n - 1 := by rw [hWdim]; simp only [s]; omega
    have hWQ' : ∀ w ∈ W, Q w = 0 := fun w hw => by
      rw [show Q w = StatedQuadMinus n F b c w from congrFun hQ0 w]
      exact hWQ w hw
    let U : Subgroup ↥(OmegaOf Q) := (perfectJoin J).map e.toMonoidHom
    have hU : ⁅U, U⁆ = U := by
      rw [← Subgroup.map_commutator, perfectJoin_perfect]
    have hst : ∀ y ∈ U, ∀ w ∈ W,
        (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F] _) w ∈ W := by
      rintro _ ⟨y, hy, rfl⟩ w hw
      obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective y
      have := hWstab y (perfectJoin_le J hy) A hA w hw
      subst hA
      exact this
    have htriv := trivial_on_perp_of_perfect hcard hB hdim (by omega) hWQ' hWdim' U hU hst
    have hev : e v ∈ U := ⟨v, h.join, rfl⟩
    have hev3 : e v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
    have hev1 : e v ≠ 1 := fun h1 => hv1 (e.injective (h1.trans (map_one e).symm))
    obtain ⟨V₀, hV₀C, hV₀P, hV₀bot⟩ := exists_perfect_of_stable hcard hB hdim hn' hS hev3 hev1
      hWQ' hWdim' (hst _ hev) (htriv _ hev)
    obtain ⟨V₁, hV₁C, hV₁P, hV₁bot⟩ := perfect_pullback e v hV₀C hV₀P hV₀bot
    exact hV₁bot (h.triv V₁ (fun z hz => by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact (Subgroup.mem_centralizer_iff.mp (hV₁C hz) t (Set.mem_singleton _))) hV₁P)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
