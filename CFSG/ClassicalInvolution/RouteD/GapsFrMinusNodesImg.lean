module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  minusLongBlock shortBlock)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair minusShift rLong_injective
  rankOne_minusDatum_long rankOne_minusDatum_short minusShift_comp_longBlock
  minusShift_comp_shortBlock spinGroupMap_minusShift_injective commute_rankOne_minusDatum)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (lifting_of_noCover NoCover)
open CFSG.ClassicalInvolution.Models.TwistedPairs (finOne four_le_card_shortField')
open scoped MatrixGroups commutatorElement

section Nodes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {K : Subgroup G}

theorem exists_nodes_typeTwistedD_img {m : ℕ} (hm : 4 ≤ m)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    (hcov : NoCover.{0} Odd (spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))) (c : TCtx p f .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧ (∀ a, ⁅j a, j a⁆ = j a) ∧
      (∀ a, j a ≤ locLayer Ω z) ∧ (∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω) ∧
      (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
      (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
        ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b)) ∧
      (∀ a : Fin (m - 1), locImg Ω z (j a) =
        (rankOne (minusDatum m (minusCoeffs_irr p f)).rootGroup a).map c.d.ψ) := by
  have hp2 := c.hp2
  have h4 := c.h4
  have hirr := minusCoeffs_irr p f
  have := fact_shortField hirr
  have := finite_shortField (b := (minusCoeffs p f).1) (c := (minusCoeffs p f).2)
  obtain ⟨jL, hjLmem, hjLc, hjLp, hjLK, hjLimg⟩ := c.exists_nodes_minus hm hp2
  have hlongk : ∀ a : Fin (m - 1), a.val < m - 2 → a.val + 1 < m - 1 := fun a h => by omega
  set k₂ : Fin (m - 1) := ⟨m - 2, by omega⟩ with hk₂
  have hkshort : ¬ k₂.val + 1 < m - 1 := by simp only [k₂]; omega
  set Rs := rankOne (minusDatum m hirr).rootGroup k₂ with hRs
  have hRsperf : Rs.map c.d.ψ ≤ ⁅Rs.map c.d.ψ, Rs.map c.d.ψ⁆ := by
    have hr : Rs = (shortBlock hirr m k₂).range :=
      rankOne_minusDatum_short hirr hkshort
    have h1 := range_perfect_of_sl2 (four_le_card_shortField' (b := (minusCoeffs p f).1)
      (c := (minusCoeffs p f).2)) (c.d.ψ.comp (shortBlock hirr m k₂))
    have h2 : (c.d.ψ.comp (shortBlock hirr m k₂)).range = Rs.map c.d.ψ :=
      (MonoidHom.range_comp (f := shortBlock hirr m k₂) (g := c.d.ψ)).trans
        (congrArg (Subgroup.map c.d.ψ) hr.symm)
    exact h2 ▸ h1
  obtain ⟨As, hAsp, hAsm⟩ := exists_perfect_lift c.hP1 hRsperf
  set Yl : Subgroup G := locLayer Ω z with hYl
  let js : Subgroup G := As.map Yl.subtype
  have hjsimg : locImg Ω z js = Rs.map c.d.ψ := by rw [locImg_map_subtype, hAsm]
  have hjsY : js ≤ Yl := Subgroup.map_subtype_le _
  have hjsperf : js ≤ ⁅js, js⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAsp
  have hKY : K ≤ Yl := le_centralizingLayer c.hKz
  have hKperf : K ≤ ⁅K, K⁆ := (commutator_eq_of_isClassicalMember c.hz).ge
  have hjLY : ∀ a, jL a ≤ Yl := fun a => le_centralizingLayer (hjLmem a).1
  have hjLperf : ∀ a, jL a ≤ ⁅jL a, jL a⁆ := fun a => by
    obtain ⟨zL, hzL⟩ := c.hΩ.classical (jL a) (hjLmem a).1.1
    exact (commutator_eq_of_isClassicalMember hzL).ge
  have hKjs : Commutes K js := commutes_of_commutes_locImg_perfect c.hP1 hKY hjsY hKperf
    fun x hx y hy => c.d.comm₀ x (c.hQ₀ hx) y (by
      rw [hjsimg] at hy
      obtain ⟨r, -, rfl⟩ := hy
      exact ⟨r, rfl⟩)
  have hLjs : ∀ a : Fin (m - 2), a.val + 1 < m - 2 → Commutes (jL a) js := fun a ha =>
    commutes_of_commutes_locImg_perfect c.hP1 (hjLY a) hjsY (hjLperf a) (by
      rw [hjLimg a, hjsimg]
      refine commutes_map_hom c.d.ψ ?_
      exact fun x hx y hy => commute_rankOne_minusDatum hirr
        (⟨a.val, by have := a.2; omega⟩ : Fin (m - 1)) k₂ (by simp only [k₂]; omega) x hx y hy)
  let j : Fin (m - 1) → Subgroup G := fun a => if h : a.val < m - 2 then jL ⟨a.val, h⟩ else js
  have hjl : ∀ a : Fin (m - 1), (h : a.val < m - 2) → j a = jL ⟨a.val, h⟩ := fun a h =>
    dite_eq_left h
  have hjsd : ∀ a : Fin (m - 1), ¬ a.val < m - 2 → j a = js := fun a h => dite_eq_right h
  refine ⟨j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : a.val < m - 2
    · rw [hjl a h]
      exact hjLK _
    · rw [hjsd a h]
      exact hKjs
  · intro a
    by_cases h : a.val < m - 2
    · rw [hjl a h]
      exact le_antisymm (commutator_self_le _) (hjLperf _)
    · rw [hjsd a h]
      exact le_antisymm (commutator_self_le _) hjsperf
  · intro a
    by_cases h : a.val < m - 2
    · rw [hjl a h]
      exact hjLY _
    · rw [hjsd a h]
      exact hjsY
  · intro a ha
    rw [hjl a (by omega)]
    exact (hjLmem _).1.1
  · intro a b hab u hu v hv
    have ha : a.val < m - 2 := by have := b.2; omega
    rw [hjl a ha] at hu
    by_cases hb : b.val < m - 2
    · rw [hjl b hb] at hv
      exact hjLc ⟨a.val, ha⟩ ⟨b.val, hb⟩ (by simp only; omega) u hu v hv
    · rw [hjsd b hb] at hv
      exact hLjs ⟨a.val, ha⟩ (by have := b.2; simp only; omega) u hu v hv
  · intro a b hab hb
    rw [hjl a (by omega), hjl b (by omega)]
    exact hjLp ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ (by simp only; omega)
  · intro a b ha hb
    have hal : a.val < m - 2 := by omega
    have hbl : ¬ b.val < m - 2 := by omega
    have hbk : b = k₂ := Fin.ext (by simp only [k₂]; omega)
    rw [hjl a hal, hjsd b hbl]
    subst hbk
    obtain ⟨θ, hθinj, hθl, hθU, hθV⟩ := exists_twistedB2_minusDatum_inj hirr
      (ModelFacts.two_ne_zero_galoisField f hp2) hm ha hb
    have hψR : ∀ r ∈ (rankOne (minusDatum m hirr).rootGroup a :
          Subgroup (modelUniv .POmegaMinus m p f Fact.out).K),
        ∀ r' ∈ (rankOne (minusDatum m hirr).rootGroup a :
          Subgroup (modelUniv .POmegaMinus m p f Fact.out).K),
        c.d.ψ r = c.d.ψ r' → r = r' := by
      intro r hr r' hr' h
      have hmem : r⁻¹ * r' ∈ c.d.ψ.ker :=
        MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h, inv_mul_cancel])
      have h1 : r⁻¹ * r' = 1 := c.hY.central _ (rankOne_mem_fund_minus hirr (hlongk a hal)) _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hr) hr') (c.d.ker_le hmem)
      exact inv_mul_eq_one.mp h1
    have hpairX : TwistedB2BlockPair hirr ((c.d.ψ.comp θ).range)
        (locImg Ω z (jL ⟨a.val, hal⟩)) (locImg Ω z js) := by
      refine ⟨c.d.ψ.comp θ, rfl, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have hc := c.d.ker_le (show θ x ∈ c.d.ψ.ker from hx)
        rw [Subgroup.mem_center_iff]
        intro y
        apply hθinj
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.mp hc (θ y)
      · intro u v huv
        apply hθl
        have hmu : θ ((spinMinusModel hirr).lb u) ∈ rankOne (minusDatum m hirr).rootGroup a := by
          rw [← hθU]
          exact ⟨_, ⟨u, rfl⟩, rfl⟩
        have hmv : θ ((spinMinusModel hirr).lb v) ∈ rankOne (minusDatum m hirr).rootGroup a := by
          rw [← hθU]
          exact ⟨_, ⟨v, rfl⟩, rfl⟩
        exact hψR _ hmu _ hmv huv
      · exact ((Subgroup.map_map _ c.d.ψ θ).symm.trans
          (congrArg (Subgroup.map c.d.ψ) hθU)).trans (hjLimg ⟨a.val, hal⟩).symm
      · exact ((Subgroup.map_map _ c.d.ψ θ).symm.trans
          (congrArg (Subgroup.map c.d.ψ) hθV)).trans hjsimg.symm
    exact twistedB2BlockPair_of_locImg_perfect hirr hg6 hcov c.h4 c.hP1 (hjLY _) hjsY
      (hjLperf _) hjsperf hpairX
  · intro a
    by_cases h : a.val < m - 2
    · rw [hjl a h]
      exact hjLimg ⟨a.val, h⟩
    · rw [hjsd a h]
      have hak : a = k₂ := Fin.ext (by simp only [k₂]; omega)
      subst hak
      exact hjsimg


end Nodes

end CFSG.ClassicalInvolution.RouteD
