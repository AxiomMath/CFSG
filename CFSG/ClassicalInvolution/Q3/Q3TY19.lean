module

public import CFSG.ClassicalInvolution.Q3.Q3TY6
public import CFSG.ClassicalInvolution.Q3.Q3TY11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair rankOne_minusDatum_short
  rankOne_minusDatum_long commute_rankOne_minusDatum)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  minusLongBlock shortBlock four_le_card_shortField' finOne)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem conjSub_layer_member {tY : StatedLieTag} {nY : ℕ} (c : TCtx3 tY nY Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z) (h2t : t * t = 1) (hKt : conjSub t K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNQ : ¬ locImg Ω z N ≤ c.d.Q₁) :
    conjSub t N ∈ centralizingMembers Ω {z} ∧ conjSub t N ≠ K ∧
      ¬ locImg Ω z (conjSub t N) ≤ c.d.Q₁ := by
  have hΩ := c.hΩ.conjInvariant
  have hNz := conjSub_mem_centralizingMembers3 hΩ htz hN
  refine ⟨hNz, fun h => hNK ?_, fun h => ?_⟩
  · have := congrArg (conjSub t) h
    rwa [Gaps.conjSub_conjSub_self h2t, hKt] at this
  · obtain ⟨T, hT, hTeq⟩ := c.exists_twin
    have hconj := c.conjSub_twin_eq3 htz h2t hKt hT hTeq.le
    have h1 := c.eq_of_locImg_le_Q₁ hNz hT h hTeq.le
    apply hNQ
    have : N = T := by rw [← Gaps.conjSub_conjSub_self h2t N, h1, hconj]
    rw [this, hTeq]

theorem locAut_mem_range {tY : StatedLieTag} {nY : ℕ} (c : TCtx3 tY nY Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z) (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY
      (modelUniv tY nY 3 1 Nat.prime_three).D, R.map c.d.ψ)
    (k : (modelUniv tY nY 3 1 Nat.prime_three).K) :
    Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      (R.map c.d.ψ).map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNQ, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K, hN'Q⟩ := c.conjSub_layer_member htz h2t hKt hNz hNK hNQ
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K hN'Q
    rw [← hNeq, Gaps.locAut_locImg c.hΩ.conjInvariant htz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

theorem exists_nodes_typeTwistedD3_img {m : ℕ} (hm : 4 ≤ m)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr 3 1)) (c : TCtx3 .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧ (∀ a, j a ≤ locLayer Ω z) ∧
      (∀ a : Fin (m - 1), a.val + 2 < m →
        j a ∈ centralizingMembers Ω {z} ∧ ∀ x ∈ j a, x ^ 12 = 1) ∧
      (∀ a : Fin (m - 1), ¬ a.val + 2 < m → j a ≤ ⁅j a, j a⁆) ∧
      (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
      (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
      (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
        ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (j a) (j b)) ∧
      (∀ a : Fin (m - 1), locImg Ω z (j a) =
        (rankOne (minusDatum m (minusCoeffs_irr 3 1)).rootGroup a).map c.d.ψ) := by
  have hirr := minusCoeffs_irr 3 1
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have := fact_shortField hirr
  have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
  obtain ⟨jL, hjLmem, hjLc, hjLp, hjLK, hjLimg⟩ := c.exists_nodes_minus3 hm
  have hlongk : ∀ a : Fin (m - 1), a.val < m - 2 → a.val + 1 < m - 1 := fun a h => by omega
  set k₂ : Fin (m - 1) := ⟨m - 2, by omega⟩ with hk₂
  have hkshort : ¬ k₂.val + 1 < m - 1 := by simp only [k₂]; omega
  set Rs := rankOne (minusDatum m hirr).rootGroup k₂ with hRs
  have hRsperf : Rs.map c.d.ψ ≤ ⁅Rs.map c.d.ψ, Rs.map c.d.ψ⁆ := by
    have hr : Rs = (shortBlock hirr m k₂).range := rankOne_minusDatum_short hirr hkshort
    have h1 := range_perfect_of_sl2 (four_le_card_shortField' (b := (minusCoeffs 3 1).1)
      (c := (minusCoeffs 3 1).2)) (c.d.ψ.comp (shortBlock hirr m k₂))
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
  have hjLY : ∀ a, jL a ≤ Yl := fun a => le_centralizingLayer (hjLmem a).1
  have hjL12 : ∀ a, ∀ x ∈ jL a, x ^ 12 = 1 := fun a => by
    obtain ⟨zL, hzL⟩ := c.hΩ.classical (jL a) (hjLmem a).1.1
    exact pow_twelve_of_exact hzL (c.hex _ (hjLmem a).1.1)
  have hKjs : Commutes K js := RouteD.Gaps.commutes_symm
    (commutes_of_commutes_locImg_perfect c.hP1 hjsY hKY hjsperf fun x hx y hy => by
      rw [hjsimg] at hx
      obtain ⟨r, -, rfl⟩ := hx
      exact (c.d.comm₀ y (c.hQ₀ hy) _ ⟨r, rfl⟩).symm)
  have hLjs : ∀ a : Fin (m - 2), a.val + 1 < m - 2 → Commutes (jL a) js := fun a ha =>
    RouteD.Gaps.commutes_symm (commutes_of_commutes_locImg_perfect c.hP1 hjsY (hjLY a) hjsperf (by
      rw [hjLimg a, hjsimg]
      refine (commutes_map_hom c.d.ψ ?_).symm
      exact fun x hx y hy => commute_rankOne_minusDatum hirr
        (⟨a.val, by have := a.2; omega⟩ : Fin (m - 1)) k₂ (by simp only [k₂]; omega) x hx y hy))
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
      exact hjLY _
    · rw [hjsd a h]
      exact hjsY
  · intro a ha
    rw [hjl a (by omega)]
    exact ⟨(hjLmem _).1, hjL12 _⟩
  · intro a ha
    rw [hjsd a (by omega)]
    exact hjsperf
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
    obtain ⟨θ, hθinj, hθl, hθU, hθV⟩ := exists_twistedB2_minusDatum_inj hirr h2 hm ha hb
    have hψR : ∀ r ∈ (rankOne (minusDatum m hirr).rootGroup a :
          Subgroup (modelUniv .POmegaMinus m 3 1 Nat.prime_three).K),
        ∀ r' ∈ (rankOne (minusDatum m hirr).rootGroup a :
          Subgroup (modelUniv .POmegaMinus m 3 1 Nat.prime_three).K),
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
    exact Q3TY.twistedB2BlockPair_of_locImg3 hirr hg6 c.hP1 c.hO3 (hjLY _) hjsY (hjL12 _) hjsperf
      hpairX
  · intro a
    by_cases h : a.val < m - 2
    · rw [hjl a h]
      exact hjLimg ⟨a.val, h⟩
    · rw [hjsd a h]
      have hak : a = k₂ := Fin.ext (by simp only [k₂]; omega)
      subst hak
      exact hjsimg

end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3
