module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDRecognition
public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes

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

section Model

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem exists_twistedB2_minusDatum_inj (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    {i j : Fin (n - 1)} (hia : i.val + 3 = n) (hjb : j.val + 2 = n) :
    ∃ θ : spinGroup (quadMinus 3 F b c) →* spinGroup (quadMinus n F b c),
      Function.Injective θ ∧ Function.Injective (θ.comp (spinMinusModel hirr).lb) ∧
      (spinMinusModel hirr).lb.range.map θ = rankOne (minusDatum n hirr).rootGroup i ∧
      (spinMinusModel hirr).sb.range.map θ = rankOne (minusDatum n hirr).rootGroup j := by
  have hn3 : 3 ≤ n := by omega
  have hi : i.val + 1 < n - 1 := by omega
  have hj : ¬ j.val + 1 < n - 1 := by omega
  have hinj := spinGroupMap_minusShift_injective h2 n hn3 hirr
  have hl := minusShift_comp_longBlock (b := b) (c := c) hn3 hia hi
  have hs := minusShift_comp_shortBlock hn3 hirr hjb
  refine ⟨(minusShift n hn3 b c).spinGroupMap, hinj, ?_, ?_, ?_⟩
  · change Function.Injective ((minusShift n hn3 b c).spinGroupMap.comp (minusLongBlock b c))
    rw [hl]
    exact rLong_injective hi
  · change (minusLongBlock b c).range.map (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hl, rankOne_minusDatum_long hirr hi]
  · change (shortBlock hirr 3 finOne).range.map
      (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hs, rankOne_minusDatum_short hirr hj]

end Model


section Lift


theorem isPerfect_of_sup_eq_top {X : Type*} [Group X] {A B : Subgroup X} (hA : A ≤ ⁅A, A⁆)
    (hB : B ≤ ⁅B, B⁆) (h : A ⊔ B = ⊤) : Group.IsPerfect X := by
  refine ⟨?_⟩
  rw [commutator_def]
  refine top_le_iff.mp ?_
  calc (⊤ : Subgroup X) = A ⊔ B := h.symm
    _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := sup_le (hA.trans (Subgroup.commutator_mono le_top le_top))
      (hB.trans (Subgroup.commutator_mono le_top le_top))

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem isPerfect_spinMinus6 (hg : SpinMinus6Generated hirr) (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (spinGroup (quadMinus 3 F b c)) := by
  have := finite_shortField (b := b) (c := c)
  refine isPerfect_of_sup_eq_top (A := (spinMinusModel hirr).lb.range)
    (B := (spinMinusModel hirr).sb.range) (range_perfect_of_sl2 h4 _)
    (range_perfect_of_sl2 (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField'
      (b := b) (c := c)) _) hg

theorem twistedB2BlockPair_lift (hg6 : SpinMinus6Generated hirr)
    (hcov : NoCover.{0} Odd (spinGroup (quadMinus 3 F b c))) (h4 : 4 ≤ Nat.card F)
    {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) {A B : Subgroup Y} (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆)
    {W : Subgroup (Y ⧸ O)}
    (h : TwistedB2BlockPair hirr W (A.map (QuotientGroup.mk' O)) (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, TwistedB2BlockPair hirr W' A B := by
  have := finite_shortField (b := b) (c := c)
  have hfin6 : Finite (spinGroup (quadMinus 3 F b c)) := finite_spinGroup_quadMinus 3 b c
  have hperf6 := isPerfect_spinMinus6 hirr hg6 h4
  let π := QuotientGroup.mk' O
  let P : Subgroup Y := A ⊔ B
  let π' : ↥P →* Y ⧸ O := π.comp P.subtype
  have hW : W ≤ A.map π ⊔ B.map π := twistedB2BlockPair_le_sup hirr hg6 h
  obtain ⟨θb, hrange, hker, hinjL, hU, hV⟩ := h
  have hrange' : π'.range = A.map π ⊔ B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup]
  have hAle : A.map π ≤ θb.range := hU ▸ Subgroup.map_le_range θb _
  have hBle : B.map π ≤ θb.range := hV ▸ Subgroup.map_le_range θb _
  have hθ : ∀ s, θb s ∈ π'.range := fun s => by
    rw [hrange']
    exact hW (hrange ▸ ⟨s, rfl⟩)
  have hPperf : P ≤ ⁅P, P⁆ :=
    sup_le (hA.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
      (hB.trans (Subgroup.commutator_mono le_sup_right le_sup_right))
  have : Group.IsPerfect ↥P :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)) hPperf)
  have hZc : π'.ker ≤ Subgroup.center ↥P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hZodd : Odd (Nat.card π'.ker) := by
    refine hOodd.of_dvd_nat ?_
    let g : π'.ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  let e : (↥P ⧸ π'.ker) ≃* π'.range := QuotientGroup.quotientKerEquivRange π'
  let θc : spinGroup (quadMinus 3 F b c) →* π'.range := θb.codRestrict π'.range hθ
  let θbar : spinGroup (quadMinus 3 F b c) →* ↥P ⧸ π'.ker := e.symm.toMonoidHom.comp θc
  have hθcsurj : Function.Surjective θc := by
    rintro ⟨w, hw⟩
    rw [hrange'] at hw
    have hw' : w ∈ θb.range := (sup_le hAle hBle) hw
    obtain ⟨x, hx⟩ := hw'
    exact ⟨x, Subtype.ext hx⟩
  have hθbarsurj : Function.Surjective θbar := e.symm.surjective.comp hθcsurj
  have hθbarker : θbar.ker ≤ Subgroup.center (spinGroup (quadMinus 3 F b c)) := by
    intro x hx
    apply hker
    have hx' : e.symm (θc x) = 1 := hx
    have : θc x = 1 := (MulEquiv.map_eq_one_iff e.symm).mp hx'
    simpa [θc, Subtype.ext_iff] using this
  obtain ⟨θ, -, hθker, hθeq⟩ := lifting_of_noCover hcov hZc hZodd θbar hθbarsurj hθbarker
  have hπθ : ∀ x, π ((θ x : ↥P) : Y) = θb x := by
    intro x
    have h1 := hθeq x
    have h2 : e ((θ x : ↥P ⧸ π'.ker)) = θc x := by
      rw [h1]
      exact e.apply_symm_apply _
    have h3 : (e ((θ x : ↥P ⧸ π'.ker)) : Y ⧸ O) = π' (θ x) := rfl
    rw [h2] at h3
    exact h3.symm.trans rfl
  let θY : spinGroup (quadMinus 3 F b c) →* Y := P.subtype.comp θ
  have hπθY : π.comp θY = θb := MonoidHom.ext hπθ
  refine ⟨θY.range, θY, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hθker
    exact Subtype.ext (MonoidHom.mem_ker.mp hx)
  · intro a b hab
    apply hinjL
    simp only [MonoidHom.comp_apply] at hab ⊢
    rw [← hπθ, ← hπθ]
    exact congrArg π hab
  · refine eq_of_map_mk_eq_of_central hOc ?_ hA ?_
    · rw [← MonoidHom.range_comp]
      exact range_perfect_of_sl2 h4 _
    · rw [Subgroup.map_map, hπθY]
      exact hU
  · refine eq_of_map_mk_eq_of_central hOc ?_ hB ?_
    · rw [← MonoidHom.range_comp]
      exact range_perfect_of_sl2 (four_le_card_shortField' (b := b) (c := c)) _
    · rw [Subgroup.map_map, hπθY]
      exact hV

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem twistedB2BlockPair_map {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : TwistedB2BlockPair hirr W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    TwistedB2BlockPair hirr (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, hrange, hker, hinjL, hU, hV⟩ := h
  refine ⟨φ.comp θ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · exact hφ.comp hinjL
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

variable {p f : ℕ} [Fact p.Prime]

theorem twistedB2BlockPair_of_locImg_perfect {G : Type} [Group G] [Finite G]
    (hg6 : SpinMinus6Generated hirr) (hcov : NoCover.{0} Odd (spinGroup (quadMinus 3 F b c)))
    (h4 : 4 ≤ Nat.card F) {Ω : Set (Subgroup G)} {x : G} (hP1 : LocalOddCentral Ω {x})
    {A B : Subgroup G} (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) (hAp : A ≤ ⁅A, A⁆)
    (hBp : B ≤ ⁅B, B⁆) {W : Subgroup (locQuot Ω x)}
    (h : TwistedB2BlockPair hirr W (locImg Ω x A) (locImg Ω x B)) :
    ∃ W' : Subgroup G, TwistedB2BlockPair hirr W' A B := by
  obtain ⟨W', hW'⟩ := twistedB2BlockPair_lift hirr hg6 hcov h4
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) (perfect_subgroupOf hA hAp)
    (perfect_subgroupOf hB hBp) h
  have := twistedB2BlockPair_map hirr hW' (locLayer Ω x).subtype (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA,
    inf_eq_left.mpr hB] at this
  exact ⟨_, this⟩

end Lift

section Nodes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {K : Subgroup G}

theorem exists_nodes_typeTwistedD {m : ℕ} (hm : 4 ≤ m)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    (hcov : NoCover.{0} Odd (spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))) (c : TCtx p f .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧ (∀ a, ⁅j a, j a⁆ = j a) ∧
      (∀ a, j a ≤ locLayer Ω z) ∧ (∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω) ∧
      (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
      (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
        ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b)) := by
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
  refine ⟨j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end Nodes

end CFSG.ClassicalInvolution.RouteD
