module

public import CFSG.ClassicalInvolution.Q3.Q3EXTwin
public import CFSG.ClassicalInvolution.Q3.Q3WAD4
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleF4
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleE6
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleE8
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTwistedE6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


section Ctx

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem localShapeC3_conj (hΩ : ConjInvariant Ω) (g z : G) {a : ℕ} {c : CompData}
    (h : LocalShapeC3 a c Ω z) : LocalShapeC3 a c Ω (g * z * g⁻¹) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := h
  obtain ⟨D', hD'⟩ := exists_lieSystemData3_conj hΩ g z D
  refine ⟨ι, hι, D', hcard, i₁, ?_, fun i hi => ?_⟩
  · rw [hD']
    exact hk
  · rw [hD']
    exact hrest i hi

variable {z : G} {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G}

theorem exists_ctx_member3 [Finite G] (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z) {M : Subgroup G} (hM : M ∈ Ω) {x : G}
    (hx : IsClassicalMember3 M x) : Nonempty (ETCtx3 tY nY Ω M x) := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hzx : IsClassicalMember3 M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hxe : x = g * z * g⁻¹ := involution_unique3 hx hzx
  subst hxe
  have hshape_x := localShapeC3_conj c.hΩ.conjInvariant g z hshape
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  have hO3_x : LocalOddThreeFree3 Ω (g * z * g⁻¹) :=
    localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
  obtain ⟨dx⟩ := LocalShapeC3.nonempty_dictT c.hY.sc c.hΩ hM hzx hshape_x
  exact ⟨{ hΩ := c.hΩ
           hex := c.hex
           hK := hM
           hz := hzx
           hP1 := hP1_x
           hO3 := hO3_x
           d := dx
           hY := c.hY }⟩

end Ctx

section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem false_of_star3 (c : ETCtx3 tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z)
    (hne : (modelFund 3 1 tY nY).Nonempty)
    (hstar : ModelStar (GaloisField 3 1) (modelFund 3 1 tY nY))
    (hodd : ∀ y ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K, Odd (orderOf y)) :
    False := by
  classical
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, -⟩ := c.exists_member_of_fund hR₀
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨cx⟩ := exists_ctx_member3 c hsingle hshape hM.1 hxM
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx (fun h => hMK h.symm)
  obtain ⟨R₁, hR₁, R₂, hR₂, Rc, hRc, c01, c02, c12, p0, p1, p2⟩ := hstar RK hRK
  let Rn : Fin 4 → Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K := ![RK, R₁, R₂, Rc]
  have hRn : ∀ a, Rn a ∈ modelFund 3 1 tY nY := by
    intro a
    fin_cases a
    exacts [hRK, hR₁, hR₂, hRc]
  have hcomm : ∀ a b : Fin 4, a ≠ b → ¬ (a.val < 3 ∧ b.val = 3) → ¬ (b.val < 3 ∧ a.val = 3) →
      Commutes (Rn a) (Rn b) := by
    intro a b hab h1 h2
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd rfl hab
      | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
      | exact absurd ⟨by decide, by decide⟩ h1 | exact absurd ⟨by decide, by decide⟩ h2
  have hstd : ∀ a b : Fin 4, (a.val < 3 ∧ b.val = 3) →
      ∃ W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
        LinearBlockStandardPair (GaloisField 3 1) W (Rn a) (Rn b) := by
    rintro a b ⟨ha, hb⟩
    have hb' : b = 3 := Fin.ext hb
    subst hb'
    fin_cases a
    exacts [p0, p1, p2, absurd ha (by decide)]
  obtain ⟨j, hj, hjc, hjp, -⟩ :=
    cx.exists_nodes Rn hRn (fun a b => a.val < 3 ∧ b.val = 3) hcomm hstd
  have hj0 : j 0 = K := cx.eq_of_locImg_eq (hj 0).1 hKx (((hj 0).2.2).trans hKR.symm)
  have h01 : Commutes K (j 1) := hj0 ▸ hjc 0 1 (by decide) (by decide) (by decide)
  have h02 : Commutes K (j 2) := hj0 ▸ hjc 0 2 (by decide) (by decide) (by decide)
  have h12 : Commutes (j 1) (j 2) := hjc 1 2 (by decide) (by decide) (by decide)
  have h03 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K (j 3) :=
    hj0 ▸ hjp 0 3 ⟨by decide, rfl⟩
  have h13 := hjp 1 3 ⟨by decide, rfl⟩
  have h23 := hjp 2 3 ⟨by decide, rfl⟩
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical (j 1) (hj 1).1.1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj 2).1.1
  obtain ⟨a₃, ha₃, hc₀, hc₁, hc₂, hw₃⟩ := d4Frame3_holds G Ω c.hΩ.conjInvariant K (j 1) (j 2)
    (j 3) z w₁ w₂ c.hK (hj 1).1.1 (hj 2).1.1 (hj 3).1.1 c.hz hw₁ hw₂ h01 h02 h12 h03 h13 h23
  have hz1 : j 1 ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (hj 1).1.1 c.hz.mem h01.symm
  have hz2 : j 2 ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (hj 2).1.1 c.hz.mem h02.symm
  have hz3 : a₃ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes ha₃ c.hz.mem hc₀
  have hne1 : j 1 ≠ K := fun h => not_commutes_self3 c.hz (h ▸ h01)
  have hne2 : j 2 ≠ K := fun h => not_commutes_self3 c.hz (h ▸ h02)
  have hne3 : a₃ ≠ K := fun h => not_commutes_self3 c.hz (h ▸ hc₀)
  obtain ⟨R₁', hR₁', h1R⟩ := c.exists_fund_of_ne hz1 hne1
  obtain ⟨R₂', hR₂', h2R⟩ := c.exists_fund_of_ne hz2 hne2
  obtain ⟨R₃', hR₃', h3R⟩ := c.exists_fund_of_ne hz3 hne3
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer c.hKz c.hz.mem
  have hw₁Y : w₁ ∈ locLayer Ω z := le_centralizingLayer hz1 hw₁.mem
  have hw₂Y : w₂ ∈ locLayer Ω z := le_centralizingLayer hz2 hw₂.mem
  have hw₃Y : z * w₁ * w₂ ∈ locLayer Ω z := le_centralizingLayer hz3 hw₃.mem
  have hrel : locElt Ω z (z * w₁ * w₂) hw₃Y =
      locElt Ω z z hzY * locElt Ω z w₁ hw₁Y * locElt Ω z w₂ hw₂Y := by
    rw [locElt_mul, locElt_mul]
  have hrng : ∀ {L : Subgroup G} {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
      (hL : L ≤ locLayer Ω z) {w : G} (hw : w ∈ L), locImg Ω z L = R.map c.d.ψ →
      locElt Ω z w (hL hw) ∈ c.d.ψ.range := by
    intro L R hL w hw hLR
    have := locElt_mem_locImg hL hw
    rw [hLR] at this
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  have m1 := hrng (le_centralizingLayer hz1) hw₁.mem h1R
  have m2 := hrng (le_centralizingLayer hz2) hw₂.mem h2R
  have m3 := hrng (le_centralizingLayer hz3) hw₃.mem h3R
  have hzbar : locElt Ω z z hzY ∈ c.d.ψ.range := by
    have e : locElt Ω z z hzY =
        locElt Ω z (z * w₁ * w₂) hw₃Y * (locElt Ω z w₂ hw₂Y)⁻¹ * (locElt Ω z w₁ hw₁Y)⁻¹ := by
      rw [hrel]
      group
    rw [e]
    exact c.d.ψ.range.mul_mem (c.d.ψ.range.mul_mem m3 (c.d.ψ.range.inv_mem m2))
      (c.d.ψ.range.inv_mem m1)
  obtain ⟨y, hy⟩ := hzbar
  have hcentral : ∀ w : locQuot Ω z, w * locElt Ω z z hzY = locElt Ω z z hzY * w := by
    intro w
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective w
    show QuotientGroup.mk' _ (y' * ⟨z, hzY⟩) = QuotientGroup.mk' _ (⟨z, hzY⟩ * y')
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} y'.2)
  have hyc : y ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K := by
    have := c.hY.perfK
    refine mem_center_of_comm_mem_center fun s => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hy]
    rw [commutatorElement_def, ← hcentral (c.d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
  have h2 : orderOf (locElt Ω z z hzY) = 2 := orderOf_locElt hzY c.hz.orderOf_eq_two
  have hdvd : orderOf (c.d.ψ y) ∣ orderOf y := orderOf_map_dvd c.d.ψ y
  rw [hy, h2] at hdvd
  have := Nat.odd_iff.mp (hodd y hyc)
  omega

end Star

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Steinberg.TwistedE6 CFSG.Blueprint.Chevalley


section Facts

theorem yData3_F4 (hadm : StatedLieAdmissible .F4 0 3 1) : YData3 .F4 0 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .F4 0 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_f4Datum (F := GaloisField 3 1)
  have hl := ModelFacts.isLongestRoot_single .F4 0 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 4; decide⟩) (hl ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide))
  have hR₁ := rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 3 1 Nat.prime_three).D
    (k := ⟨1, by show 1 < 4; decide⟩) (hl ⟨1, by show 1 < 4; decide⟩ (by show 1 < 2; decide))
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .F4 0 Nat.prime_three trivial hadm).2⟩

theorem yData3_E6 (hadm : StatedLieAdmissible .E6 0 3 1) : YData3 .E6 0 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .E6 (modelUniv .E6 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E6 0 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e6Datum (F := GaloisField 3 1)
  have hl := ModelFacts.isLongestRoot_single .E6 0 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 3 1 Nat.prime_three).D
    (k := ⟨2, by show 2 < 6; decide⟩) (hl ⟨2, by show 2 < 6; decide⟩ trivial)
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .E6 0 Nat.prime_three trivial hadm).2⟩

theorem yData3_E8 (hadm : StatedLieAdmissible .E8 0 3 1) : YData3 .E8 0 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .E8 (modelUniv .E8 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E8 0 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e8Datum (F := GaloisField 3 1)
  have hl := ModelFacts.isLongestRoot_single .E8 0 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 8; decide⟩) (hl ⟨0, by show 0 < 8; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 3 1 Nat.prime_three).D
    (k := ⟨2, by show 2 < 8; decide⟩) (hl ⟨2, by show 2 < 8; decide⟩ trivial)
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .E8 0 Nat.prime_three trivial hadm).2⟩

theorem yData3_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 3 1) :
    YData3 .twistedE6 0 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .twistedE6
      (modelUniv .twistedE6 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .twistedE6 0 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := Balance.standardPair_twistedE6_nodes hadm
  have hl := ModelFacts.isLongestRoot_single .twistedE6 0 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .twistedE6)
    (modelUniv .twistedE6 0 3 1 Nat.prime_three).D (k := nf 0)
    (hl (nf 0) (by show 0 < 2; decide))
  have hR₁ := rankOne_mem_fundamental (t := .twistedE6)
    (modelUniv .twistedE6 0 3 1 Nat.prime_three).D (k := nf 1)
    (hl (nf 1) (by show 1 < 2; decide))
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .twistedE6 0 Nat.prime_three trivial hadm).2⟩

end Facts

section Shapes

theorem shapePiece3_single_star (h3 : OddThreeFreeInput) {tY : StatedLieTag} {nY : ℕ}
    (hY : YData3 tY nY) (hne : (modelFund 3 1 tY nY).Nonempty)
    (hstar : ModelStar (GaloisField 3 1) (modelFund 3 1 tY nY))
    (hodd : ∀ y ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K, Odd (orderOf y)) :
    ShapePiece3 1 (CompData.model tY nY) := by
  intro G _ _ _ hnab K z hR hshape
  exfalso
  have hΩ := hR.inClass
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hΩ hK hR.cls hshape
  let c : ETCtx3 tY nY (conjClass3 K) K z :=
    { hΩ := hΩ, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1, hO3 := h3 G K z hR, d := d,
      hY := hY }
  exact EX.false_of_star3 c (fun L hL => single_class3 K L hL) hshape hne hstar hodd

theorem shapePiece3_F4 (h3 : OddThreeFreeInput) : ShapePiece3 1 (CompData.model .F4 0) := by
  have hadm : StatedLieAdmissible .F4 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hl := ModelFacts.isLongestRoot_single .F4 0 3 1 Nat.prime_three trivial hadm
  exact shapePiece3_single_star h3 (yData3_F4 hadm)
    ⟨_, rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 3 1 Nat.prime_three).D
      (k := ⟨0, by show 0 < 4; decide⟩) (hl ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide))⟩
    (modelStar_F4 hadm) odd_center_F4

theorem shapePiece3_E6 (h3 : OddThreeFreeInput) : ShapePiece3 1 (CompData.model .E6 0) := by
  have hadm : StatedLieAdmissible .E6 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hl := ModelFacts.isLongestRoot_single .E6 0 3 1 Nat.prime_three trivial hadm
  exact shapePiece3_single_star h3 (yData3_E6 hadm)
    ⟨_, rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 3 1 Nat.prime_three).D
      (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)⟩
    (modelStar_E6 hadm) odd_center_E6

theorem shapePiece3_E8 (h3 : OddThreeFreeInput) : ShapePiece3 1 (CompData.model .E8 0) := by
  have hadm : StatedLieAdmissible .E8 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hl := ModelFacts.isLongestRoot_single .E8 0 3 1 Nat.prime_three trivial hadm
  exact shapePiece3_single_star h3 (yData3_E8 hadm)
    ⟨_, rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 3 1 Nat.prime_three).D
      (k := ⟨0, by show 0 < 8; decide⟩) (hl ⟨0, by show 0 < 8; decide⟩ trivial)⟩
    (modelStar_E8 hadm) odd_center_E8

theorem shapePiece3_twistedE6 (h3 : OddThreeFreeInput) :
    ShapePiece3 1 (CompData.model .twistedE6 0) := by
  have hadm : StatedLieAdmissible .twistedE6 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hl := ModelFacts.isLongestRoot_single .twistedE6 0 3 1 Nat.prime_three trivial hadm
  exact shapePiece3_single_star h3 (yData3_twistedE6 hadm)
    ⟨_, rankOne_mem_fundamental (t := .twistedE6)
      (modelUniv .twistedE6 0 3 1 Nat.prime_three).D (k := nf 0)
      (hl (nf 0) (by show 0 < 2; decide))⟩
    (modelStar_twistedE6 hadm) (odd_center_twistedE6 le_rfl)

end Shapes

end CFSG.ClassicalInvolution.Q3.Q3W
