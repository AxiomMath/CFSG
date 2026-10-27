module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTwin
public import CFSG.ClassicalInvolution.RouteD.MultiD4

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

@[expose] def ModelStar (F : Type) [Field F] {KY : Type} [Group KY]
    (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∃ R₁ ∈ 𝓕, ∃ R₂ ∈ 𝓕, ∃ Rc ∈ 𝓕, Commutes R R₁ ∧ Commutes R R₂ ∧ Commutes R₁ R₂ ∧
    (∃ W, LinearBlockStandardPair F W R Rc) ∧ (∃ W, LinearBlockStandardPair F W R₁ Rc) ∧
    (∃ W, LinearBlockStandardPair F W R₂ Rc)

theorem ModelStar.of_node_star {t : StatedLieTag} {K : Type} [Group K] {D : UniversalRootDatum K}
    (hsc : FundamentalSingleClass t D) {F : Type} [Field F]
    {R₀ R₁ R₂ Rc : Subgroup K} (h0 : R₀ ∈ fundamentalSubgroups t D)
    (h1 : R₁ ∈ fundamentalSubgroups t D) (h2 : R₂ ∈ fundamentalSubgroups t D)
    (hc : Rc ∈ fundamentalSubgroups t D) (c01 : Commutes R₀ R₁) (c02 : Commutes R₀ R₂)
    (c12 : Commutes R₁ R₂) (p0 : ∃ W, LinearBlockStandardPair F W R₀ Rc)
    (p1 : ∃ W, LinearBlockStandardPair F W R₁ Rc) (p2 : ∃ W, LinearBlockStandardPair F W R₂ Rc) :
    ModelStar F (fundamentalSubgroups t D) := by
  intro R hR
  obtain ⟨g, rfl⟩ := hsc R₀ h0 R hR
  refine ⟨conjSub g R₁, conjSub_mem_fundamentalSubgroups h1 g, conjSub g R₂,
    conjSub_mem_fundamentalSubgroups h2 g, conjSub g Rc, conjSub_mem_fundamentalSubgroups hc g,
    c01.conjSub g, c02.conjSub g, c12.conjSub g, ?_, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := p0
    exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := p1
    exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := p2
    exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW g⟩

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem false_of_star (c : ETCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 1 tY nY Ω z) (hne : (modelFund p f tY nY).Nonempty)
    (hstar : ModelStar (GaloisField p f) (modelFund p f tY nY))
    (hodd : ∀ y ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K, Odd (orderOf y)) : False := by
  classical
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, -⟩ := c.exists_member_of_fund hR₀
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hM.1 hxM
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx (fun h => hMK h.symm)
  obtain ⟨R₁, hR₁, R₂, hR₂, Rc, hRc, c01, c02, c12, p0, p1, p2⟩ := hstar RK hRK
  let Rn : Fin 4 → Subgroup (modelUniv tY nY p f Fact.out).K := ![RK, R₁, R₂, Rc]
  have hRn : ∀ a, Rn a ∈ modelFund p f tY nY := by
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
      ∃ W : Subgroup (modelUniv tY nY p f Fact.out).K,
        LinearBlockStandardPair (GaloisField p f) W (Rn a) (Rn b) := by
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
  have h03 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K (j 3) :=
    hj0 ▸ hjp 0 3 ⟨by decide, rfl⟩
  have h13 := hjp 1 3 ⟨by decide, rfl⟩
  have h23 := hjp 2 3 ⟨by decide, rfl⟩
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical (j 1) (hj 1).1.1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj 2).1.1
  obtain ⟨a₃, ha₃, hc₀, hc₁, hc₂, hw₃⟩ := d4Frame_holds (p := p) (f := f) c.hp2 c.hq G Ω
    c.hΩ.conjInvariant K (j 1) (j 2) (j 3) z w₁ w₂ c.hK (hj 1).1.1 (hj 2).1.1 (hj 3).1.1 c.hz hw₁
    hw₂ h01 h02 h12 h03 h13 h23
  have hz1 : j 1 ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (hj 1).1.1 c.hz.mem h01.symm
  have hz2 : j 2 ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (hj 2).1.1 c.hz.mem h02.symm
  have hz3 : a₃ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes ha₃ c.hz.mem hc₀
  have hne1 : j 1 ≠ K := fun h => not_commutes_self_of_mem c.hΩ c.hK (h ▸ h01)
  have hne2 : j 2 ≠ K := fun h => not_commutes_self_of_mem c.hΩ c.hK (h ▸ h02)
  have hne3 : a₃ ≠ K := fun h => not_commutes_self_of_mem c.hΩ c.hK (h ▸ hc₀)
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
  have hrng : ∀ {L : Subgroup G} {R : Subgroup (modelUniv tY nY p f Fact.out).K}
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
  have hyc : y ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K := by
    have := c.hY.perfK
    refine mem_center_of_comm_mem_center fun s => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hy]
    rw [commutatorElement_def, ← hcentral (c.d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
  have h2 : orderOf (locElt Ω z z hzY) = 2 := orderOf_locElt hzY c.hz.orderOf_eq_two
  have hdvd : orderOf (c.d.ψ y) ∣ orderOf y := orderOf_map_dvd c.d.ψ y
  rw [hy, h2] at hdvd
  have := Nat.odd_iff.mp (hodd y hyc)
  omega

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
