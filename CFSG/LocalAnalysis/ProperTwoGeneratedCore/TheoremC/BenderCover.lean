module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCentral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent
public import CFSG.Walter.AStar.Subnormal
public import CFSG.StronglyEmbedded

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly BenderCover

theorem BenderCover.isStronglyEmbeddedOrder_of_fusionStronglyEmbedded {G : Type*} [Group G]
    {M : Subgroup G} (h : fusionStronglyEmbedded M) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have hg' : g⁻¹ ∉ M := fun h' => hg (by simpa only [inv_inv] using M.inv_mem h')
  simpa only [inv_inv] using h.2.2 g⁻¹ hg'

variable {X : Type} [Group X] [Finite X]

namespace CoreConfig

variable {Y : Subgroup X} {u z : X}

theorem component_center_eq_of_mul_self (hc : CoreConfig Y u z) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (huJ : u ∈ J) {s : J} (hs : s ∈ Subgroup.center J)
    (hss : s * s = 1) : s = 1 ∨ s = ⟨u, huJ⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨hs1, hsu⟩ := hne
  obtain ⟨-, hZO⟩ := component_center_le_twoCore hc.oddCore_eq_bot hJ
  have hsO : (s : X) ∈ CFSG.pCore 2 X := hZO (Subgroup.mem_map_of_mem _ hs)
  have huc : (⟨u, huJ⟩ : J) ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hc.commute_center g).eq
  have huO : u ∈ CFSG.pCore 2 X := hZO (Subgroup.mem_map_of_mem _ huc)
  have hs2 : orderOf (s : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two, hss]) hs1
  have hne' : (s : X) ≠ u := fun h => hsu (Subtype.ext h)
  have hrank := two_le_pRank_of_commuting_involutions hsO huO hs2 hc.order hne'
    (hc.commute_center s)
  obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
  have hOY : CFSG.pCore 2 X ≤ Y :=
    ((CFSG.pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal P).trans hPY
  have hN := hc.normalizer_le _ hOY hrank
  rw [Subgroup.normalizer_eq_top] at hN
  exact hc.ne_top (top_le_iff.mp hN)

end CoreConfig

theorem benderCoverExclusion
    (hB : BenderBorelFactsHold) : BenderCoverExclusion := by
  intro X _ _ Y u z P J hc hJ hse
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : J.Normal := hJ.normal
  obtain ⟨⟨hperf, hsimple, -⟩, hsub⟩ := hJ.component
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hsimple
  have hbender := CFSG.BenderSuzuki.bender_suzuki (componentImage Y J)
    (isStronglyEmbeddedOrder_of_fusionStronglyEmbedded hse)
  obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hsub
  have hQmem : ∀ q : J, q ∈ (Q : Subgroup J) ↔ (q : X) ∈ (P : Subgroup X) := by
    intro q
    constructor
    · intro hq
      have h : (q : X) ∈ (Q : Subgroup J).map J.subtype := Subgroup.mem_map_of_mem _ hq
      rw [hQ] at h
      exact h.1
    · intro hq
      have h : (q : X) ∈ (P : Subgroup X) ⊓ J := ⟨hq, q.2⟩
      rw [← hQ] at h
      obtain ⟨q', hq', hqq'⟩ := h
      rwa [← Subtype.ext hqq']
  have hBF := hB _ hbender (Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)))
  rw [Sylow.coe_mapSurjective] at hBF
  obtain ⟨hZ2, -⟩ := component_center_le_twoCore hc.oddCore_eq_bot hJ.component
  have hfix : ∀ q ∈ (Q : Subgroup J), MulAut.conjNormal z q = q := fun q hq => Subtype.ext (by
    rw [MulAut.conjNormal_apply, ← (hJ.lever_comm _ ((hQmem q).mp hq)).eq,
      mul_inv_cancel_right])
  have hw : ∃ w₀ ∈ (Q : Subgroup J), (∀ q ∈ (Q : Subgroup J), Commute q w₀) ∧
      w₀ ∉ Subgroup.center J := by
    rcases hJ.lever with hzJ | ⟨-, y, hy, t, -, ht2, -, hyz⟩
    · refine ⟨⟨z, hzJ⟩, (hQmem _).mpr hJ.lever_mem, fun q hq => Subtype.ext ?_, fun hzc => ?_⟩
      · exact (hJ.lever_comm _ ((hQmem q).mp hq)).eq
      · have hzz : (⟨z, hzJ⟩ : J) * ⟨z, hzJ⟩ = 1 := Subtype.ext (by
          change z * z = 1
          rw [← pow_two, ← hc.lever_order, pow_orderOf_eq_one])
        rcases hc.component_center_eq_of_mul_self hJ.component hJ.mem hzc hzz with h | h
        · have h1 : z = 1 := congrArg Subtype.val h
          have h2 := hc.lever_order
          rw [h1, orderOf_one] at h2
          exact absurd h2 (by decide)
        · exact hc.lever_ne (congrArg Subtype.val h)
    · by_contra hcon
      push Not at hcon
      obtain ⟨r, hrQ, hr⟩ := exists_eq_conj_of_perfect hperf.commutator_eq_top hBF.aut_inner
        (MulAut.conjNormal z) hfix
      have hrc : ∀ q ∈ (Q : Subgroup J), Commute q r := fun q hq => by
        have h := (hr q).symm.trans (hfix q hq)
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
      have hrZ := hcon r hrQ hrc
      have hzc : ∀ k : J, z * k * z⁻¹ = k := fun k => by
        have h := congrArg Subtype.val (hr k)
        rw [MulAut.conjNormal_apply] at h
        rw [h, ← Subgroup.mem_center_iff.mp hrZ k, mul_inv_cancel_right]
      have hyz' : y⁻¹ * z * y = z := by
        have h := hzc ⟨y, hy.1⟩
        rw [mul_inv_eq_iff_eq_mul] at h
        change z * y = y * z at h
        rw [mul_assoc, h, inv_mul_cancel_left]
      have ht1 : t = 1 := by
        rw [hyz'] at hyz
        exact mul_eq_left.mp hyz.symm
      rw [ht1, orderOf_one] at ht2
      exact absurd ht2 (by decide)
  obtain ⟨w₀, hw₀Q, hw₀c, hw₀Z⟩ := hw
  have hbot := center_eq_bot_of_borelFacts hperf.commutator_eq_top hZ2
    (fun s hs hss => hc.component_center_eq_of_mul_self hJ.component hJ.mem hs hss) Q hBF hw₀Q
    hw₀c hw₀Z
  have huc : (⟨u, hJ.mem⟩ : J) ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hc.commute_center g).eq
  rw [hbot, Subgroup.mem_bot] at huc
  have h2 := hc.order
  rw [show u = 1 from congrArg Subtype.val huc, orderOf_one] at h2
  exact absurd h2 (by decide)

end CFSG.ProperTwoGeneratedCore.TheoremC
