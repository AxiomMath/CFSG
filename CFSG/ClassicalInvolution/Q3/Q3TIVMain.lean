module

public import CFSG.ClassicalInvolution.Q3.Q3TIVCent
public import CFSG.ClassicalInvolution.Q3.Q3WASTImg
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinC
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Asc77.S28 (FalseTwinPure pairStab mem_pairStab
  conj_mem_of_centralizes conj_swap_mem inv_mem_of_adjacent)


theorem twinInvolutionRow3 {tY : StatedLieTag} {nY : ℕ} (rf : TwinRowFacts3 tY nY)
    (hmf : TwinProductCentral3 tY nY) (h3 : OddThreeFreeInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    {T : Subgroup G} (hT : IsTwinAt (conjClass3 K) K T z) : IsClassicalMember3 T z := by
  classical
  by_contra hnot
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨c⟩ := TwinLoc3.of_setup rf h3 hR hshape
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  obtain ⟨w, hw⟩ := hR.inClass.classical T hT.mem.1
  have hwz : w ≠ z := by
    rintro rfl
    exact hnot hw
  have hKΩ : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hK, isSubnormal_le hR.cls.subnormal⟩
  have hFT : FalseTwinPure (conjClass3 K) K T z w :=
    { conj := hR.inClass.conjInvariant
      trans := fun M ⟨g, hg⟩ => ⟨g, hg⟩
      hK := hK
      hT := hT.mem.1
      hz := isUniqueInvolution_of_exact3 (hex K hK) hR.cls
      hw := isUniqueInvolution_of_exact3 (hex T hT.mem.1) hw
      hwz := hwz
      hKT := Ne.symm hT.ne
      hKc := isSubnormal_le hR.cls.subnormal
      hTc := isSubnormal_le hw.subnormal
      hTz := hT.mem.2
      commK := hT.comm_K
      commT := hT.comm_T
      noniso := fun L hL hLK hLT => c.exists_noncomm_of_ne hKΩ hT.mem (Ne.symm hT.ne)
        hT.comm_K hT.comm_T hL hLK hLT }
  obtain ⟨ε, hε⟩ := claimA3 c hFT hR.cls hw hmf
  obtain ⟨g₀, hg₀, hg₀K, hg₀T⟩ := exists_member3 c hFT
  obtain ⟨s, hsK, hsT, hsz, hsw⟩ := hFT.exists_swap
  set u₀ : G := z * w with hu₀
  have hεg₀ : g₀ * u₀ * g₀⁻¹ = ε := hε g₀ hg₀ hg₀K hg₀T
  have hStabC : ∀ x : G, x * z * x⁻¹ = z → x ∈ pairStab u₀ ε := by
    intro x hx
    left
    have hxw := hFT.conj_w_eq_of_conj_z_eq hx
    refine ⟨?_, ?_⟩
    · calc x * u₀ * x⁻¹ = (x * z * x⁻¹) * (x * w * x⁻¹) := by rw [hu₀]; group
        _ = u₀ := by rw [hx, hxw]
    · obtain ⟨h1, h2, h3⟩ := conj_mem_of_centralizes hFT hg₀ hg₀K hg₀T hx
      have := hε (x * g₀) (by rw [conjSub_mul]; exact h1) (by rw [conjSub_mul]; exact h2)
        (by rw [conjSub_mul]; exact h3)
      calc x * ε * x⁻¹ = x * (g₀ * u₀ * g₀⁻¹) * x⁻¹ := by rw [hεg₀]
        _ = (x * g₀) * u₀ * (x * g₀)⁻¹ := by group
        _ = ε := this
  have hStabS : s ∈ pairStab u₀ ε := by
    left
    refine ⟨?_, ?_⟩
    · calc s * u₀ * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by rw [hu₀]; group
        _ = w * z := by rw [hsz, hsw]
        _ = u₀ := hFT.comm_zw.symm
    · obtain ⟨h1, h2, h3⟩ := conj_swap_mem hFT hg₀ hg₀K hg₀T hsK hsT hsz
      have := hε (s * g₀) (by rw [conjSub_mul]; exact h1) (by rw [conjSub_mul]; exact h2)
        (by rw [conjSub_mul]; exact h3)
      calc s * ε * s⁻¹ = s * (g₀ * u₀ * g₀⁻¹) * s⁻¹ := by rw [hεg₀]
        _ = (s * g₀) * u₀ * (s * g₀)⁻¹ := by group
        _ = ε := this
  have hStabA : ∀ g : G, conjSub g K ∈ centralizingMembers (conjClass3 K) {z} →
      conjSub g K ≠ K → conjSub g K ≠ T → g ∈ pairStab u₀ ε := by
    intro g h1 h2 h3
    right
    refine ⟨hε g h1 h2 h3, ?_⟩
    obtain ⟨i1, i2, i3⟩ := inv_mem_of_adjacent hFT h1 h2 h3
    have := hε g⁻¹ i1 i2 i3
    calc g * ε * g⁻¹ = g * (g⁻¹ * u₀ * g⁻¹⁻¹) * g⁻¹ := by rw [this]
      _ = u₀ := by group
  let 𝔖 : Set (Subgroup G) :=
    {M | M ∈ conjClass3 K ∧ ∃ x ∈ pairStab u₀ ε, conjSub x K = M}
  have hK𝔖 : K ∈ 𝔖 := ⟨hK, 1, (pairStab u₀ ε).one_mem, conjSub_one K⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ conjClass3 K, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨-, x, hx, rfl⟩ L ⟨y, rfl⟩ hLN hNL
    refine ⟨⟨y, rfl⟩, y, ?_, rfl⟩
    have hM : conjSub (x⁻¹ * y) K = conjSub x⁻¹ (conjSub y K) := conjSub_mul _ _ _
    have hKx : conjSub x⁻¹ (conjSub x K) = K := conjSub_inv_conjSub x K
    have hcomm : Commutes K (conjSub (x⁻¹ * y) K) := by
      have := hNL.conjSub x⁻¹
      rwa [hKx, ← hM] at this
    have hMK : conjSub (x⁻¹ * y) K ≠ K := by
      intro e
      apply hLN
      have h2 : conjSub x⁻¹ (conjSub y K) = conjSub x⁻¹ (conjSub x K) := by rw [← hM, e, hKx]
      exact conjSub_injective x⁻¹ h2
    have hMz : conjSub (x⁻¹ * y) K ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hR.inClass.conjInvariant _ K hK, fun m hm => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z hR.cls.mem m hm).symm⟩
    have hxy : x⁻¹ * y ∈ pairStab u₀ ε := by
      by_cases hMT : conjSub (x⁻¹ * y) K = T
      · have hn : conjSub (s⁻¹ * (x⁻¹ * y)) K = K := by
          rw [conjSub_mul, hMT, ← hsK, conjSub_inv_conjSub]
        have hnz := hFT.conj_K_stab hn
        have := (pairStab u₀ ε).mul_mem hStabS (hStabC _ hnz)
        simpa using this
      · exact hStabA _ hMz hMK hMT
    have := (pairStab u₀ ε).mul_mem hx hxy
    simpa using this
  have hconn : RouteD.DeltaConnected (conjClass3 K) :=
    (CoreAssembly.deltaConnected_iff K).mp hR.conn
  have hall : conjClass3 K ⊆ 𝔖 :=
    subset_of_adj_closed hconn (fun M hM => hM.1) ⟨K, hK𝔖⟩ hcl
  have hallStab : ∀ g : G, g ∈ pairStab u₀ ε := by
    intro g
    obtain ⟨-, x, hx, hxg⟩ := hall ⟨g, rfl⟩
    have hxg' : conjSub x K = conjSub g K := hxg
    have hn : conjSub (x⁻¹ * g) K = K := by rw [conjSub_mul, ← hxg', conjSub_inv_conjSub]
    have hnz := hFT.conj_K_stab hn
    have := (pairStab u₀ ε).mul_mem hx (hStabC _ hnz)
    simpa using this
  have hz2 : z * z = 1 := hFT.hz.sq
  have hu1 : u₀ ≠ 1 := by
    intro h1
    apply hwz
    calc w = z * (z * w) := by rw [← mul_assoc, hz2, one_mul]
      _ = z := by rw [← hu₀, h1, mul_one]
  by_cases hεu : ε = u₀
  ·
    have hcen : u₀ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      rcases hallStab g with ⟨h1, -⟩ | ⟨h1, -⟩
      · calc g * u₀ = (g * u₀ * g⁻¹) * g := by group
          _ = u₀ * g := by rw [h1]
      · calc g * u₀ = (g * u₀ * g⁻¹) * g := by group
          _ = ε * g := by rw [h1]
          _ = u₀ * g := by rw [hεu]
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hcen
    exact hu1 hcen
  ·
    have hnorm : (Subgroup.centralizer ({u₀} : Set G)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
      have hnu : n * u₀ * n⁻¹ = u₀ := by rw [hn]; group
      have ha : n * (g⁻¹ * u₀ * g) * n⁻¹ = g⁻¹ * u₀ * g := by
        have hg := hallStab g⁻¹
        rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
        · have : g⁻¹ * u₀ * g⁻¹⁻¹ = u₀ := h1
          rw [show g⁻¹ * u₀ * g = u₀ from by simpa using this]
          exact hnu
        · have h1' : g⁻¹ * u₀ * g = ε := by simpa using h1
          rw [h1']
          rcases hallStab n with ⟨h2, h3⟩ | ⟨h2, h3⟩
          · exact h3
          · exact absurd (hnu.symm.trans h2) (Ne.symm hεu)
      have hgu : g * (g⁻¹ * u₀ * g) * g⁻¹ = u₀ := by group
      calc (g * n * g⁻¹) * u₀ = (g * n * g⁻¹) * u₀ * (g * n * g⁻¹)⁻¹ * (g * n * g⁻¹) := by group
        _ = g * (n * (g⁻¹ * u₀ * g) * n⁻¹) * g⁻¹ * (g * n * g⁻¹) := by group
        _ = g * (g⁻¹ * u₀ * g) * g⁻¹ * (g * n * g⁻¹) := by rw [ha]
        _ = u₀ * (g * n * g⁻¹) := by rw [hgu]
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.centralizer ({u₀} : Set G)) with hb | ht
    · have hzmem : z ∈ Subgroup.centralizer ({u₀} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z * u₀ = z * (w * z) := by rw [hu₀, hFT.comm_zw]
          _ = u₀ * z := by rw [hu₀]; group
      rw [hb, Subgroup.mem_bot] at hzmem
      exact hFT.hz.ne_one hzmem
    · have hg₀mem : g₀ ∈ Subgroup.centralizer ({u₀} : Set G) := by rw [ht]; trivial
      rw [Subgroup.mem_centralizer_singleton_iff] at hg₀mem
      apply hεu
      rw [← hεg₀]
      calc g₀ * u₀ * g₀⁻¹ = (u₀ * g₀) * g₀⁻¹ := by rw [hg₀mem]
        _ = u₀ := by group

end CFSG.ClassicalInvolution.Q3.Q3TIV
