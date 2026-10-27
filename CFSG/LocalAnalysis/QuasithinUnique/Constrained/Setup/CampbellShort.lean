module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem pCoreOf_le_of_isSubnormal {K H : Subgroup G} (p : ℕ) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) : pCoreOf p K ≤ pCoreOf p H := by
  have key : ∀ Y : Subgroup H, Y.IsSubnormal → pCoreOf p (Y.map H.subtype) ≤ pCoreOf p H := by
    intro Y hY
    induction hY with
    | top =>
      exact le_of_eq (by rw [Subgroup.map_top, Subgroup.range_subtype])
    | step Y Z hYZ hZ hN ih =>
      refine le_trans ?_ ih
      refine CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal p _ _
        (Subgroup.map_mono hYZ) ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hYZ)]
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYZ] at hN
      exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)
  have := key _ hK
  rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at this

theorem le_pCoreOf_of_normal_subgroupOf {H N : Subgroup G} (p : ℕ) (hle : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ pCoreOf p H :=
  CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf p N H hle hN hp

open scoped commutatorElement in
theorem central_core_module_recognizes_short_subgroup [Finite G] {H K : Subgroup G}
    (hH : CharTwo H) (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal)
    (hno : NoPQuotient 2 K)
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∨ Nat.card (K ⧸ CFSG.pCore 2 K) = 3)
    (hZ : ⁅blockQ H, K⁆ ≤ Subgroup.centralizer (blockQ H : Set G))
    (hnz : ⁅blockQ H, K⁆ ⊓ Subgroup.centralizer (K : Set G) < ⁅blockQ H, K⁆)
    (hsq : ∀ x ∈ ⁅blockQ H, K⁆, x ^ 2 ∈ ⁅blockQ H, K⁆ ⊓ Subgroup.centralizer (K : Set G))
    (hirr : ∀ W : Subgroup G, ⁅blockQ H, K⁆ ⊓ Subgroup.centralizer (K : Set G) ≤ W →
      W ≤ ⁅blockQ H, K⁆ → K ≤ Subgroup.normalizer (W : Set G) →
      W = ⁅blockQ H, K⁆ ⊓ Subgroup.centralizer (K : Set G) ∨ W = ⁅blockQ H, K⁆) :
    blockQ K = K ⊓ blockQ H ∧ blockU K = ⁅blockQ H, K⁆ ∧
      (∀ x ∈ ⁅blockQ H, K⁆, x ^ 2 = 1) ∧ CharTwo K ∧ IsShort2 K ∧ IsBlock2 H K ∧
      (((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 3 ∨ IsAltType K 5) → IsChi0Block H K) := by
  classical
  have hQ2 : IsPGroup 2 (blockQ H) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 H
  have hQH : blockQ H ≤ H := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H
  have hQn : ((blockQ H).subgroupOf H).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hHQ : H ≤ Subgroup.normalizer (blockQ H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQn
  have hKQ : K ≤ Subgroup.normalizer (blockQ H : Set G) := hKH.trans hHQ
  have hAQ : blockQ K ≤ blockQ H := pCoreOf_le_of_isSubnormal 2 hKH hsub
  have hAK : blockQ K ≤ K := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 K
  have hKQA : K ⊓ blockQ H ≤ blockQ K := by
    have hKnorm : K ≤ Subgroup.normalizer ((K ⊓ blockQ H : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hkQ := Subgroup.mem_normalizer_iff.mp (hHQ (hKH hk)) x
      constructor
      · intro hx
        obtain ⟨hxK, hxQ⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hxK) (inv_mem hk), hkQ.mp hxQ⟩
      · intro hx
        obtain ⟨hxK, hxQ⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨?_, hkQ.mpr hxQ⟩
        have := mul_mem (mul_mem (inv_mem hk) hxK) hk
        simpa [mul_assoc] using this
    exact le_pCoreOf_of_normal_subgroupOf 2 inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKnorm)
      (hQ2.to_le inf_le_right)
  have hA : blockQ K = K ⊓ blockQ H := le_antisymm (le_inf hAK hAQ) hKQA
  have hUA : ⁅blockQ H, K⁆ ≤ blockQ K := by
    have hX : (K.subgroupOf H).IsSubnormal := hsub
    have hno' : NoPQuotient 2 (K.subgroupOf H) :=
      NoPQuotient.of_surjective (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective hno
    have hR : IsPGroup 2 ((blockQ H).subgroupOf H) :=
      hQ2.of_surjective (Subgroup.subgroupOfEquivOfLe hQH).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hQH).symm.surjective
    have hXR : K.subgroupOf H ≤ Subgroup.normalizer (((blockQ H).subgroupOf H : Subgroup H) :
        Set H) := by
      intro x _
      rw [Subgroup.normalizer_eq_top_iff.mpr hQn]
      trivial
    have := (prime_residual_subnormal_p_signalizer_action hX hno' hR hXR).2
    have h2 := Subgroup.map_mono (f := H.subtype) this
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hQH,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 H (K.subgroupOf H),
      Subgroup.map_subgroupOf_eq_of_le hKH] at h2
    rw [Subgroup.commutator_comm]
    exact h2
  have hsat : ⁅⁅blockQ H, K⁆, K⁆ = ⁅blockQ H, K⁆ :=
    prime_residual_central_commutator_saturation hQ2 hKQ hno hZ
  have hUK : blockU K = ⁅blockQ H, K⁆ := by
    change ⁅blockQ K, K⁆ = _
    apply le_antisymm (Subgroup.commutator_mono hAQ le_rfl)
    calc ⁅blockQ H, K⁆ = ⁅⁅blockQ H, K⁆, K⁆ := hsat.symm
      _ ≤ ⁅blockQ K, K⁆ := Subgroup.commutator_mono hUA le_rfl
  have hUQ : ⁅blockQ H, K⁆ ≤ blockQ H := commutator_le_left_of_normalizes hKQ
  have hUab : ∀ u ∈ ⁅blockQ H, K⁆, ∀ v ∈ ⁅blockQ H, K⁆, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (hZ hv) u (hUQ hu))
  have hUnorm : K ≤ Subgroup.normalizer ((⁅blockQ H, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hKQ
  have hUU : (⁅⁅blockQ H, K⁆, K⁆ : Subgroup G) ≤ ⁅blockQ H, K⁆ :=
    commutator_le_left_of_normalizes hUnorm
  have hexp : ∀ x ∈ ⁅blockQ H, K⁆, x ^ 2 = 1 := by
    have key : ∀ x ∈ (⁅⁅blockQ H, K⁆, K⁆ : Subgroup G), x ^ 2 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u, hu, k, hk, rfl⟩ := hx
        obtain ⟨w, hw_def⟩ : ∃ w : G, w = k * u⁻¹ * k⁻¹ := ⟨_, rfl⟩
        have hwU : w ∈ (⁅blockQ H, K⁆ : Subgroup G) := by
          rw [hw_def]
          exact (Subgroup.mem_normalizer_iff.mp (hUnorm hk) u⁻¹).mp (inv_mem hu)
        have hu2 : u ^ 2 ∈ Subgroup.centralizer (K : Set G) := (hsq u hu).2
        have hk2 : Commute k (u ^ 2) := Subgroup.mem_centralizer_iff.mp hu2 k hk
        have hcomm : u * w = w * u := hUab u hu w hwU
        have hx : ⁅u, k⁆ = u * w := by
          rw [hw_def]; simp only [commutatorElement_def]; group
        have hw2 : w * w = (u ^ 2)⁻¹ := by
          have h1 : w * w = k * (u ^ 2)⁻¹ * k⁻¹ := by rw [hw_def]; group
          rw [h1, hk2.inv_right.eq]; group
        calc ⁅u, k⁆ ^ 2 = (u * w) * (u * w) := by rw [hx, pow_two]
          _ = u * (w * u) * w := by group
          _ = u * (u * w) * w := by rw [← hcomm]
          _ = u ^ 2 * (w * w) := by rw [pow_two]; simp only [mul_assoc]
          _ = 1 := by rw [hw2]; exact mul_inv_cancel _
      | one => simp
      | mul x y hx hy ihx ihy =>
        have hxU : x ∈ (⁅blockQ H, K⁆ : Subgroup G) := hUU hx
        have hyU : y ∈ (⁅blockQ H, K⁆ : Subgroup G) := hUU hy
        have hcomm : Commute x y := hUab x hxU y hyU
        rw [hcomm.mul_pow, ihx, ihy]; simp
      | inv x hx ih => rw [inv_pow, ih]; simp
    rw [hsat] at key
    exact key
  have hchar : CharTwo K := hH.of_isSubnormal hKH hsub
  have hshort : IsShort2 K := by
    refine ⟨hno, hchar, ⟨?_, ?_⟩, hq, ?_⟩
    · rw [hUK]
      refine le_inf (hUA.trans ?_) ?_
      · exact le_of_eq rfl
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact Subgroup.mem_centralizer_iff.mp (hZ hu) a (hAQ ha)
    · rw [hUK]; exact hexp
    · have hZK : blockZ K = ⁅blockQ H, K⁆ ⊓ Subgroup.centralizer (K : Set G) := by
        unfold blockZ; rw [hUK]
      rw [hZK, hUK]
      exact ⟨hnz, hirr⟩
  have hblock : IsBlock2 H K := ⟨hshort, hKH, hsub⟩
  exact ⟨hA, hUK, hexp, hchar, hshort, hblock, fun h => ⟨hblock, h⟩⟩

end CFSG.QuasithinUnique.Setup.Campbell
