module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Setting

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_center {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hSN : S ≤ normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ u ∈ N, orderOf u = 2 ∧ ∀ s ∈ S, s * u = u * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hM : N.subgroupOf S ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hNS hx⟩ : S) ∈ N.subgroupOf S := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at hmem
    rw [mem_bot]
    exact congrArg Subtype.val hmem
  have hMn : (N.subgroupOf S).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hSN g.2) x).mp hx⟩
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
  have hZp : IsPGroup 2 ↥(N.subgroupOf S ⊓ center S) := hS.to_subgroup _
  rcases hZp.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((y : S) : G), mem_subgroupOf.mp (mem_inf.mp y.2).1, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp y.2).2 ⟨s, hs⟩)

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem z2 : orderOf z = 2 := h.pmax.1.1

theorem zL : IsTwoComponentAt z L := h.pmax.1

theorem centralizer_le_normalizer : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
  le_normalizer_of_mem_footeFamilyOf h.sec4.huniq h.zL h.memF

theorem quotient_simple : IsSimpleGroup (L ⧸ pPrimeCore 2 L) ∧
    Nonempty (L ⧸ pPrimeCore 2 L ≃* L₀ ⧸ Open.fusionZStar L₀) :=
  isSimpleGroup_quotient_of_mem_footeFamilyOf h.sec4.hGA h.sec4.hGC h.sec4.hSA
    h.sec4.footeFamilyType h.sec4.hrank2 h.zL h.memF

theorem isPGroup_S : IsPGroup 2 S := h.sylS.isPGroup

theorem isPGroup_Q : IsPGroup 2 Q := h.sylQ.isPGroup

theorem S_le : S ≤ normalizer (L : Set G) := h.sylS.le

theorem Q_le : Q ≤ coreActionKernel L := h.sylQ.le

theorem zS_mem : z ∈ S := h.QS h.zQ

theorem S_le_centralizer : S ≤ centralizer ({z} : Set G) := fun s hs =>
  mem_centralizer_singleton_iff.mpr (h.zS s hs)

theorem inf_coreActionKernel : S ⊓ coreActionKernel L = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylQ.eq_of_le (le_inf h.QS h.Q_le) inf_le_right (h.isPGroup_S.to_le inf_le_left)

theorem conj_mem_Q {s q : G} (hs : s ∈ S) (hq : q ∈ Q) : s * q * s⁻¹ ∈ Q := by
  rw [← h.inf_coreActionKernel] at hq ⊢
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hq).1) (inv_mem hs),
    (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L (h.S_le hs)) q).mp
      (mem_inf.mp hq).2⟩

theorem S_le_normalizer_Q : S ≤ normalizer (Q : Set G) := fun s hs =>
  mem_normalizer_iff.mpr fun q => ⟨fun hq => h.conj_mem_Q hs hq, fun hq => by
    have h1 := h.conj_mem_Q (inv_mem hs) hq
    rwa [inv_inv, show s⁻¹ * (s * q * s⁻¹) * s = q by group] at h1⟩

theorem R_sylow : IsSylowOf 2 (S ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylS.inf_of_le_normalizer le_normalizer le_rfl

theorem conj_mem_R {s r : G} (hs : s ∈ S) (hr : r ∈ S ⊓ L) : s * r * s⁻¹ ∈ S ⊓ L :=
  mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hr).1) (inv_mem hs),
    (mem_normalizer_iff.mp (h.S_le hs) r).mp (mem_inf.mp hr).2⟩

theorem S_le_normalizer_R : S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := fun s hs =>
  mem_normalizer_iff.mpr fun r => ⟨fun hr => h.conj_mem_R hs hr, fun hr => by
    have h1 := h.conj_mem_R (inv_mem hs) hr
    rwa [inv_inv, show s⁻¹ * (s * r * s⁻¹) * s = r by group] at h1⟩

theorem not_involution_mem_inf {x : G} (hxL : x ∈ L) (hxC : x ∈ coreActionKernel L) :
    orderOf x ≠ 2 := by
  intro hx
  have := h.quotient_simple.1
  apply center_ne_bot_of_mem_coreActionKernel hxL hx hxC
  have hq := isQuasisimple_quotient_of_isPComponent h.zL.2.1 h.zL.2.2
  obtain ⟨u, v, huv⟩ := exists_mul_ne_mul_of_isQuasisimple hq
  exact center_eq_bot_of_isSimpleGroup ⟨u, v, huv⟩

theorem Q_inf_L : Q ⊓ L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hp : IsPGroup 2 ↥(Q ⊓ L) := h.isPGroup_Q.to_le inf_le_left
  rcases hp.card_eq_or_dvd with h1 | h2
  · exact hne (Subgroup.card_eq_one.mp h1)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine h.not_involution_mem_inf (mem_inf.mp y.2).2 (h.Q_le (mem_inf.mp y.2).1) ?_
  rw [Subgroup.orderOf_coe, hy]

theorem commute_Q_R {q r : G} (hq : q ∈ Q) (hr : r ∈ S ⊓ L) : q * r = r * q := by
  have h1 : q * r * q⁻¹ * r⁻¹ ∈ Q := by
    have h2 := h.conj_mem_Q (mem_inf.mp hr).1 (inv_mem hq)
    rw [show q * r * q⁻¹ * r⁻¹ = q * (r * q⁻¹ * r⁻¹) by group]
    exact mul_mem hq h2
  have h3 : q * r * q⁻¹ * r⁻¹ ∈ S ⊓ L := by
    have h4 := h.conj_mem_R (h.QS hq) hr
    exact mul_mem h4 (inv_mem hr)
  have h5 : q * r * q⁻¹ * r⁻¹ ∈ Q ⊓ L := mem_inf.mpr ⟨h1, (mem_inf.mp h3).2⟩
  rw [h.Q_inf_L, mem_bot] at h5
  calc q * r = q * r * q⁻¹ * r⁻¹ * (r * q) := by group
    _ = r * q := by rw [h5, one_mul]

theorem tR : t ∈ S ⊓ L := mem_inf.mpr ⟨h.tS, h.tL⟩

theorem pRank_Q : CFSG.pRank 2 ↥Q = 2 := by
  have h1 := pRank_subgroup_mono h.Q_le
  have h2 := pRank_le_of_isSylowOf h.sylQ
  rw [h.rankCL] at h1 h2
  omega

theorem z_ne_t : z ≠ t := by
  intro hzt
  have hz : z ∈ Q ⊓ L := mem_inf.mpr ⟨h.zQ, hzt ▸ h.tL⟩
  rw [h.Q_inf_L, mem_bot] at hz
  have := h.z2
  rw [hz, orderOf_one] at this
  omega

theorem repoint {u : G} (huQ : u ∈ Q) (hu2 : orderOf u = 2) (huS : ∀ s ∈ S, s * u = u * s) :
    Sec5 G L₀ (footeF L₀ u) Q S T u t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := h.sec4
  have huC : u ∈ coreActionKernel L := h.Q_le huQ
  obtain ⟨hfix, hLu, hLuF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hu2 huC
  obtain ⟨B, hB, hBmax, hBF, -⟩ :=
    exists_mem_footeFamilyOf_of_mem_coreActionKernel h4.hLB h4.huniq h.pmax h.memF hu2 huC
  have hBL : B = footeF L₀ u := (eq_footeF h4.huniq hB hBF).symm
  have hLmax : FootePointedMaximal u (footeF L₀ u) := hBL ▸ hBmax
  have hLu' : IsTwoComponentAt u (footeFixed L u) := hfix ▸ hLu
  have hQL : Q ≤ coreActionKernel (footeF L₀ u) := by
    intro q hq
    rw [← hfix]
    exact mem_coreActionKernel_footeFixed (huS q (h.QS hq)).symm (h.Q_le hq) hLu'
  have hrk : CFSG.pRank 2 ↥(coreActionKernel (footeF L₀ u)) = 2 := by
    refine le_antisymm (h.rankC _ hLuF) ?_
    have h1 := pRank_subgroup_mono hQL
    rwa [h.pRank_Q] at h1
  have hQsyl : IsSylowOf 2 Q (coreActionKernel (footeF L₀ u)) :=
    isSylowOf_of_twoPart_le h.isPGroup_Q hQL (h.maxQ _ hLuF hrk)
  have hSL : S ≤ normalizer ((footeF L₀ u : Subgroup G) : Set G) := fun s hs =>
    le_normalizer_of_mem_footeFamilyOf h4.huniq hLu hLuF
      (mem_centralizer_singleton_iff.mpr (huS s hs))
  have hd : twoPart (coreActionKernel (footeF L₀ u)) = Nat.card Q := hQsyl.card_eq.symm
  have hSsyl : IsSylowOf 2 S (normalizer ((footeF L₀ u : Subgroup G) : Set G)) :=
    isSylowOf_of_twoPart_le h.isPGroup_S hSL (h.maxS _ hLuF hrk hd)
  have htL : t ∈ footeF L₀ u := by
    rw [← hfix, footeFixed]
    refine subset_closure ⟨mem_sup_left (mem_inf.mpr ⟨h.tL, ?_⟩), 1, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (h.tZ u (h.QS huQ)).symm
    · rw [pow_one, h.t2]
  exact ⟨h4, h.rankC, hLuF, hLmax, hrk, hQsyl, h.maxQ, hSsyl, h.QS, h.maxS, h.sylT, h.ST,
    huQ, huS, h.tS, htL, h.tZ, h.t2⟩

end Sec5

end CFSG.ComponentClassification.Foote5
