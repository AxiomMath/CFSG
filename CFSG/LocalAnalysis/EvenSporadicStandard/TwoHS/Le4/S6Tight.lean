module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PerfectLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Lift

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_four {g : G} (hg : orderOf g = 4) :
    IsPGroup 2 (zpowers g) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.tight_phi (h : StdHyp G L)
    (hZ : ∀ z ∈ center L, z ^ 2 = 1)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2) {s : G}
    (hs4 : orderOf s = 4) (hsN : s ∈ normalizer (L : Set G))
    (hsC : ∀ y ∈ zpowers s, y ∈ centralizer (L : Set G) → y = 1)
    (hsT : ∀ x : G, x * s ^ 2 = s ^ 2 * x → x * s * x⁻¹ ∈ zpowers s) :
    ∃ (zL : L) (c : G), c ∈ centralizer (L : Set G) ∧ (zL : G) * c = s ^ 2 ∧
      Commute (zL : G) c ∧ zL * zL ∈ center L ∧ zL ∉ center L ∧
      orderOf (zL : L ⧸ center L) = 2 ∧
      normalizerAction L ⟨s, hsN⟩ * normalizerAction L ⟨s, hsN⟩ =
        MulAut.conj (zL : L ⧸ center L) ∧
      ∀ q ∈ centralizer ({(zL : L ⧸ center L)} : Set (L ⧸ center L)), Odd (orderOf q) →
        normalizerAction L ⟨s, hsN⟩ q = q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : commutator L = ⊤ := h.standard.1.1
  set C := centralizer (L : Set G) with hCdef
  have hs44 : s ^ 4 = 1 := by rw [← hs4]; exact pow_orderOf_eq_one s
  have hs2ne : s ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs4] at this
    omega
  have hs2s2 : s ^ 2 * s ^ 2 = 1 := by rw [← pow_add]; exact hs44
  have hs2 : s ^ 2 ∈ L ⊔ C := h.sq_mem_sup_centralizer hout hsN
  obtain ⟨l₂, hl₂, c₂, hc₂, hsq⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (A := L) (B := C) le_rfl hs2
  have hlc : Commute l₂ c₂ := mem_centralizer_iff.mp hc₂ l₂ hl₂
  have hsq' : (l₂ * c₂) * (l₂ * c₂) = l₂ * l₂ * (c₂ * c₂) := by
    calc (l₂ * c₂) * (l₂ * c₂) = l₂ * (c₂ * l₂) * c₂ := by group
      _ = l₂ * (l₂ * c₂) * c₂ := by rw [← hlc.eq]
      _ = l₂ * l₂ * (c₂ * c₂) := by group
  have h1 : l₂ * l₂ * (c₂ * c₂) = 1 := by rw [← hsq', ← hsq, hs2s2]
  have hzzL : l₂ * l₂ ∈ L := L.mul_mem hl₂ hl₂
  have hzzC : l₂ * l₂ ∈ C := by
    have hcc : c₂ * c₂ ∈ C := C.mul_mem hc₂ hc₂
    have : l₂ * l₂ = (c₂ * c₂)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact C.inv_mem hcc
  have hzzZ : (⟨l₂ * l₂, hzzL⟩ : L) ∈ center L := by
    have hmem : l₂ * l₂ ∈ (center L).map L.subtype := by
      rw [map_center_eq_inf_centralizer]; exact ⟨hzzL, hzzC⟩
    obtain ⟨w, hw, hwe⟩ := hmem
    have : w = ⟨l₂ * l₂, hzzL⟩ := Subtype.ext hwe
    rwa [this] at hw
  set zL : L := ⟨l₂, hl₂⟩ with hzLdef
  have hzL2 : zL * zL ∈ center L := hzzZ
  have hzcen : zL ∉ center L := by
    intro hz
    have hzC : l₂ ∈ C := mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩)
    have hs2C : s ^ 2 ∈ C := by rw [hsq]; exact C.mul_mem hzC hc₂
    exact hs2ne (hsC _ (Subgroup.pow_mem _ (mem_zpowers s) 2) hs2C)
  have hzbar : orderOf (zL : L ⧸ center L) = 2 := orderOf_mk_eq_two zL hzL2 hzcen
  set φ : MulAut (L ⧸ center L) := normalizerAction L ⟨s, hsN⟩ with hφdef
  have hφx : ∀ x : L, ∃ y : L, (y : G) = s * (x : G) * s⁻¹ ∧
      φ (x : L ⧸ center L) = (y : L ⧸ center L) := fun x => by
    have hy : s * (x : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN (x : G)).1 x.2
    exact ⟨⟨_, hy⟩, rfl, normalizerAction_apply ⟨s, hsN⟩ x ⟨_, hy⟩ rfl⟩
  refine ⟨zL, c₂, hc₂, hsq.symm, hlc, hzL2, hzcen, hzbar, ?_, ?_⟩
  · refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | _ x =>
      obtain ⟨y, hy, hφy⟩ := hφx x
      obtain ⟨y₂, hy₂, hφy₂⟩ := hφx y
      rw [MulAut.mul_apply, hφy, hφy₂]
      have hcx : (x : G) * c₂ = c₂ * (x : G) := mem_centralizer_iff.mp hc₂ x x.2
      have hss : s * s = l₂ * c₂ := by rw [← sq]; exact hsq
      have hy₂' : (y₂ : G) = (l₂ * c₂) * (x : G) * (l₂ * c₂)⁻¹ := by
        rw [← hss, hy₂, hy]
        group
      have : y₂ = zL * x * zL⁻¹ := by
        apply Subtype.ext
        rw [hy₂']
        show _ = l₂ * (x : G) * l₂⁻¹
        calc (l₂ * c₂) * (x : G) * (l₂ * c₂)⁻¹ = l₂ * (c₂ * (x : G) * c₂⁻¹) * l₂⁻¹ := by group
          _ = l₂ * (x : G) * l₂⁻¹ := by rw [← hcx]; group
      rw [this]
      rfl
  · intro q hq hqodd
    obtain ⟨x, rfl, hxodd⟩ := exists_odd_lift hZ hqodd
    have hxz : Commute x zL :=
      commute_of_odd_of_commute_mk hZ hxodd (mem_centralizer_singleton_iff.1 hq)
    have hxz' : (x : G) * l₂ = l₂ * (x : G) := congrArg Subtype.val hxz.eq
    have hxc : (x : G) * c₂ = c₂ * (x : G) := mem_centralizer_iff.mp hc₂ x x.2
    have hxt : (x : G) * s ^ 2 = s ^ 2 * (x : G) := by
      rw [hsq]
      calc (x : G) * (l₂ * c₂) = (x * l₂) * c₂ := by group
        _ = (l₂ * x) * c₂ := by rw [hxz']
        _ = l₂ * (x * c₂) := by group
        _ = l₂ * (c₂ * x) := by rw [hxc]
        _ = l₂ * c₂ * x := by group
    have hxt' : (x : G)⁻¹ * s ^ 2 = s ^ 2 * (x : G)⁻¹ := by
      calc (x : G)⁻¹ * s ^ 2 = (x : G)⁻¹ * (s ^ 2 * x) * (x : G)⁻¹ := by group
        _ = (x : G)⁻¹ * (x * s ^ 2) * (x : G)⁻¹ := by rw [hxt]
        _ = s ^ 2 * (x : G)⁻¹ := by group
    have hxnorm : (x : G) ∈ normalizer (zpowers s : Set G) := by
      have h2 : (x : G) * s * (x : G)⁻¹ ∈ zpowers s := hsT _ hxt
      have h3 : (x : G)⁻¹ * s * (x : G) ∈ zpowers s := by
        simpa using hsT _ hxt'
      refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ h2 _
      · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
        have hyk : y = (x : G)⁻¹ * s ^ k * (x : G) := by
          rw [hk]; group
        have h4 := conj_zpow (a := (x : G)⁻¹) (b := s) (i := k)
        rw [hyk]
        simp only [inv_inv] at h4
        rw [← h4]
        exact Subgroup.zpow_mem _ h3 _
    have hxodd' : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
    have hcomm : (x : G) * s = s * (x : G) :=
      commute_of_odd_of_mem_normalizer (isPGroup_zpowers_of_orderOf_eq_four hs4) hxodd' hxnorm s
        (mem_zpowers s)
    have hxs : (x : G) = s * (x : G) * s⁻¹ := by
      calc (x : G) = (x : G) * s * s⁻¹ := by group
        _ = s * (x : G) * s⁻¹ := by rw [hcomm]
    exact normalizerAction_apply ⟨s, hsN⟩ x x hxs

end CFSG.EvenSporadicStandard.TwoHS
