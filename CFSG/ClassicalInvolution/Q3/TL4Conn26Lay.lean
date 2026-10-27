module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

section Act

omit [Finite G] in
theorem mem_normalizer_layerY (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) :
    y ∈ Subgroup.normalizer ((layerY Ω x : Subgroup G) : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr (layerY_conjSub_eq hcl hy)

noncomputable abbrev secAct (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) : MulAut (SecQuot Ω x) :=
  s26Act (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩

theorem comm_mem_oddCoreOf_coreAt {y : G} (hy : y ∈ Subgroup.centralizer ({x} : Set G))
    {M : Subgroup G} (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) {k : G} (hk : k ∈ coreAt x M) :
    ⁅y, k⁆ ∈ oddCoreOf (coreAt x M) := by
  have hyL : y ∈ Subgroup.normalizer (coreAt x M : Set G) := mem_normalizer_coreAt x hyN hy
  have h1 : y * k * y⁻¹ ∈ coreAt x M := (Subgroup.mem_normalizer_iff.mp hyL k).mp hk
  have hmem : ⁅y, k⁆ ∈ coreAt x M := by
    rw [commutatorElement_def]
    exact (coreAt x M).mul_mem h1 ((coreAt x M).inv_mem hk)
  exact inf_oddCoreOf_le (coreAt_le x M) ⟨hmem, hcomm k (coreAt_le x M hk)⟩

theorem mk_mem_oddCoreOf_secImg {M : Subgroup G} (hM : XMem Ω x M) (c : ↥(layerY Ω x))
    (hc : (c : G) ∈ oddCoreOf (coreAt x M)) :
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) c : SecQuot Ω x) ∈
      oddCoreOf (secImg Ω x M) := by
  have hLY : coreAt x M ≤ layerY Ω x := coreAt_le_layerY hM
  have h1 : c ∈ oddCoreOf ((coreAt x M).subgroupOf (layerY Ω x)) := by
    rw [oddCoreOf_subgroupOf hLY]
    exact hc
  have h2 := oddCoreOf_map_mk_of_odd (K := (coreAt x M).subgroupOf (layerY Ω x))
    (X := classicalInvolutionOddCore ↥(layerY Ω x)) (odd_natCard_inf odd_natCard_oddCore_layerY _)
  unfold secImg
  rw [h2]
  exact Subgroup.mem_map_of_mem _ h1

theorem secAct_mul_inv_mem (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) {M : Subgroup G} (hM : XMem Ω x M)
    (hyN : y ∈ Subgroup.normalizer (M : Set G)) (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ secImg Ω x M, secAct hcl hy kb * kb⁻¹ ∈ oddCoreOf (secImg Ω x M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hyY := mem_normalizer_layerY hcl hy
  have hkL : (k' : G) ∈ coreAt x M := Subgroup.mem_subgroupOf.mp hk'
  have hyk : y * (k' : G) * y⁻¹ ∈ layerY Ω x :=
    (Subgroup.mem_normalizer_iff.mp hyY (k' : G)).mp k'.2
  have e := s26Act_mk (layerY Ω x) ⟨y, hyY⟩ k' ⟨y * (k' : G) * y⁻¹, hyk⟩ rfl
  have hc : ((⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹ : ↥(layerY Ω x)) : G) = ⁅y, (k' : G)⁆ := by
    simp [commutatorElement_def]
  have h3 := mk_mem_oddCoreOf_secImg hM (⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹)
    (by rw [hc]; exact comm_mem_oddCoreOf_coreAt hy hyN hcomm hkL)
  change s26Act (layerY Ω x) ⟨y, hyY⟩ (QuotientGroup.mk k') * (QuotientGroup.mk k')⁻¹ ∈ _
  rw [e]
  simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h3

theorem mem_oddCoreOf_coreAt_of_mk_mem {M : Subgroup G} (hM : XMem Ω x M) (c : ↥(layerY Ω x))
    (hcM : (c : G) ∈ coreAt x M)
    (hc : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) c : SecQuot Ω x) ∈
      oddCoreOf (secImg Ω x M)) :
    (c : G) ∈ oddCoreOf (coreAt x M) := by
  have hLY : coreAt x M ≤ layerY Ω x := coreAt_le_layerY hM
  have h2 := oddCoreOf_map_mk_of_odd (K := (coreAt x M).subgroupOf (layerY Ω x))
    (X := classicalInvolutionOddCore ↥(layerY Ω x)) (odd_natCard_inf odd_natCard_oddCore_layerY _)
  unfold secImg at hc
  rw [h2] at hc
  obtain ⟨c', hc', hcc'⟩ := Subgroup.mem_map.mp hc
  rw [oddCoreOf_subgroupOf hLY] at hc'
  have hc'L : (c' : G) ∈ oddCoreOf (coreAt x M) := Subgroup.mem_subgroupOf.mp hc'
  have hdiv : c'⁻¹ * c ∈ classicalInvolutionOddCore ↥(layerY Ω x) := QuotientGroup.eq.mp hcc'
  have hmem : (c' : G)⁻¹ * c ∈ coreAt x M ⊓ oddCoreOf (layerY Ω x) := by
    refine ⟨(coreAt x M).mul_mem ((coreAt x M).inv_mem (mem_oddCoreOf_iff.mp hc'L).1) hcM,
      mem_oddCoreOf_iff.mpr ⟨(layerY Ω x).mul_mem ((layerY Ω x).inv_mem c'.2) c.2, ?_⟩⟩
    convert hdiv using 1
  have h3 := inf_oddCoreOf_le hLY hmem
  have : (c : G) = (c' : G) * ((c' : G)⁻¹ * c) := by group
  rw [this]
  exact (oddCoreOf (coreAt x M)).mul_mem hc'L h3

end Act

section Fixed

theorem exists_fixed_lift_sec (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (hy2 : y * y = 1) (u : SecQuot Ω x)
    (hu : secAct hcl hy u = u) :
    ∃ w : ↥(layerY Ω x), y * (w : G) * y⁻¹ = w ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w : SecQuot Ω x) = u := by
  classical
  have hyY := mem_normalizer_layerY hcl hy
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hyk : y * (w₀ : G) * y⁻¹ ∈ layerY Ω x :=
    (Subgroup.mem_normalizer_iff.mp hyY (w₀ : G)).mp w₀.2
  have e := s26Act_mk (layerY Ω x) ⟨y, hyY⟩ w₀ ⟨y * (w₀ : G) * y⁻¹, hyk⟩ rfl
  have h1 : ((⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(layerY Ω x)) : SecQuot Ω x) =
      (w₀ : SecQuot Ω x) := e.symm.trans hu
  have h2 : (⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(layerY Ω x))⁻¹ * w₀ ∈
      classicalInvolutionOddCore ↥(layerY Ω x) := QuotientGroup.eq.mp h1
  set N : Subgroup G := oddCoreOf (layerY Ω x) with hN
  have hx : ∀ b ∈ Subgroup.zpowers y, (w₀ : G)⁻¹ * (b * (w₀ : G) * b⁻¹) ∈ N := by
    intro b hb
    rcases Balance.Bootstrap.mem_zpowers_involution hy2 hb with hb1 | hb1
    · rw [hb1]
      simp
    · rw [hb1]
      have h3 : (y * (w₀ : G) * y⁻¹)⁻¹ * (w₀ : G) ∈ N := by
        refine mem_oddCoreOf_iff.mpr ⟨(layerY Ω x).mul_mem ((layerY Ω x).inv_mem hyk) w₀.2, ?_⟩
        convert h2 using 1
      have := N.inv_mem h3
      simpa [mul_assoc] using this
  have hAN : ∀ b ∈ Subgroup.zpowers y, ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
    intro b hb n hn
    have hbc : b ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.zpowers_le.mpr hy) hb
    have := mem_normalizer_oddCore_of_mem_normalizer (mem_normalizer_layerY hcl hbc)
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow hy2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨n, hnN, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup hA2
    (oddCoreOf_odd_natCard _) hAN hx
  have hnY : n ∈ layerY Ω x := (mem_oddCoreOf_iff.mp hnN).1
  refine ⟨⟨(w₀ : G) * n, (layerY Ω x).mul_mem w₀.2 hnY⟩, hfix y (Subgroup.mem_zpowers y), ?_⟩
  apply QuotientGroup.eq.mpr
  have hn' := (mem_oddCoreOf_iff.mp hnN).2
  have hE : (⟨(w₀ : G) * n, (layerY Ω x).mul_mem w₀.2 hnY⟩ : ↥(layerY Ω x))⁻¹ * w₀ =
      (⟨n, hnY⟩ : ↥(layerY Ω x))⁻¹ := by
    apply Subtype.ext
    simp
  rw [hE]
  exact (classicalInvolutionOddCore ↥(layerY Ω x)).inv_mem hn'

variable (Ω x) in
@[expose] noncomputable def secImage (H : Subgroup G) : Subgroup (SecQuot Ω x) :=
  (H.subgroupOf (layerY Ω x)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))

theorem mem_secImage_of_fixed (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (hy2 : y * y = 1) {H : Subgroup G}
    (hCy : Subgroup.centralizer ({y} : Set G) ≤ H) (u : SecQuot Ω x)
    (hu : secAct hcl hy u = u) : u ∈ secImage Ω x H := by
  obtain ⟨w, hw, rfl⟩ := exists_fixed_lift_sec hcl hy hy2 u hu
  refine ⟨w, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  apply hCy
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (w : G) * y = (y * (w : G) * y⁻¹) * y := by rw [hw]
    _ = y * (w : G) := by group

omit [Finite G] in
theorem layerY_le_of_closure {H : Subgroup G} (hO : oddCoreOf (layerY Ω x) ≤ H)
    (S : Set (SecQuot Ω x)) (hS : S ⊆ (secImage Ω x H : Set (SecQuot Ω x)))
    (hgen : Subgroup.closure S = ⊤) : layerY Ω x ≤ H := by
  intro w hw
  have hmem : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))
      (⟨w, hw⟩ : ↥(layerY Ω x)) : SecQuot Ω x) ∈ secImage Ω x H := by
    have h1 : Subgroup.closure S ≤ secImage Ω x H := (Subgroup.closure_le _).mpr hS
    rw [hgen] at h1
    exact h1 (Subgroup.mem_top _)
  obtain ⟨h, hh, hhw⟩ := hmem
  have h2 : h⁻¹ * ⟨w, hw⟩ ∈ classicalInvolutionOddCore ↥(layerY Ω x) := QuotientGroup.eq.mp hhw
  have h3 : (h : G)⁻¹ * w ∈ oddCoreOf (layerY Ω x) :=
    mem_oddCoreOf_iff.mpr ⟨(layerY Ω x).mul_mem ((layerY Ω x).inv_mem h.2) hw,
      by convert h2 using 1⟩
  have hhH : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
  have : w = (h : G) * ((h : G)⁻¹ * w) := by group
  rw [this]
  exact H.mul_mem hhH (hO h3)

end Fixed

omit [Finite G] in
theorem mk_mem_center_secQuot {w : G} (hw : w ∈ layerY Ω x) (hwx : w = x) :
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨w, hw⟩ : SecQuot Ω x) ∈
      Subgroup.center (SecQuot Ω x) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hg : (g' : G) ∈ Subgroup.centralizer ({x} : Set G) := layerY_le_centralizer g'.2
  have hcz : (g' : G) * w = w * g' := by
    rw [hwx]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hc2 : g' * (⟨w, hw⟩ : ↥(layerY Ω x)) = ⟨w, hw⟩ * g' := Subtype.ext hcz
  change QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) g' * _ =
    _ * QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) g'
  rw [← map_mul, ← map_mul, hc2]

end CFSG.ClassicalInvolution.Q3.TL4
