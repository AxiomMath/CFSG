module

public import CFSG.ClassicalInvolution.Asc77.AscCX1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Abs

variable {G : Type} [Group G] [Finite G] {Y : Subgroup G}

theorem mk_ne_one_of_involution {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    (QuotientGroup.mk ⟨z, hzY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : orderOf (⟨⟨z, hzY⟩, h⟩ : ↥(classicalInvolutionOddCore ↥Y)) ∣
      Nat.card (classicalInvolutionOddCore ↥Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at hdvd
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥Y))
    (even_iff_two_dvd.mpr hdvd)

theorem conj_ne_one_of_center_eq_bot {M : Type} [Group M] (hcen : Subgroup.center M = ⊥)
    {w : M} (hw : w ≠ 1) : MulAut.conj w ≠ 1 := by
  intro h
  apply hw
  have hwc : w ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut M => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * w = w * g * w⁻¹ * w := by rw [h1]
      _ = w * g := by group
  rwa [hcen, Subgroup.mem_bot] at hwc

theorem mem_zStarOf_of_layerAut_eq_conj {d z : G} {H : Subgroup G}
    (hHY : ∀ h ∈ H, conjSub h Y = Y) (hHd : ∀ h ∈ H, h * d = d * h) (hzH : z ∈ H)
    (hdY : conjSub d Y = Y) (hzY : z ∈ Y)
    (hcen : Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) = ⊥)
    (hd : ∀ y, C25Y.layerAut Y hdY y =
      QuotientGroup.mk ⟨z, hzY⟩ * y * (QuotientGroup.mk ⟨z, hzY⟩)⁻¹) :
    z ∈ zStarOf H := by
  rw [C25W.mem_zStarOf_iff]
  refine ⟨hzH, fun y hy => ?_⟩
  have hyi : y⁻¹ ∈ H := H.inv_mem hy
  set w := y⁻¹ * z * y⁻¹⁻¹ with hw
  have hwY : w ∈ Y := by
    have h1 : w ∈ conjSub y⁻¹ Y := Generic.conj_mem_conjSub hzY
    rwa [hHY _ hyi] at h1
  set α := C25Y.layerAut Y (hHY _ hyi) with hα
  set δ := C25Y.layerAut Y hdY with hδ
  have hαz : α (QuotientGroup.mk ⟨z, hzY⟩) = QuotientGroup.mk ⟨w, hwY⟩ := by
    rw [hα, C25Y.layerAut_mk]
    rfl
  have hcomm : ∀ u, α (δ u) = δ (α u) := by
    intro u
    refine QuotientGroup.induction_on u fun u => ?_
    rw [hα, hδ, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub]
    have hyd : y⁻¹ * d = d * y⁻¹ := hHd _ hyi
    calc y⁻¹ * (d * (u : G) * d⁻¹) * y⁻¹⁻¹ = (y⁻¹ * d) * (u : G) * (y⁻¹ * d)⁻¹ := by group
      _ = (d * y⁻¹) * (u : G) * (d * y⁻¹)⁻¹ := by rw [hyd]
      _ = d * (y⁻¹ * (u : G) * y⁻¹⁻¹) * d⁻¹ := by group
  have hwz : (QuotientGroup.mk ⟨w, hwY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) =
      QuotientGroup.mk ⟨z, hzY⟩ := by
    set zb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk ⟨z, hzY⟩ with hzbdef
    set wb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk ⟨w, hwY⟩ with hwbdef
    have hc : zb⁻¹ * wb ∈ Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) := by
      rw [Subgroup.mem_center_iff]
      intro v
      obtain ⟨u, rfl⟩ := α.surjective v
      have h1 : α (δ u) = wb * α u * wb⁻¹ := by
        rw [hd u, map_mul, map_mul, map_inv, hαz]
      rw [hcomm u, hd (α u)] at h1
      have h2 : wb⁻¹ * zb * α u = α u * (wb⁻¹ * zb) := by
        calc wb⁻¹ * zb * α u = wb⁻¹ * (zb * α u * zb⁻¹) * zb := by group
          _ = wb⁻¹ * (wb * α u * wb⁻¹) * zb := by rw [h1]
          _ = α u * (wb⁻¹ * zb) := by group
      calc α u * (zb⁻¹ * wb) = (wb⁻¹ * zb)⁻¹ * ((wb⁻¹ * zb) * α u) * (zb⁻¹ * wb) := by group
        _ = (wb⁻¹ * zb)⁻¹ * (α u * (wb⁻¹ * zb)) * (zb⁻¹ * wb) := by rw [← h2]
        _ = zb⁻¹ * wb * α u := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc wb = zb * (zb⁻¹ * wb) := by group
      _ = zb := by rw [hc, mul_one]
  have hO : z⁻¹ * w ∈ oddCoreOf Y := by
    rw [QuotientGroup.eq] at hwz
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem hwz, ?_⟩
    simp
  have hmem : z⁻¹ * w ∈ H := by
    refine H.mul_mem (H.inv_mem hzH) ?_
    rw [hw]
    exact H.mul_mem (H.mul_mem hyi hzH) (H.inv_mem hyi)
  have h3 := CX.mem_oddCore_of_mem_oddCoreOf hHY (c := ⟨z⁻¹ * w, hmem⟩) hO
  have e : z⁻¹ * y⁻¹ * z * y = z⁻¹ * w := by rw [hw]; group
  rw [e]
  exact Subgroup.mem_map.mpr ⟨_, h3, rfl⟩

theorem le_trivialOnQuot_of_layerAut_trivial {F : Subgroup G} (hFY : ∀ e ∈ F, conjSub e Y = Y)
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut Y (hFY e he) y = y) :
    F ≤ trivialOnQuot Y := by
  intro e he
  have hY := hFY e he
  refine ⟨mem_normalizer_iff_conjSub_eq.mpr hY, fun x hx => ?_⟩
  have h1 := htriv e he (QuotientGroup.mk ⟨x, hx⟩)
  rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
  have h2 := (inferInstance : (classicalInvolutionOddCore ↥Y).Normal).conj_mem _
    ((classicalInvolutionOddCore _).inv_mem h1) ⟨x, hx⟩
  refine Subgroup.mem_map.mpr ⟨_, h2, ?_⟩
  simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, C25Y.coe_conjOnSub,
    commutatorElement_def]
  group

theorem not_mem_zStarOf_of_layerAut_trivial {z : G} {F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hFY : ∀ e ∈ F, conjSub e Y = Y) (hzF : z ∈ Subgroup.centralizer (F : Set G)) (hzY : z ∈ Y)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) = ⊥)
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut Y (hFY e he) y = y) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
  classical
  intro hz
  set N := classicalInvolutionOddCore ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set C := Subgroup.centralizer (F : Set G) with hC
  have hFY' := le_trivialOnQuot_of_layerAut_trivial hFY htriv
  obtain ⟨-, hzc⟩ := (C25W.mem_zStarOf_iff C).mp hz
  set M : Subgroup (↥Y ⧸ N) :=
    ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y).map π with hM
  have hcover : ∀ x : ↥Y, ∃ h : ↥Y, (h : G) ∈ C ∧ π h = π x := by
    intro x
    obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hF2 hFY' x.2
    refine ⟨⟨h, hh.1⟩, hh.2, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨h, hh.1⟩ : ↥Y)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n, hxhn]
      group
    rw [e]
    exact hn'
  have hMnorm : M.Normal := by
    refine ⟨fun m hm y => ?_⟩
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    refine Subgroup.mem_map.mpr ⟨h * m₀ * h⁻¹, ?_, by simp [hπ]⟩
    rw [Subgroup.mem_subgroupOf] at hm₀ ⊢
    obtain ⟨hmO, hmY, hmC⟩ := hm₀
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (h : G) * m₀ * (h : G)⁻¹ ∈ conjSub (h : G) (oddCoreOf C) :=
        Generic.conj_mem_conjSub hmO
      rwa [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem hhC] at h1
    · exact (h * m₀ * h⁻¹).2
    · exact C.mul_mem (C.mul_mem hhC hmC) (C.inv_mem hhC)
  have hModd : Odd (Nat.card M) := by
    have hO : Odd (Nat.card (oddCoreOf C)) := by
      unfold oddCoreOf
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥C
    have h1 : Nat.card M ∣ Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) ∣ Nat.card (oddCoreOf C) := by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx).1
    exact Odd.of_dvd_nat hO (h1.trans h2)
  have hMbot : M = ⊥ := by
    have h1 : M ≤ classicalInvolutionOddCore (↥Y ⧸ N) :=
      le_sSup (show M ∈ {K : Subgroup (↥Y ⧸ N) | K.Normal ∧ Odd (Nat.card K)} from
        ⟨hMnorm, hModd⟩)
    have h2 : classicalInvolutionOddCore (↥Y ⧸ N) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
    rw [h2] at h1
    exact le_bot_iff.mp h1
  have hzcen : π ⟨z, hzY⟩ ∈ Subgroup.center (↥Y ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    have hcom : (⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h ∈
        (oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      refine ⟨by simpa using hzc (h : G) hhC, SetLike.coe_mem _, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hzF) (C.inv_mem hhC)) hzF) hhC
    have h1 : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) = 1 := by
      have : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) ∈ M := Subgroup.mem_map_of_mem _ hcom
      rwa [hMbot, Subgroup.mem_bot] at this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π h * π ⟨z, hzY⟩ =
          π h * π ⟨z, hzY⟩ * ((π ⟨z, hzY⟩)⁻¹ * (π h)⁻¹ * π ⟨z, hzY⟩ * π h) := by
            rw [h1, mul_one]
      _ = π ⟨z, hzY⟩ * π h := by group
  rw [hcen, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzcen
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : orderOf (⟨⟨z, hzY⟩, hzcen⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at hdvd
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)


theorem not_mem_zStarOf_of_fix_of_normalizes {Y F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hFY : ∀ e ∈ F, conjSub e Y = Y) {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1)
    {x : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hfix : ∀ e (he : e ∈ F), C25Y.layerAut Y (hFY e he) x = x)
    (hxz : x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹ ≠ QuotientGroup.mk ⟨z, hzY⟩)
    (hxzc : (x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹) * QuotientGroup.mk ⟨z, hzY⟩ =
      QuotientGroup.mk ⟨z, hzY⟩ * (x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹)) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
  classical
  intro hz
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  set C := Subgroup.centralizer (F : Set G) with hC
  have hOodd : Odd (Nat.card (oddCoreOf Y)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hAN : ∀ a ∈ F, ∀ n ∈ oddCoreOf Y, a * n * a⁻¹ ∈ oddCoreOf Y := by
    intro a ha n hn
    have h1 : a * n * a⁻¹ ∈ conjSub a (oddCoreOf Y) := Generic.conj_mem_conjSub hn
    rwa [← Thompson.oddCoreOf_conjSub_eq, hFY a ha] at h1
  have hx : ∀ a ∈ F, (x₀ : G)⁻¹ * (a * x₀ * a⁻¹) ∈ oddCoreOf Y := by
    intro a ha
    have h1 := hfix a ha
    rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem h1, ?_⟩
    simp [C25Y.coe_conjOnSub, mul_assoc]
  obtain ⟨n, hn, hfixn⟩ := exists_fixed_mem_coset_of_isPGroup hF2 hOodd hAN hx
  have hnY : n ∈ Y := Subgroup.map_subtype_le _ hn
  have hx₁Y : (x₀ : G) * n ∈ Y := Y.mul_mem x₀.2 hnY
  have hx₁C : (x₀ : G) * n ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro e he
    have := hfixn e he
    calc e * ((x₀ : G) * n) = e * ((x₀ : G) * n) * e⁻¹ * e := by group
      _ = (x₀ : G) * n * e := by rw [this]
  have hx₁bar : (QuotientGroup.mk (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y) :
      ↥Y ⧸ classicalInvolutionOddCore ↥Y) = QuotientGroup.mk x₀ := by
    rw [QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y)⁻¹ * x₀ = n'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n]
      group
    rw [e]
    exact (classicalInvolutionOddCore ↥Y).inv_mem hn'
  have hc := ((C25W.mem_zStarOf_iff C).mp hz).2 ((x₀ : G) * n)⁻¹ (C.inv_mem hx₁C)
  set c : G := z⁻¹ * ((x₀ : G) * n)⁻¹⁻¹ * z * ((x₀ : G) * n)⁻¹ with hcdef
  have hcY : c ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem hzY) (Y.inv_mem (Y.inv_mem hx₁Y))) hzY)
      (Y.inv_mem hx₁Y)
  have hcodd : Odd (orderOf c) := by
    obtain ⟨c', hc', hc'c⟩ := Subgroup.mem_map.mp hc
    have h1 : orderOf c' ∣ Nat.card (classicalInvolutionOddCore ↥C) := by
      have := orderOf_dvd_natCard (⟨c', hc'⟩ : ↥(classicalInvolutionOddCore ↥C))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf c = orderOf c' := by
      rw [← hc'c, Subgroup.subtype_apply, Subgroup.orderOf_coe]
    rw [h2]
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥C) h1
  set zb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk ⟨z, hzY⟩ with hzb
  set xb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk x₀ with hxb
  have hπc : (QuotientGroup.mk ⟨c, hcY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) =
      zb⁻¹ * (xb * zb * xb⁻¹) := by
    have e1 : (⟨c, hcY⟩ : ↥Y) = (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨(x₀ : G) * n, hx₁Y⟩ * ⟨z, hzY⟩ *
        (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y)⁻¹ := by
      apply Subtype.ext
      simp [hcdef]
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hx₁bar, ← hzb]
    group
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul]
    have : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
    rw [this, QuotientGroup.mk_one]
  have hzi : zb⁻¹ = zb := by
    calc zb⁻¹ = zb⁻¹ * (zb * zb) := by rw [hzb2, mul_one]
      _ = zb := by group
  have hw2 : (xb * zb * xb⁻¹) * (xb * zb * xb⁻¹) = 1 := by
    calc (xb * zb * xb⁻¹) * (xb * zb * xb⁻¹) = xb * (zb * zb) * xb⁻¹ := by group
      _ = 1 := by rw [hzb2]; group
  have hord : orderOf (zb⁻¹ * (xb * zb * xb⁻¹)) = 2 := by
    rw [hzi]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc zb * (xb * zb * xb⁻¹) * (zb * (xb * zb * xb⁻¹)) =
            zb * ((xb * zb * xb⁻¹) * zb) * (xb * zb * xb⁻¹) := by group
        _ = zb * (zb * (xb * zb * xb⁻¹)) * (xb * zb * xb⁻¹) := by rw [hxzc]
        _ = (zb * zb) * ((xb * zb * xb⁻¹) * (xb * zb * xb⁻¹)) := by group
        _ = 1 := by rw [hzb2, hw2, one_mul]
    · intro h1
      apply hxz
      calc xb * zb * xb⁻¹ = zb⁻¹ * (zb * (xb * zb * xb⁻¹)) := by group
        _ = zb := by rw [h1, mul_one, hzi]
  have hdvd : orderOf (QuotientGroup.mk ⟨c, hcY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ∣
      orderOf (⟨c, hcY⟩ : ↥Y) :=
    orderOf_map_dvd (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) _
  rw [hπc, hord, Subgroup.orderOf_mk] at hdvd
  exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr hdvd)


end Abs

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
