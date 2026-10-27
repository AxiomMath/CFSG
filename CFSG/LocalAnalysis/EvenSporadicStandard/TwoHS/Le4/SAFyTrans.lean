module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyNorm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HIndex

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y : G} {S₀ : Subgroup G} {n : G}

namespace Sect7Hyps

variable (hH : Sect7Hyps G L f s y S₀ n)
include hH

theorem y_normalizes {l : G} (hl : l ∈ L) : y * l * y⁻¹ ∈ L :=
  (mem_normalizer_iff.1 (y_mem_normalizer hH.four hH.cent_eq) l).1 hl

theorem y_conj_zpow (i : ℤ) : y * f ^ i * y⁻¹ = (f ^ i)⁻¹ := by
  rw [← conj_zpow, hH.yf, inv_zpow]

theorem sq_mem_of_cent {a : G} (ha : a * f ^ 2 = f ^ 2 * a) : a * a ∈ L := by
  have haN : a ∈ (L ⊔ zpowers f) ⊔ zpowers y := by
    rw [← hH.cent_eq]; exact mem_centralizer_singleton_iff.2 ha
  rcases mem_or_exists_of_mem_sup_zpowers hH.yy (fun b hb => hH.conj_y_mem_f hb) haN with
    h | ⟨b, hb, rfl⟩
  · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (fun l hl => hH.comm_f hl) h
    have hc : l * f ^ i = f ^ i * l := ((show Commute l f from hH.comm_f hl).zpow_right i).eq
    have hff : f ^ i * f ^ i = (f ^ 2) ^ i := by
      rw [← (Commute.refl f).mul_zpow, ← sq]
    have e : l * f ^ i * (l * f ^ i) = l * l * (f ^ 2) ^ i := by
      calc l * f ^ i * (l * f ^ i) = l * (f ^ i * l) * f ^ i := by group
        _ = l * (l * f ^ i) * f ^ i := by rw [← hc]
        _ = l * l * (f ^ i * f ^ i) := by group
        _ = l * l * (f ^ 2) ^ i := by rw [hff]
    rw [e]
    exact L.mul_mem (L.mul_mem hl hl) (zpow_mem hH.sq_mem_L i)
  · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (fun l hl => hH.comm_f hl) hb
    have hl' : y * l * y⁻¹ ∈ L := hH.y_normalizes hl
    have hc : (y * l * y⁻¹) * f ^ i = f ^ i * (y * l * y⁻¹) :=
      ((show Commute (y * l * y⁻¹) f from hH.comm_f hl').zpow_right i).eq
    have e : l * f ^ i * y * (l * f ^ i * y) = l * (y * l * y⁻¹) := by
      calc l * f ^ i * y * (l * f ^ i * y)
          = l * f ^ i * (y * l * y⁻¹) * (y * f ^ i * y⁻¹) * (y * y) := by group
        _ = l * f ^ i * (y * l * y⁻¹) * (f ^ i)⁻¹ * 1 := by rw [hH.y_conj_zpow, hH.yy]
        _ = l * ((f ^ i * (y * l * y⁻¹)) * (f ^ i)⁻¹) := by group
        _ = l * (((y * l * y⁻¹) * f ^ i) * (f ^ i)⁻¹) := by rw [hc]
        _ = l * (y * l * y⁻¹) := by group
    rw [e]
    exact L.mul_mem hl hl'

theorem mem_L_of_order_three {a : G} (ha : a * f ^ 2 = f ^ 2 * a) (ha3 : orderOf a = 3) :
    a ∈ L := by
  have h1 := hH.sq_mem_of_cent ha
  have h3 : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have : a = (a * a)⁻¹ := by
    have : a * (a * a) = 1 := by simpa [pow_succ, mul_assoc] using h3
    exact (eq_inv_of_mul_eq_one_left this)
  rw [this]
  exact L.inv_mem h1

theorem L_data : Group.IsPerfect L ∧ Nat.card (center L) = 2 ∧
    IsSporadic (L ⧸ center L) .HS :=
  ⟨Group.isPerfect_def.2 hH.four.std.standard.1.1, hH.four.card_center, hH.quot⟩

theorem exists_conj_of_three (h3 : HSThreeClass) {a b : G} (ha : a * f ^ 2 = f ^ 2 * a)
    (ha3 : orderOf a = 3) (hb : b * f ^ 2 = f ^ 2 * b) (hb3 : orderOf b = 3) :
    ∃ g : G, g ∈ L ∧ g * a * g⁻¹ = b := by
  have haL := hH.mem_L_of_order_three ha ha3
  have hbL := hH.mem_L_of_order_three hb hb3
  obtain ⟨hP, hZ, hq⟩ := hH.L_data
  obtain ⟨g, hg⟩ := (h3 L hP hZ hq).1 ⟨a, haL⟩ ⟨b, hbL⟩
    (by rw [Subgroup.orderOf_mk]; exact ha3) (by rw [Subgroup.orderOf_mk]; exact hb3)
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem card_cent_le (h3 : HSThreeClass) {r : G} (hr : r ∈ L) (hr3 : orderOf r = 3) :
    Nat.card (centralizer ({f ^ 2, r} : Set G)) ≤ 2880 := by
  obtain ⟨hP, hZ, hq⟩ := hH.L_data
  set Hs : Subgroup G := centralizer ({f ^ 2, r} : Set G) with hHs
  set Ns : Subgroup G := centralizer ({f ^ 2} : Set G) with hNs
  have hHN : Hs ≤ Ns := by
    apply centralizer_le
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    simp [hx]
  have hLN : L ≤ Ns := by
    intro l hl
    rw [hNs, mem_centralizer_singleton_iff]
    exact hH.comm_t hl
  have hrel : L.relIndex Ns ≤ 4 :=
    relindex_le_four_of_inv hLN (fun l hl => hH.comm_f hl) hH.sq_mem_L hH.yy
      (y_mem_normalizer hH.four hH.cent_eq) hH.cent_eq hH.yf
  have hrel0 : L.relIndex Ns ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hidx : (L.subgroupOf Hs).index ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right hHN hrel0).trans hrel
  have hcard := Subgroup.card_mul_index (L.subgroupOf Hs)
  have hr' : orderOf (⟨r, hr⟩ : L) = 3 := by rw [Subgroup.orderOf_mk]; exact hr3
  have hC := (h3 L hP hZ hq).2 ⟨r, hr⟩ hr'
  have hmemL : ∀ x : ↥(L.subgroupOf Hs), ((x : Hs) : G) ∈ L := fun x =>
    Subgroup.mem_subgroupOf.1 x.2
  have hcomm : ∀ x : ↥(L.subgroupOf Hs),
      (⟨((x : Hs) : G), hmemL x⟩ : L) ∈ centralizer ({(⟨r, hr⟩ : L)} : Set L) := by
    intro x
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := mem_centralizer_iff.1 (x : Hs).2 r (by simp)
    exact this.symm
  let ψ : ↥(L.subgroupOf Hs) → ↥(centralizer ({(⟨r, hr⟩ : L)} : Set L)) := fun x =>
    ⟨_, hcomm x⟩
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 := congrArg (fun z : ↥(centralizer ({(⟨r, hr⟩ : L)} : Set L)) => ((z : L) : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hle := (Nat.card_le_card_of_injective ψ hψ).trans hC
  calc Nat.card Hs = Nat.card (L.subgroupOf Hs) * (L.subgroupOf Hs).index := hcard.symm
    _ ≤ 720 * 4 := Nat.mul_le_mul hle hidx
    _ = 2880 := by norm_num

theorem exists_three_commuting (hO : HSOuterThree) {w : G} (hww : w * w = 1)
    (hw : w * f ^ 2 = f ^ 2 * w) (hwf : w ∉ L ⊔ zpowers f) :
    ∃ r : G, r ∈ L ∧ orderOf r = 3 ∧ r * w = w * r := by
  have hwN : w ∈ (L ⊔ zpowers f) ⊔ zpowers y := by
    rw [← hH.cent_eq]; exact mem_centralizer_singleton_iff.2 hw
  rcases mem_or_exists_of_mem_sup_zpowers hH.yy (fun b hb => hH.conj_y_mem_f hb) hwN with
    h | ⟨b, hb, rfl⟩
  · exact absurd h hwf
  obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (fun l hl => hH.comm_f hl) hb
  have hc : l * f ^ i = f ^ i * l := ((show Commute l f from hH.comm_f hl).zpow_right i).eq
  set w₁ : G := l * y with hw₁
  have hw₁H : w₁ ∈ L ⊔ zpowers y :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (mem_zpowers y))
  have hw₁L : w₁ ∉ L := by
    intro h
    apply hH.y_not
    have : y = l⁻¹ * w₁ := by rw [hw₁]; group
    rw [this]
    exact Subgroup.mem_sup_left (L.mul_mem (L.inv_mem hl) h)
  have hweq : l * f ^ i * y = f ^ i * w₁ := by
    calc l * f ^ i * y = (f ^ i * l) * y := by rw [hc]
      _ = f ^ i * w₁ := by rw [hw₁]; group
  have hw₁f : w₁ * f ^ i * w₁⁻¹ = (f ^ i)⁻¹ := by
    calc w₁ * f ^ i * w₁⁻¹ = l * (y * f ^ i * y⁻¹) * l⁻¹ := by rw [hw₁]; group
      _ = l * (f ^ i)⁻¹ * l⁻¹ := by rw [hH.y_conj_zpow]
      _ = (f ^ i)⁻¹ := by
        have : l * (f ^ i)⁻¹ = (f ^ i)⁻¹ * l := (show Commute l (f ^ i) from hc).inv_right.eq
        rw [this]; group
  have hw₁w₁ : w₁ * w₁ = 1 := by
    have e : f ^ i * w₁ * (f ^ i * w₁) = f ^ i * (w₁ * f ^ i * w₁⁻¹) * (w₁ * w₁) := by group
    rw [hweq] at hww
    rw [hw₁f] at e
    calc w₁ * w₁ = f ^ i * (f ^ i)⁻¹ * (w₁ * w₁) := by group
      _ = 1 := by rw [← e]; exact hww
  have hcov := isHSCover_H1 hH.four hH.yy hH.y_not hH.cent_eq hH.quot
  obtain ⟨r, hrE, hr3, hrw⟩ := hO _ _ hcov ⟨w₁, hw₁H⟩ (Subtype.ext (by simpa using hw₁w₁))
    (by rw [Subgroup.mem_subgroupOf]; exact hw₁L)
  have hrL : (r : G) ∈ L := Subgroup.mem_subgroupOf.1 hrE
  have hrw' : (r : G) * w₁ = w₁ * (r : G) := congrArg Subtype.val hrw
  refine ⟨(r : G), hrL, by rw [Subgroup.orderOf_coe]; exact hr3, ?_⟩
  have hrf : (r : G) * f ^ i = f ^ i * (r : G) :=
    ((show Commute (r : G) f from hH.comm_f hrL).zpow_right i).eq
  rw [hweq]
  calc (r : G) * (f ^ i * w₁) = f ^ i * ((r : G) * w₁) := by rw [← mul_assoc, hrf, mul_assoc]
    _ = f ^ i * (w₁ * (r : G)) := by rw [hrw']
    _ = f ^ i * w₁ * (r : G) := by group

theorem dichotomy (hI : HSInvolutionClasses) {v : G} (hvL : v ∈ L) (hvv : v * v = 1)
    (hv1 : v ≠ 1) (hvt : v ≠ f ^ 2) :
    ((∃ g : G, v = g * f ^ 2 * g⁻¹) ∧ ¬ ∃ g : G, f ^ 2 * v = g * f ^ 2 * g⁻¹) ∨
    ((∃ g : G, f ^ 2 * v = g * f ^ 2 * g⁻¹) ∧ ¬ ∃ g : G, v = g * f ^ 2 * g⁻¹) := by
  obtain ⟨hP, hZ, hq⟩ := hH.L_data
  obtain ⟨u, hu, huu, hunc⟩ := hH.u
  obtain ⟨τ, hτZ, hτ⟩ := hH.four.exists_center_gen
  have hf2 : f ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hH.four.order] at this
    omega
  have hτ1 : τ ≠ 1 := fun h => hf2 (by rw [← hτ, h]; rfl)
  have hvnc : (⟨v, hvL⟩ : L) ∉ center L := by
    intro hc
    have hcent : v ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := Subgroup.mem_center_iff.1 hc ⟨l, hl⟩
      exact congrArg Subtype.val this
    rcases hH.four.eq_one_or_eq_sq hcent hvv with h | h
    · exact hv1 h
    · exact hvt h
  have hnot := hH.not_conj
  obtain ⟨g', hg'⟩ := hH.s_conj
  have hs2L : s ^ 2 ∈ L := by rw [← hu]; exact u.2
  have hcs : s ^ 2 * f ^ 2 = f ^ 2 * s ^ 2 := (hH.comm_t hs2L)
  obtain ⟨g, hg⟩ := hI L hP hZ hq τ hτZ hτ1 u ⟨v, hvL⟩ huu (Subtype.ext hvv) hunc hvnc
  have hgt : (g : G) * f ^ 2 = f ^ 2 * g := hH.comm_t g.2
  have hff : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact hH.f_pow_four
  have hvt' : v * f ^ 2 = f ^ 2 * v := hH.comm_t hvL
  rcases hg with hg | hg
  · left
    have hgv : (g : G) * s ^ 2 * (g : G)⁻¹ = v := by
      have := congrArg Subtype.val hg
      simpa [hu] using this
    refine ⟨⟨(g : G) * g', ?_⟩, ?_⟩
    · rw [← hgv, hg']; group
    · rintro ⟨h, hh⟩
      apply hnot
      refine ⟨(g : G)⁻¹ * h, ?_⟩
      calc s ^ 2 * f ^ 2 = f ^ 2 * s ^ 2 := hcs
        _ = (g : G)⁻¹ * (g * f ^ 2) * s ^ 2 := by group
        _ = (g : G)⁻¹ * (f ^ 2 * g) * s ^ 2 := by rw [hgt]
        _ = (g : G)⁻¹ * (f ^ 2 * ((g : G) * s ^ 2 * (g : G)⁻¹)) * g := by group
        _ = (g : G)⁻¹ * (f ^ 2 * v) * g := by rw [hgv]
        _ = (g : G)⁻¹ * (h * f ^ 2 * h⁻¹) * g := by rw [hh]
        _ = ((g : G)⁻¹ * h) * f ^ 2 * ((g : G)⁻¹ * h)⁻¹ := by group
  · right
    have hgv : (g : G) * s ^ 2 * (g : G)⁻¹ = v * f ^ 2 := by
      have := congrArg Subtype.val hg
      simpa [hu, hτ] using this
    refine ⟨⟨(g : G) * g', ?_⟩, ?_⟩
    · rw [← hvt', ← hgv, hg']; group
    · rintro ⟨h, hh⟩
      apply hnot
      refine ⟨(g : G)⁻¹ * h, ?_⟩
      calc s ^ 2 * f ^ 2 = (g : G)⁻¹ * (v * f ^ 2) * g * f ^ 2 := by rw [← hgv]; group
        _ = (g : G)⁻¹ * v * (f ^ 2 * g) * f ^ 2 := by group
        _ = (g : G)⁻¹ * v * (g * f ^ 2) * f ^ 2 := by rw [hgt]
        _ = (g : G)⁻¹ * v * g * (f ^ 2 * f ^ 2) := by group
        _ = (g : G)⁻¹ * v * g := by rw [hff]; group
        _ = (g : G)⁻¹ * (h * f ^ 2 * h⁻¹) * g := by rw [hh]
        _ = ((g : G)⁻¹ * h) * f ^ 2 * ((g : G)⁻¹ * h)⁻¹ := by group

end Sect7Hyps

end CFSG.EvenSporadicStandard.TwoHS
