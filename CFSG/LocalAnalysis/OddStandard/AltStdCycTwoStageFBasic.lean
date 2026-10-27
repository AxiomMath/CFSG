module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.OddStandard.AltStdBalSigma
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseTrick

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageF

open Subgroup AltStdBal AltStdSec

structure Inner (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z : G) : Prop where
  std : StandardSetting G L
  hn : 13 ≤ n
  iso : Nonempty (L ≃* alternatingGroup (Fin n))
  cyc : Cyc L Q z
  card : Nat.card Q = 2
  hE : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem Inner.hn8 (c : Inner G L Q n z) : 8 ≤ n := by
  have := c.hn
  omega

theorem Inner.le_cent (c : Inner G L Q n z) : L ≤ centralizer ({z} : Set G) :=
  AltStdCycTwo.le_cent_single c.std c.cyc

theorem Inner.decomp (c : Inner G L Q n z) {x : G} (hx : x ∈ centralizer ({z} : Set G)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : ∃ l ∈ L, x = l ∨ x = l * z := by
  obtain ⟨θ⟩ := c.iso
  exact AltStdCycTwo.exists_eq_of_two_pow c.std θ c.hn8 c.cyc c.card hx (c.hE hx) hk

theorem Inner.decomp_of_mul_self (c : Inner G L Q n z) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hx2 : x * x = 1) : ∃ l ∈ L, x = l ∨ x = l * z :=
  c.decomp hx (k := 1) (by rw [pow_one, sq]; exact hx2)

theorem Inner.decomp_of_mem {R : Subgroup G} (c : Inner G L Q n z)
    (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R) {x : G} (hx : x ∈ R) :
    ∃ l ∈ L, x = l ∨ x = l * z := by
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  exact c.decomp (hRC hx) (k := k) (congrArg Subtype.val hk)

theorem Inner.not_conj_mem (c : Inner G L Q n z) (g : G) : g * z * g⁻¹ ∉ L := by
  obtain ⟨θ⟩ := c.iso
  exact AltStdCycTwo.not_conj_mem_L c.std θ c.hn8 c.cyc c.card g

theorem Inner.z_not_mem (c : Inner G L Q n z) : z ∉ L := by
  simpa using c.not_conj_mem 1

theorem Inner.fusionSet_conj (c : Inner G L Q n z) {y l : G} (hy : y ∈ FusionSet L z)
    (hl : l ∈ L) : l * y * l⁻¹ ∈ FusionSet L z := by
  obtain ⟨hyL, hy2, g, hg⟩ := hy
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (c.le_cent hl)
  refine ⟨mul_mem (mul_mem hl hyL) (inv_mem hl), ?_, l * g, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy2
  · calc l * g * z * (l * g)⁻¹ = l * (g * z * g⁻¹) * l⁻¹ := by group
      _ = l * (z * y) * l⁻¹ := by rw [hg]
      _ = (l * z * l⁻¹) * (l * y * l⁻¹) := by group
      _ = z * (l * y * l⁻¹) := by
          have : l * z * l⁻¹ = z := by rw [hlz]; group
          rw [this]

theorem Inner.mem_conjSub_of_partner (c : Inner G L Q n z) {y g : G} (hy : y ∈ L)
    (hg : g * z * g⁻¹ = z * y) : y ∈ conjSub g L := by
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 (c.le_cent hy)
  have hzz := c.cyc.mul_self
  have hg' : z = g⁻¹ * (z * y) * g := by rw [← hg]; group
  have hwc : (g⁻¹ * z * g) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * z = g⁻¹ * z * g * (g⁻¹ * (z * y) * g) := by rw [← hg']
      _ = g⁻¹ * (z * z * y) * g := by group
      _ = g⁻¹ * y * g := by rw [hzz]; group
      _ = g⁻¹ * (z * y * z) * g := by
          have : z * y * z = y := by
            calc z * y * z = z * (y * z) := mul_assoc _ _ _
              _ = z * (z * y) := by rw [hyz]
              _ = (z * z) * y := (mul_assoc _ _ _).symm
              _ = y := by rw [hzz, one_mul]
          rw [this]
      _ = z * (g⁻¹ * z * g) := by
          calc g⁻¹ * (z * y * z) * g = (g⁻¹ * (z * y) * g) * (g⁻¹ * z * g) := by group
            _ = z * (g⁻¹ * z * g) := by rw [← hg']
  have hww : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  obtain ⟨l, hl, hwl⟩ := c.decomp_of_mul_self hwc hww
  rcases hwl with hwl | hwl
  · exfalso
    have := c.not_conj_mem g⁻¹
    rw [inv_inv] at this
    exact this (by rw [hwl]; exact hl)
  · rw [mem_conjSub_iff]
    have hl' : l = g⁻¹ * z * g * z := by
      calc l = l * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = g⁻¹ * z * g * z := by rw [hwl]
    have : g⁻¹ * y * g = l := by
      calc g⁻¹ * y * g = g⁻¹ * (z * (z * y)) * g := by
            rw [← mul_assoc z z y, hzz, one_mul]
        _ = (g⁻¹ * z * g) * (g⁻¹ * (z * y) * g) := by group
        _ = (g⁻¹ * z * g) * z := by rw [← hg']
        _ = l := hl'.symm
    rw [this]
    exact hl

theorem Inner.not_le_centralizer_of_sylow (c : Inner G L Q n z) (S : Sylow 2 G) :
    ¬ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  intro hSC
  have hzS : z ∈ (S : Subgroup G) :=
    mem_of_maximal c.cyc hSC S.isPGroup' (fun R' _ hp hSR' => S.3 hp hSR')
  have hzL := c.z_not_mem
  have hrel : (S ⊓ L : Subgroup G).relIndex S = 2 := by
    have hdvd : (S ⊓ L : Subgroup G).relIndex S ∣ 2 := by
      rw [relIndex_dvd_two_iff]
      refine ⟨z, hzS, fun b hb => ?_⟩
      obtain ⟨l, hl, hbl⟩ := c.decomp_of_mem hSC S.isPGroup' hb
      rcases hbl with rfl | rfl
      · exact Or.inr (Subgroup.mem_inf.2 ⟨hb, hl⟩)
      · refine Or.inl (Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hb hzS, ?_⟩)
        rw [mul_assoc, c.cyc.mul_self, mul_one]
        exact hl
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exfalso
      exact hzL (Subgroup.mem_inf.1 ((relIndex_eq_one.1 h1) hzS)).2
    · exact h2
  obtain ⟨g, hg⟩ := Solomon75.exists_conj_mem_of_thompson c.std.simple c.std.nonab S.isPGroup'
    S.not_dvd_index inf_le_left hrel hzS (fun hzU => hzL (Subgroup.mem_inf.1 hzU).2) c.cyc.order
  have := c.not_conj_mem g⁻¹
  rw [inv_inv] at this
  exact this (Subgroup.mem_inf.1 hg).2

theorem Inner.exists_common_involution_norm (c : Inner G L Q n z) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) :
    ∃ x y₀ : G, y₀ ∈ R ∧ y₀ ∈ L ∧ y₀ ≠ 1 ∧ y₀ * y₀ = 1 ∧ (∀ r ∈ R, r * y₀ = y₀ * r) ∧
      x * z * x⁻¹ = y₀ * z ∧ x⁻¹ * y₀ * x ∈ L ∧
      (∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧ (∀ r ∈ R, x⁻¹ * r * x ∈ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : z ∈ R := mem_of_maximal c.cyc hRC hR hRmax
  have hzz := c.cyc.mul_self
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hne : R ≠ (S : Subgroup G) := fun hRS' =>
    c.not_le_centralizer_of_sylow S (hRS' ▸ hRC)
  have hnil : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : R.subgroupOf (S : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hRS fun s hs => ?_
    have : (⟨s, hs⟩ : (S : Subgroup G)) ∈ R.subgroupOf (S : Subgroup G) := by
      rw [htop]
      trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G))
    (R.subgroupOf (S : Subgroup G)) hlt
  obtain ⟨⟨x, hxS⟩, hxN, hxH⟩ := IsConcreteLE.exists_of_lt hgrow
  have hxR : x ∉ R := fun hx => hxH hx
  have hconj : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.1 hxN ⟨r, hRS hr⟩).1 hr
  have hconj' : ∀ r ∈ R, x⁻¹ * r * x ∈ R := by
    intro r hr
    have hS' : x⁻¹ * r * x ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxS) (hRS hr)) hxS
    have h1 := (mem_normalizer_iff.1 hxN ⟨x⁻¹ * r * x, hS'⟩).2
    have h2 : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    have h3 : x * (x⁻¹ * r * x) * x⁻¹ ∈ R := by
      rw [h2]
      exact hr
    exact h1 h3
  set w := x * z * x⁻¹ with hw
  have hwR : w ∈ R := hconj z hzR
  have hwC : ∀ r ∈ R, r * w = w * r := by
    intro r hr
    have hzc : (x⁻¹ * r * x) * z = z * (x⁻¹ * r * x) :=
      mem_centralizer_singleton_iff.1 (hRC (hconj' r hr))
    calc r * w = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [hw]; group
      _ = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by rw [hzc]
      _ = w * r := by rw [hw]; group
  have hwne : w ≠ z := by
    intro hwz
    apply hxR
    have hxC : x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [← hw, hwz]
    have hle : R ⊔ Subgroup.zpowers x ≤ (S : Subgroup G) :=
      sup_le hRS (Subgroup.zpowers_le.2 hxS)
    have hp : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers x) := S.isPGroup'.to_le hle
    have hC : R ⊔ Subgroup.zpowers x ≤ centralizer ({z} : Set G) :=
      sup_le hRC (Subgroup.zpowers_le.2 hxC)
    have := hRmax _ hC hp le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨l, hl, hwl⟩ := c.decomp_of_mem hRC hR hwR
  rcases hwl with hwl | hwl
  · have hwL : w ∈ L := by
      rw [hwl]
      exact hl
    exact absurd hwL (c.not_conj_mem x)
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (c.le_cent hl)
  have hlw : l = w * z := by rw [hwl, mul_assoc, hzz, mul_one]
  have hww : w * w = 1 := by
    rw [hw]
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  refine ⟨x, l, hlw ▸ Subgroup.mul_mem _ hwR hzR, hl, ?_, ?_, ?_, hwl, ?_, hconj, hconj'⟩
  · intro hl1
    apply hwne
    rw [hwl, hl1, one_mul]
  · have h1 : (l * z) * (l * z) = 1 := by rw [← hwl]; exact hww
    calc l * l = (l * z) * (l * z) * (z * z)⁻¹ := by
          rw [hzz]
          calc l * l = l * (z * z) * l := by rw [hzz]; group
            _ = l * z * (z * l) := by group
            _ = (l * z) * (l * z) := by rw [← hlz]
            _ = _ := by group
      _ = 1 := by rw [h1, hzz]; group
  · intro r hr
    have hrz : r * z = z * r := mem_centralizer_singleton_iff.1 (hRC hr)
    rw [hlw]
    calc r * (w * z) = (r * w) * z := by group
      _ = (w * r) * z := by rw [hwC r hr]
      _ = w * (r * z) := by group
      _ = w * (z * r) := by rw [hrz]
      _ = (w * z) * r := by group
  ·
    set v := x⁻¹ * z * x with hv
    have hvz : v * z = z * v := by
      calc v * z = x⁻¹ * (z * (x * z * x⁻¹)) * x := by rw [hv]; group
        _ = x⁻¹ * ((x * z * x⁻¹) * z) * x := by rw [← hw, hwC z hzR]
        _ = z * v := by rw [hv]; group
    have hvv : v * v = 1 := by
      calc v * v = x⁻¹ * (z * z) * x := by rw [hv]; group
        _ = 1 := by rw [hzz]; group
    obtain ⟨l', hl', hvl⟩ := c.decomp_of_mul_self (mem_centralizer_singleton_iff.2 hvz) hvv
    rcases hvl with hvl | hvl
    · exfalso
      have := c.not_conj_mem x⁻¹
      rw [inv_inv] at this
      have hvL : v ∈ L := by
        rw [hvl]
        exact hl'
      exact this hvL
    have hl'z : l' * z = z * l' := mem_centralizer_singleton_iff.1 (c.le_cent hl')
    have : x⁻¹ * l * x = l' := by
      calc x⁻¹ * l * x = z * v := by rw [hlw, hw, hv]; group
        _ = z * (l' * z) := by rw [hvl]
        _ = (z * l') * z := by group
        _ = (l' * z) * z := by rw [← hl'z]
        _ = l' := by rw [mul_assoc, hzz, mul_one]
    rw [this]
    exact hl'

theorem Inner.fusionAll_of_section_fusion (c : Inner G L Q n z) {R : Subgroup G} {e₀ : G}
    (he₀R : e₀ ∈ R) (he₀2 : orderOf e₀ = 2) (he₀L : e₀ ∈ L)
    (hsec : ∀ b ∈ L, b ∈ centralizer (R : Set G) → orderOf b = 2 →
      ∃ h' ∈ centralizer (R : Set G), h' * z * h'⁻¹ = z * b)
    (hcov : ∀ y ∈ L, orderOf y = 2 → ∃ l ∈ L, (l * y * l⁻¹ ∈ centralizer (R : Set G) ∨
      ∃ b ∈ L, b ∈ centralizer (R : Set G) ∧ orderOf b = 2 ∧ b * e₀ ≠ 1 ∧ l * y * l⁻¹ = b * e₀))
    (he₀cov : ∃ l ∈ L, l * e₀ * l⁻¹ ∈ centralizer (R : Set G)) : FusionAll L z := by
  have hY : ∀ b ∈ L, b ∈ centralizer (R : Set G) → orderOf b = 2 → b ∈ FusionSet L z := by
    intro b hb hbC hb2
    obtain ⟨h', -, hh'⟩ := hsec b hb hbC hb2
    exact ⟨hb, hb2, h', hh'⟩
  have he₀Y : e₀ ∈ FusionSet L z := by
    obtain ⟨l, hl, hlC⟩ := he₀cov
    have hl2 : orderOf (l * e₀ * l⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact he₀2
    have := hY _ (mul_mem (mul_mem hl he₀L) (inv_mem hl)) hlC hl2
    have h2 := c.fusionSet_conj this (inv_mem hl)
    simpa [mul_assoc] using h2
  rw [fusionAll_iff]
  intro y hy hy2
  obtain ⟨l, hl, hcase⟩ := hcov y hy hy2
  have hlinv : ∀ w ∈ FusionSet L z, l * y * l⁻¹ = w → y ∈ FusionSet L z := by
    intro w hw hwy
    have := c.fusionSet_conj hw (inv_mem hl)
    rw [← hwy] at this
    simpa [mul_assoc] using this
  rcases hcase with hC | ⟨b, hb, hbC, hb2, hne, hby⟩
  · refine hlinv (l * y * l⁻¹) (hY _ (mul_mem (mul_mem hl hy) (inv_mem hl)) hC ?_) rfl
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hy2
  · exact hlinv (b * e₀) (mem_fusionSet_mul_of_section he₀Y hb hb2 he₀R hbC hne
      (hsec b hb hbC hb2)) hby

end CFSG.OddStandard.AltStdCycTwo.StageF
