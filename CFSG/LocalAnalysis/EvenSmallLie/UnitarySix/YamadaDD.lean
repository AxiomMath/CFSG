module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDC4
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mem_comm_mod [Finite G] {p : ℕ} [Fact p.Prime] {P M N : Subgroup G}
    (hP : IsPGroup p P) (hNP : N ≤ P) (hM : P ≤ normalizer (M : Set G))
    (hN : P ≤ normalizer (N : Set G)) {n₀ : G} (hn₀N : n₀ ∈ N) (hn₀M : n₀ ∉ M) :
    ∃ n ∈ N, n ∉ M ∧ ∀ c ∈ P, c * n * c⁻¹ * n⁻¹ ∈ M := by
  set M' := M.subgroupOf P with hM'
  set N' := N.subgroupOf P with hN'
  have hM'n : M'.Normal := ⟨fun m hm g => by
    rw [hM', mem_subgroupOf] at hm ⊢
    exact (mem_normalizer_iff.mp (hM g.2) m).mp hm⟩
  have hN'n : N'.Normal := ⟨fun m hm g => by
    rw [hN', mem_subgroupOf] at hm ⊢
    exact (mem_normalizer_iff.mp (hN g.2) m).mp hm⟩
  have hQ : IsPGroup p (P ⧸ M') := hP.to_quotient M'
  have : Group.IsNilpotent (P ⧸ M') := hQ.isNilpotent
  set N'' := N'.map (QuotientGroup.mk' M') with hN''
  have hN''n : N''.Normal := hN'n.map _ (QuotientGroup.mk'_surjective M')
  have hne : N'' ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk' M' ⟨n₀, hNP hn₀N⟩ : P ⧸ M') ∈ N'' :=
      ⟨⟨n₀, hNP hn₀N⟩, hn₀N, rfl⟩
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hM',
      mem_subgroupOf] at hmem
    exact hn₀M hmem
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  obtain ⟨⟨n, hnP⟩, hnN, hnx⟩ := (mem_inf.mp x.2).1
  refine ⟨n, hnN, ?_, fun c hc => ?_⟩
  · intro hnM
    apply hx1
    apply Subtype.ext
    rw [← hnx, QuotientGroup.mk'_apply, OneMemClass.coe_one, QuotientGroup.eq_one_iff, hM',
      mem_subgroupOf]
    exact hnM
  · have hxZ := (mem_inf.mp x.2).2
    have hcomm := (mem_center_iff.mp hxZ) (QuotientGroup.mk' M' ⟨c, hc⟩)
    rw [← hnx, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hcomm
    rw [hM', mem_subgroupOf] at hcomm
    have e : ((⟨c, hc⟩ * ⟨n, hnP⟩ : P)⁻¹ * (⟨n, hnP⟩ * ⟨c, hc⟩ : P) : P) =
        (⟨n, hnP⟩ : P)⁻¹ * (⟨c, hc⟩ : P)⁻¹ * ⟨n, hnP⟩ * ⟨c, hc⟩ := by group
    rw [e] at hcomm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm
    have : c * n * c⁻¹ * n⁻¹ = (c * n) * (n⁻¹ * c⁻¹ * n * c)⁻¹ * (c * n)⁻¹ := by group
    rw [this]
    exact (mem_normalizer_iff.mp (hM (mul_mem hc hnP)) _).mp (inv_mem hcomm)

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem e_comm_t : d.e * d.t = d.t * d.e := h.comm_of_mem_L h.e_mem_L

theorem e_mem_X₄ [Finite G] : d.e ∈ d.X₄ :=
  CA₄_le_X₄ ⟨h.e_cent_A₄, h.L_le_H h.e_mem_L⟩

theorem withT_A₄_le_cent_e : d.withT d.A₄ ≤ centralizer ({d.e} : Set G) := by
  refine sup_le (fun a ha => ?_) ?_
  · rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp h.e_cent_A₄ a ha)
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    exact h.e_comm_t.symm

theorem withT_A₄_le_T₃ : d.withT d.A₄ ≤ d.withT d.A₃ := sup_le_sup_right h.A₄_le_A₃ _

theorem withT_A₄_le_D [Finite G] : d.withT d.A₄ ≤ d.D :=
  le_inf (h.withT_A₄_le_T₃.trans h.T₃_le_C₄) h.withT_A₄_le_cent_e

theorem D_inf_H [Finite G] : d.D ⊓ d.H = d.withT d.A₄ := by
  apply le_antisymm
  · rintro x ⟨⟨hxC, hxe⟩, hxH⟩
    have hxT : x ∈ d.withT d.A₃ := by rw [← h.C₄_inf_H]; exact ⟨hxC, hxH⟩
    rw [h.mem_withT_iff h.A₄_le_L]
    have hte : d.t ∈ centralizer ({d.e} : Set G) :=
      mem_centralizer_singleton_iff.mpr h.e_comm_t.symm
    rcases (h.mem_withT_iff h.A₃_le_L).mp hxT with hx | hx
    · exact Or.inl (h.A₃_cent_e ⟨hx, hxe⟩)
    · exact Or.inr (h.A₃_cent_e ⟨hx, mul_mem hxe hte⟩)
  · exact le_inf h.withT_A₄_le_D (h.withT_le_H h.A₄_le_L)

theorem exists_D_conj [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ c ∈ d.D, c⁻¹ * d.t * c = a * d.t := by
  obtain ⟨c₀, hc₀, hc₀t⟩ := h.exists_C₄_conj ha
  set T : Set G := {c | c ∈ d.C₄ ∧ c⁻¹ * d.t * c = a * d.t} with hT
  have hTimg : T = (fun y => y * c₀) '' ((d.C₄ ⊓ d.H : Subgroup G) : Set G) := by
    ext c
    constructor
    · rintro ⟨hc, hct⟩
      refine ⟨c * c₀⁻¹, mem_inf.mpr ⟨mul_mem hc (inv_mem hc₀), ?_⟩, by group⟩
      change c * c₀⁻¹ ∈ centralizer ({d.t} : Set G)
      rw [mem_centralizer_singleton_iff]
      calc c * c₀⁻¹ * d.t = c * (c₀⁻¹ * d.t * c₀) * c₀⁻¹ := by group
        _ = c * (c⁻¹ * d.t * c) * c₀⁻¹ := by rw [hc₀t, hct]
        _ = d.t * (c * c₀⁻¹) := by group
    · rintro ⟨y, ⟨hyC, hyH⟩, rfl⟩
      refine ⟨mul_mem hyC hc₀, ?_⟩
      have hyt : y * d.t = d.t * y := mem_centralizer_singleton_iff.mp hyH
      calc (y * c₀)⁻¹ * d.t * (y * c₀) = c₀⁻¹ * (y⁻¹ * (d.t * y)) * c₀ := by group
        _ = c₀⁻¹ * d.t * c₀ := by rw [← hyt]; group
        _ = a * d.t := hc₀t
  have hcard : T.ncard = 2 ^ 13 := by
    rw [hTimg, Set.ncard_image_of_injective _ (mul_left_injective c₀), ← Nat.card_coe_set_eq]
    change Nat.card (d.C₄ ⊓ d.H : Subgroup G) = _
    rw [h.C₄_inf_H, h.card_withT h.A₃_le_L, h.card_A₃]
    norm_num
  have hTe : ∀ c ∈ T, d.e * c * d.e⁻¹ ∈ T := by
    rintro c ⟨hc, hct⟩
    refine ⟨(mem_normalizer_iff.mp (X₄_le_normalizer_C₄ h.e_mem_X₄) c).mp hc, ?_⟩
    have het : d.e⁻¹ * d.t * d.e = d.t := by
      calc d.e⁻¹ * d.t * d.e = d.e⁻¹ * (d.t * d.e) := by group
        _ = d.e⁻¹ * (d.e * d.t) := by rw [h.e_comm_t]
        _ = d.t := by group
    have hea : d.e * a * d.e⁻¹ = a := by
      rw [← mem_centralizer_iff.mp h.e_cent_A₄ a ha]; group
    calc (d.e * c * d.e⁻¹)⁻¹ * d.t * (d.e * c * d.e⁻¹)
        = d.e * (c⁻¹ * (d.e⁻¹ * d.t * d.e) * c) * d.e⁻¹ := by group
      _ = d.e * (a * d.t) * d.e⁻¹ := by rw [het, hct]
      _ = (d.e * a * d.e⁻¹) * (d.e * d.t * d.e⁻¹) := by group
      _ = a * d.t := by rw [hea, h.e_comm_t]; group
  obtain ⟨c, ⟨hc, hct⟩, hce⟩ := exists_conj_fixed h.e_pow hTe (by rw [hcard]; norm_num)
  refine ⟨c, mem_inf.mpr ⟨hc, ?_⟩, hct⟩
  rw [mem_centralizer_singleton_iff]
  calc c * d.e = d.e * c * d.e⁻¹ * d.e := by rw [hce]
    _ = d.e * c := by group

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

omit h in
theorem D_le_C₄ : d.D ≤ d.C₄ := inf_le_left

omit h in
theorem D_le_cent_e : d.D ≤ centralizer ({d.e} : Set G) := inf_le_right

omit h in
theorem D_le_X₄ : d.D ≤ d.X₄ := inf_le_left.trans C₄_le_X₄

theorem D_le_cent_A₄ [Finite G] : d.D ≤ centralizer (d.A₄ : Set G) :=
  inf_le_left.trans h.C₄_le_cent

theorem card_D [Finite G] : Nat.card d.D = 2 ^ 9 := by
  rw [card_eq_of_crossed_onto h.t_sq h.D_le_cent_A₄ (fun c hc => h.crossed_X₄ (D_le_X₄ hc))
    (fun a ha => ?_)]
  · change Nat.card (d.D ⊓ d.H : Subgroup G) * _ = _
    rw [h.D_inf_H, h.card_withT h.A₄_le_L, h.card_A₄]
    norm_num
  · obtain ⟨c, hc, hct⟩ := h.exists_D_conj ha
    exact ⟨c, hc, by rw [hct, mul_assoc, h.t_sq, mul_one]⟩

theorem NLA₃_le_X₄ [Finite G] : d.NLA₃ ≤ d.X₄ := fun _ hn =>
  mem_normalizer_sup (h.NLA₃_le hn) (mem_normalizer_zpowers (h.comm_of_mem_L hn.1))

theorem comm_A₃_C₄ [Finite G] {a c : G} (ha : a ∈ d.A₃) (hc : c ∈ d.C₄) :
    c * a * c⁻¹ * a⁻¹ ∈ d.withT d.A₄ := by
  have hA4n : ∀ x ∈ d.X₄, ∀ y ∈ d.withT d.A₄, x * y * x⁻¹ ∈ d.withT d.A₄ :=
    fun x hx y hy => (mem_normalizer_iff.mp hx y).mp hy
  let B : Subgroup G :=
    { carrier := {b | b ∈ d.A₃ ∧ ∀ c ∈ d.C₄, c * b * c⁻¹ * b⁻¹ ∈ d.withT d.A₄}
      one_mem' := ⟨one_mem _, fun c _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
        refine ⟨mul_mem hx hy, fun c hc => ?_⟩
        have e : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
            (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact mul_mem (hxc c hc) (hA4n x (h.T₃_le_X₄ (le_withT _ hx)) _ (hyc c hc))
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨inv_mem hx, fun c hc => ?_⟩
        have e : c * x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x := by group
        rw [e]
        have hx' : x⁻¹ ∈ d.X₄ := inv_mem (h.T₃_le_X₄ (le_withT _ hx))
        simpa using hA4n _ hx' _ (inv_mem (hxc c hc)) }
  have hA4B : d.A₄ ≤ B := fun b hb => ⟨h.A₄_le_A₃ hb, fun c hc => by
    rw [← mem_centralizer_iff.mp (h.C₄_le_cent hc) b hb]
    simp⟩
  have hBN : d.NLA₃ ≤ normalizer (B : Set G) := by
    intro n hn
    have hnX := h.NLA₃_le_X₄ hn
    apply mem_normalizer_of_conj_mem
    rintro b ⟨hb, hbc⟩
    refine ⟨(mem_normalizer_iff.mp hn.2 b).mp hb, fun c hc => ?_⟩
    have hc' : n⁻¹ * c * n ∈ d.C₄ := by
      have := (mem_normalizer_iff.mp (X₄_le_normalizer_C₄ (inv_mem hnX)) c).mp hc
      simpa using this
    have e : c * (n * b * n⁻¹) * c⁻¹ * (n * b * n⁻¹)⁻¹ =
        n * ((n⁻¹ * c * n) * b * (n⁻¹ * c * n)⁻¹ * b⁻¹) * n⁻¹ := by group
    rw [e]
    exact hA4n n hnX _ (hbc _ hc')
  rcases h.A₃_irred B hA4B (fun b hb => hb.1) hBN with hB | hB
  · exfalso
    obtain ⟨a₀, ha₀, ha₀4⟩ : ∃ a₀ ∈ d.A₃, a₀ ∉ d.A₄ := by
      by_contra hno
      push Not at hno
      have hle : d.A₃ ≤ d.A₄ := fun x hx => hno x hx
      have := Subgroup.card_le_of_le hle
      rw [h.card_A₃, h.card_A₄] at this
      norm_num at this
    have hT4 : d.withT d.A₄ ≤ d.withT d.A₃ := h.withT_A₄_le_T₃
    have ha₀T : a₀ ∉ d.withT d.A₄ := by
      intro hm
      rcases (h.mem_withT_iff h.A₄_le_L).mp hm with hm | hm
      · exact ha₀4 hm
      · apply h.t_not_mem_L
        have : d.t = a₀⁻¹ * (a₀ * d.t) := by group
        rw [this]
        exact mul_mem (inv_mem (h.A₃_le_L ha₀)) (h.A₄_le_L hm)
    obtain ⟨n, hnT, hnM, hnc⟩ := exists_mem_comm_mod (p := 2) (P := d.C₄) (M := d.withT d.A₄)
      (N := d.withT d.A₃) (isPGroup_oTwo _) h.T₃_le_C₄ (fun x hx => C₄_le_X₄ hx)
      (fun x hx => h.X₄_le_normalizer_T₃ (C₄_le_X₄ hx)) (le_withT _ ha₀) ha₀T
    rcases (h.mem_withT_iff h.A₃_le_L).mp hnT with hn | hn
    · have : n ∈ B := ⟨hn, hnc⟩
      rw [hB] at this
      exact hnM (le_withT _ this)
    · have hnB : n * d.t ∈ B := by
        refine ⟨hn, fun c hc => ?_⟩
        have hcX := C₄_le_X₄ hc
        have hct : c * d.t * c⁻¹ * d.t⁻¹ ∈ d.withT d.A₄ := by
          have := h.crossed_X₄ (inv_mem hcX)
          rw [h.t_inv]
          simpa using le_withT _ this
        have e : c * (n * d.t) * c⁻¹ * (n * d.t)⁻¹ =
            (c * n * c⁻¹ * n⁻¹) * (n * (c * d.t * c⁻¹ * d.t⁻¹) * n⁻¹) := by group
        rw [e]
        exact mul_mem (hnc c hc) (hA4n n (h.T₃_le_X₄ hnT) _ hct)
      rw [hB] at hnB
      apply hnM
      rw [h.mem_withT_iff h.A₄_le_L]
      exact Or.inr hnB
  · have : a ∈ B := by rw [hB]; exact ha
    exact this.2 c hc

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem withT_A₄_le_cent_A₃ : d.withT d.A₄ ≤ centralizer (d.A₃ : Set G) := by
  refine sup_le ?_ ?_
  · rw [← le_centralizer_iff]
    exact h.A₃_le_cent_A₄
  · rw [zpowers_le, mem_centralizer_iff]
    intro a ha
    exact h.comm_of_mem_L (h.A₃_le_L ha)

theorem D_le_cent_A₃ [Finite G] : d.D ≤ centralizer (d.A₃ : Set G) := by
  intro x hx
  have hxe : x * d.e = d.e * x := mem_centralizer_singleton_iff.mp (D_le_cent_e hx)
  have hle : ⁅d.A₃, zpowers d.e⁆ ⊔ d.A₄ ≤ centralizer ({x} : Set G) := by
    refine sup_le ?_ (fun a ha => ?_)
    · rw [commutator_le]
      intro a ha g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      have hgx : d.e ^ k * x = x * d.e ^ k := (Commute.zpow_left (show Commute d.e x from
        hxe.symm) k)
      set w := x * a * x⁻¹ * a⁻¹ with hwdef
      have hw : w ∈ d.withT d.A₄ := h.comm_A₃_C₄ ha (D_le_C₄ hx)
      have hgw : d.e ^ k * w = w * d.e ^ k := by
        have := mem_centralizer_singleton_iff.mp (h.withT_A₄_le_cent_e hw)
        exact (Commute.zpow_left (show Commute d.e w from this.symm) k)
      have hcA : ⁅a, d.e ^ k⁆ ∈ d.A₃ := by
        rw [commutatorElement_def, show a * d.e ^ k * a⁻¹ * (d.e ^ k)⁻¹ =
          a * (d.e ^ k * a⁻¹ * (d.e ^ k)⁻¹) by group]
        refine mul_mem ha ?_
        have hen : d.e ^ k ∈ normalizer (d.A₃ : Set G) := zpow_mem h.e_norm_A₃ k
        exact (mem_normalizer_iff.mp hen _).mp (inv_mem ha)
      have hwc : w * ⁅a, d.e ^ k⁆ = ⁅a, d.e ^ k⁆ * w :=
        (mem_centralizer_iff.mp (h.withT_A₄_le_cent_A₃ hw) _ hcA).symm
      have hxa : x * a * x⁻¹ = w * a := by rw [hwdef]; group
      have hxg : x * d.e ^ k * x⁻¹ = d.e ^ k := by rw [← hgx]; group
      rw [mem_centralizer_singleton_iff]
      have key : x * ⁅a, d.e ^ k⁆ * x⁻¹ = ⁅a, d.e ^ k⁆ := by
        calc x * ⁅a, d.e ^ k⁆ * x⁻¹ = (x * a * x⁻¹) * (x * d.e ^ k * x⁻¹) *
              (x * a * x⁻¹)⁻¹ * (x * d.e ^ k * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
          _ = (w * a) * d.e ^ k * (w * a)⁻¹ * (d.e ^ k)⁻¹ := by rw [hxa, hxg]
          _ = w * ⁅a, d.e ^ k⁆ * (d.e ^ k * w⁻¹ * (d.e ^ k)⁻¹) := by
              rw [commutatorElement_def]; group
          _ = w * ⁅a, d.e ^ k⁆ * w⁻¹ := by
              rw [show d.e ^ k * w⁻¹ * (d.e ^ k)⁻¹ = w⁻¹ by
                calc d.e ^ k * w⁻¹ * (d.e ^ k)⁻¹ = (d.e ^ k * w * (d.e ^ k)⁻¹)⁻¹ := by group
                  _ = w⁻¹ := by rw [hgw]; group]
          _ = ⁅a, d.e ^ k⁆ := by rw [hwc]; group
      calc ⁅a, d.e ^ k⁆ * x = x * ⁅a, d.e ^ k⁆ * x⁻¹ * x := by rw [key]
        _ = x * ⁅a, d.e ^ k⁆ := by group
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp (h.D_le_cent_A₄ hx) a ha
  rw [mem_centralizer_iff]
  intro a ha
  exact (mem_centralizer_singleton_iff.mp (hle (h.A₃_le_comm_e ha)))

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem exists_mul_A₃_D [Finite G] {c : G} (hc : c ∈ d.C₄) :
    ∃ a ∈ d.A₃, ∃ x ∈ d.D, c = a * x := by
  obtain ⟨x, hx, hxt⟩ := h.exists_D_conj (h.crossed_X₄ (C₄_le_X₄ hc))
  have hcx : c * x⁻¹ ∈ d.withT d.A₃ := by
    rw [← h.C₄_inf_H]
    refine mem_inf.mpr ⟨mul_mem hc (inv_mem (D_le_C₄ hx)), ?_⟩
    change c * x⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have e1 : c⁻¹ * d.t * c = x⁻¹ * d.t * x := by
      rw [hxt, mul_assoc _ d.t d.t, h.t_sq, mul_one]
    calc c * x⁻¹ * d.t = c * (x⁻¹ * d.t * x) * x⁻¹ := by group
      _ = c * (c⁻¹ * d.t * c) * x⁻¹ := by rw [e1]
      _ = d.t * (c * x⁻¹) := by group
  rcases (h.mem_withT_iff h.A₃_le_L).mp hcx with ha | ha
  · exact ⟨c * x⁻¹, ha, x, hx, by group⟩
  · refine ⟨c * x⁻¹ * d.t, ha, d.t * x, mul_mem (h.withT_A₄_le_D (t_mem_withT _)) hx, ?_⟩
    rw [show c * x⁻¹ * d.t * (d.t * x) = c * x⁻¹ * (d.t * d.t) * x by group, h.t_sq]
    group

theorem D_eq [Finite G] : d.D = d.C₄ ⊓ centralizer (d.A₃ : Set G) := by
  refine le_antisymm (le_inf D_le_C₄ h.D_le_cent_A₃) ?_
  intro c hcm
  obtain ⟨hc, hcA⟩ := mem_inf.mp hcm
  obtain ⟨a, ha, x, hx, rfl⟩ := h.exists_mul_A₃_D hc
  have haA : a ∈ centralizer (d.A₃ : Set G) := by
    have := mul_mem hcA (inv_mem (h.D_le_cent_A₃ hx))
    simpa using this
  have ha4 : a ∈ d.A₄ := h.center_A₃ ⟨ha, haA⟩
  exact mul_mem (h.withT_A₄_le_D (le_withT _ ha4)) hx

theorem X₄_le_normalizer_A₃ [Finite G] : d.X₄ ≤ normalizer (d.A₃ : Set G) := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := h.X₄_factor hx
  have hy : x * c⁻¹ ∈ normalizer (d.A₃ : Set G) :=
    h.NHA₄_le ⟨h.X₄_le_normalizer_A₄ (mul_mem hx (inv_mem (C₄_le_X₄ hc))), hxc⟩
  have hc' : c ∈ normalizer (d.A₃ : Set G) := by
    obtain ⟨a, ha, y, hy', rfl⟩ := h.exists_mul_A₃_D hc
    exact mul_mem (Subgroup.le_normalizer ha) (centralizer_le_normalizer _ (h.D_le_cent_A₃ hy'))
  have e : x = (x * c⁻¹) * c := by group
  rw [e]
  exact mul_mem hy hc'

theorem X₄_le_normalizer_D [Finite G] : d.X₄ ≤ normalizer (d.D : Set G) := by
  intro x hx
  rw [h.D_eq]
  exact mem_normalizer_of_conj_mem fun y hy =>
    ⟨(mem_normalizer_iff.mp (X₄_le_normalizer_C₄ hx) y).mp hy.1,
      conj_mem_centralizer (h.X₄_le_normalizer_A₃ hx) hy.2⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
