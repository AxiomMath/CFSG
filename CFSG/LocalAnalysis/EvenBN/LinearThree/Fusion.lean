module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelFacts
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionExists

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard (sg)
open CFSG.OddStandard.Seitz77 (Datum)
open scoped commutatorElement

namespace Radicals

variable {G : Type*} [Group G] {V V₁ V₂ : Subgroup G} {q : ℕ}

theorem exists_noncomm [Finite G] (hR : Radicals V V₁ V₂ q) (hq : 2 ≤ q) :
    ∃ x ∈ V, ∃ y ∈ V, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ centralizer (V : Set G) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
    hcon y hy x hx
  have h1 : V ⊓ centralizer (V : Set G) = V := inf_eq_left.mpr hle
  have h2 : Nat.card V₁ ≤ Nat.card ↥(V ⊓ centralizer (V : Set G)) := by
    rw [h1]
    exact Subgroup.card_le_of_le hR.le₁
  rw [hR.card_center, hR.card₁] at h2
  nlinarith

theorem mul_self_of_mem_center (hR : Radicals V V₁ V₂ q) {u : G}
    (hu : u ∈ V ⊓ centralizer (V : Set G)) : u * u = 1 := by
  rw [← hR.inf_eq] at hu
  rw [← sq]
  exact hR.elem₁.2 u hu.1

end Radicals

section Adj

variable {G : Type*} [Group G] {A : Subgroup G} {q : ℕ} {V₁ V₂ : Subgroup G}

theorem sup_adj_eq (d : Datum A) (hR : Radicals d.V V₁ V₂ q) :
    (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) = d.V ⊔ zpowers d.t := by
  rw [sup_sup_sup_comm, sup_idem, hR.sup_eq]

variable [Finite G]

theorem commutator_adjV_le (d : Datum A) :
    ⁅d.V ⊔ zpowers d.t, d.V ⊔ zpowers d.t⁆ ≤ d.V := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact d.commutator_mem_V (d.adj_le_P le_rfl hg₁) ((d.mem_adj_iff le_rfl).mp hg₁)
    ((d.mem_adj_iff le_rfl).mp hg₂)

theorem commutator_adjV_ne_bot (d : Datum A) (hq : 2 ≤ q) (hR : Radicals d.V V₁ V₂ q) :
    ⁅d.V ⊔ zpowers d.t, d.V ⊔ zpowers d.t⁆ ≠ ⊥ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hR.exists_noncomm hq
  intro hbot
  have h1 := Subgroup.commutator_mem_commutator (mem_sup_left hx : x ∈ d.V ⊔ zpowers d.t)
    (mem_sup_left hy : y ∈ d.V ⊔ zpowers d.t)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact hxy h1

end Adj

namespace Facts

section Gamma

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {q : ℕ} {V₁ V₂ : Subgroup G}

theorem t_not_mem_A (F : FusionFacts A q) (d : Datum A) : d.t ∉ A :=
  (SylowSetting.of_datum d).t_not_mem F

theorem map_conj_adj (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    {n : G} (hn : n ∈ normalizer (d.P : Set G)) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom = V₁ ⊔ zpowers d.t ∨
      (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom = V₂ ⊔ zpowers d.t := by
  have hd := SylowSetting.of_datum d
  obtain ⟨hEP, hE, hcard⟩ := hd.adj_properties F hR hW
  refine hd.elem_eq_adj F hq hR ?_ (isElemAbelian_map _ hE) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hn x).mp (hEP hx)
  · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hcard]

theorem central_mem_adj (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    {z : G} (hz : z ∈ d.P ⊓ centralizer (d.P : Set G)) (hz2 : z * z = 1) {W : Subgroup G}
    (hW : W = V₁ ∨ W = V₂) : z ∈ W ⊔ zpowers d.t := by
  have hd := SylowSetting.of_datum d
  obtain ⟨hEP, hE, hcard⟩ := hd.adj_properties F hR hW
  have hF : IsElemAbelian 2 ((W ⊔ zpowers d.t) ⊔ zpowers z) :=
    OddStandard.Seitz77.isElemAbelian_sup_zpowers hE
      (fun e he => mem_centralizer_iff.mp hz.2 e (hEP he)) hz2
  have hFP : (W ⊔ zpowers d.t) ⊔ zpowers z ≤ d.P := sup_le hEP ((zpowers_le).mpr hz.1)
  have hFcard : Nat.card ↥((W ⊔ zpowers d.t) ⊔ zpowers z) ≤ 2 * q ^ 2 :=
    hd.card_elem_le F hq hR hFP hF
  have hFeq : W ⊔ zpowers d.t = (W ⊔ zpowers d.t) ⊔ zpowers z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hFcard)
  rw [hFeq]
  exact mem_sup_right (mem_zpowers z)

theorem central_mem_U_or (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    {z : G} (hz : z ∈ d.P ⊓ centralizer (d.P : Set G)) (hz2 : z * z = 1) :
    z ∈ d.V ⊓ centralizer (d.V : Set G) ∨ z * d.t ∈ d.V ⊓ centralizer (d.V : Set G) := by
  have h1 := (d.mem_adj_iff hR.le₁).mp (Facts.central_mem_adj F d hq hR hz hz2 (Or.inl rfl))
  have h2 := (d.mem_adj_iff hR.le₂).mp (Facts.central_mem_adj F d hq hR hz hz2 (Or.inr rfl))
  rw [← hR.inf_eq]
  have ht : ∀ a b : G, a ∈ d.V → b ∈ d.V → a⁻¹ * b = d.t → False := fun a b ha hb h =>
    Facts.t_not_mem_A F d (h ▸ mul_mem (inv_mem ha) hb).2
  rcases h1 with a1 | a1 <;> rcases h2 with a2 | a2
  · exact Or.inl ⟨a1, a2⟩
  · exact (ht z (z * d.t) (hR.le₁ a1) (hR.le₂ a2) (by group)).elim
  · exact (ht z (z * d.t) (hR.le₂ a2) (hR.le₁ a1) (by group)).elim
  · exact Or.inr ⟨a1, a2⟩

theorem conj_mem_adjV (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    {n : G} (hn : n ∈ normalizer (d.P : Set G)) {y : G} (hy : y ∈ d.V ⊔ zpowers d.t) :
    n * y * n⁻¹ ∈ d.V ⊔ zpowers d.t := by
  rw [← sup_adj_eq d hR] at hy ⊢
  have hmap : ((V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)).map (MulAut.conj n).toMonoidHom ≤
      (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases Facts.map_conj_adj F d hq hR hn (Or.inl rfl) with h | h <;> rw [h]
      exacts [le_sup_left, le_sup_right]
    · rcases Facts.map_conj_adj F d hq hR hn (Or.inr rfl) with h | h <;> rw [h]
      exacts [le_sup_left, le_sup_right]
  have := hmap (Subgroup.mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

theorem not_isConj_of_mem (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    {x : G} (hxA : x ∈ A) : ¬ IsConj d.t x := by
  intro hconj
  have hnorm : ∀ n ∈ normalizer (d.P : Set G), ∀ y ∈ ⁅d.V ⊔ zpowers d.t, d.V ⊔ zpowers d.t⁆,
      n * y * n⁻¹ ∈ ⁅d.V ⊔ zpowers d.t, d.V ⊔ zpowers d.t⁆ := fun n hn y hy =>
    OddStandard.Seitz77.conj_mem_commutator (fun z hz => Facts.conj_mem_adjV F d hq hR hn hz) hy
  obtain ⟨w, hwD, hw2, hwc⟩ := OddStandard.Seitz77.exists_involution_normal_center
    d.hP.isPGroup ((commutator_adjV_le d).trans inf_le_left)
    (fun p hp y hy => hnorm p (le_normalizer hp) y hy) (commutator_adjV_ne_bot d (by omega) hR)
  have hwV : w ∈ d.V := commutator_adjV_le d hwD
  have hxo : orderOf x = 2 := by
    rw [OddStandard.Seitz77.orderOf_eq_of_isConj hconj]
    exact d.sector.t_order
  obtain ⟨a, haA, hax⟩ := F.invol_conj x hxA w hwV.2 hxo hw2
  have hwconj : IsConj d.t w := hconj.trans (isConj_iff.mpr ⟨a, hax⟩)
  have hwz : w ∈ d.P ⊓ centralizer (d.P : Set G) :=
    ⟨hwV.1, mem_centralizer_iff.mpr fun p hp => hwc p hp⟩
  obtain ⟨n, hn, hnt⟩ := OddStandard.Seitz77.exists_normalizer_conj_of_mem_center
    d.P_isSylow_centralizer hwz hwconj
  have htD := hnorm n hn w hwD
  have : n * w * n⁻¹ = d.t := by rw [← hnt]; group
  rw [this] at htD
  exact Facts.t_not_mem_A F d (commutator_adjV_le d htD).2

end Gamma

section Alpha

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {q : ℕ} {V₁ V₂ : Subgroup G}

theorem exists_involution_U (d : Datum A) (hq : 2 ≤ q) (hR : Radicals d.V V₁ V₂ q) :
    ∃ w ∈ d.V ⊓ centralizer (d.V : Set G), orderOf w = 2 ∧ ∀ p ∈ d.P, p * w = w * p := by
  refine OddStandard.Seitz77.exists_involution_normal_center d.hP.isPGroup
    (fun x hx => hx.1.1) ?_ ?_
  · intro x hx n hn
    refine ⟨d.conj_mem_V hx hn.1, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ d.V := d.conj_mem_V (d.P.inv_mem hx) hv
    have h := mem_centralizer_iff.mp hn.2 _ hv'
    calc v * (x * n * x⁻¹) = x * ((x⁻¹ * v * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * v * x)) * x⁻¹ := by
        rw [show x⁻¹ * v * x = x⁻¹ * v * x⁻¹⁻¹ by group, h]
      _ = x * n * x⁻¹ * v := by group
  · intro hbot
    have h1 := hR.card_center
    rw [hbot, Subgroup.card_bot] at h1
    omega

theorem alpha_of_exists_mul_t (F : FusionFacts A q) (d : Datum A) (hq : 2 ≤ q)
    (hR : Radicals d.V V₁ V₂ q) {v : G} (hvA : v ∈ A) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvt : IsConj d.t (v * d.t)) : d.Alpha := by
  obtain ⟨w, hwU, hwo, hwc⟩ := exists_involution_U d hq hR
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  obtain ⟨a, ha, hav⟩ := F.invol_conj v hvA w hwU.1.2 hvo hwo
  have hct : a * d.t * a⁻¹ = d.t := by rw [d.comm_t_of_mem ha, mul_inv_cancel_right]
  have hconj : IsConj d.t (w * d.t) := by
    refine hvt.trans (isConj_iff.mpr ⟨a, ?_⟩)
    calc a * (v * d.t) * a⁻¹ = (a * v * a⁻¹) * (a * d.t * a⁻¹) := by group
      _ = w * d.t := by rw [hav, hct]
  refine ⟨w * d.t, ⟨d.P.mul_mem hwU.1.1 d.t_mem_P, mem_centralizer_iff.mpr fun p hp => ?_⟩,
    hconj, ?_⟩
  · calc p * (w * d.t) = (p * w) * d.t := by group
      _ = (w * p) * d.t := by rw [hwc p hp]
      _ = w * (p * d.t) := by group
      _ = w * (d.t * p) := by rw [d.P_comm_t hp]
      _ = w * d.t * p := by group
  · intro h
    have hw1 : w = 1 := by
      have := congrArg (· * d.t) h
      simpa [mul_assoc, d.t_mul_self] using this
    rw [hw1, orderOf_one] at hwo
    exact absurd hwo (by norm_num)

theorem alpha (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hZ : ∃ g : G, g⁻¹ * d.t * g ≠ d.t ∧ g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g)) :
    d.Alpha := by
  obtain ⟨t', ht'P, hc, hne⟩ := OddStandard.Seitz77.Facts.exists_conj_mem_P d hZ
  have ht'2 := d.mul_self_of_isConj hc
  have ht'N : t' ∈ normalizer (A : Set G) := d.P_le_normalizer ht'P
  have hq2 : 2 ≤ q := by omega
  by_cases hAK : t' ∈ A ⊔ centralizer (A : Set G)
  · rcases (SylowSetting.of_datum d).mem_V_or F ht'P hAK ht'2 with h | h
    · exact (Facts.not_isConj_of_mem F d hq hR h.2 hc).elim
    · have hct : t' * d.t = d.t * t' := d.P_comm_t ht'P
      refine Facts.alpha_of_exists_mul_t F d hq2 hR h.2 ?_ ?_ ?_
      · calc t' * d.t * (t' * d.t) = t' * (d.t * t') * d.t := by group
          _ = t' * (t' * d.t) * d.t := by rw [hct]
          _ = (t' * t') * (d.t * d.t) := by group
          _ = 1 := by rw [ht'2, d.t_mul_self, one_mul]
      · intro h1
        apply hne
        calc t' = t' * d.t * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
          _ = d.t := by rw [h1, one_mul]
      · rwa [mul_assoc, d.t_mul_self, mul_one]
  · obtain ⟨D, hDle, hD, c, hcD, hco⟩ := F.outer_perfect t' ht'N ht'2 hAK
    have hc2 : c * c = 1 := by rw [← sq, ← hco, pow_orderOf_eq_one]
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hco
      exact absurd hco (by norm_num)
    obtain ⟨b, hb, hbt⟩ := F.outer_fuse t' ht'N ht'2 hAK c (hDle hcD) hc2
    obtain ⟨g, hgt⟩ : ∃ g : G, g * t' * g⁻¹ = d.t := by
      obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hc
      exact ⟨c₀⁻¹, by rw [← hc₀]; group⟩
    let D₁ : Subgroup G := D.map (MulAut.conj g).toMonoidHom
    have hD₁N : D₁ ≤ normalizer (A : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y * t' = t' * y := mem_centralizer_singleton_iff.mp (hDle hy).2
      have : g * y * g⁻¹ ∈ centralizer ({d.t} : Set G) := by
        rw [mem_centralizer_singleton_iff, ← hgt]
        calc g * y * g⁻¹ * (g * t' * g⁻¹) = g * (y * t') * g⁻¹ := by group
          _ = g * (t' * y) * g⁻¹ := by rw [hy']
          _ = g * t' * g⁻¹ * (g * y * g⁻¹) := by group
      exact (OddStandard.centralizer_t_facts d.sector).1 this
    have hD₁ : ⁅D₁, D₁⁆ = D₁ := by rw [← Subgroup.map_commutator, hD]
    have hc₁ : g * c * g⁻¹ ∈ D₁ := ⟨c, hcD, by simp [MulAut.conj_apply]⟩
    have hc₁2 : (g * c * g⁻¹) * (g * c * g⁻¹) = 1 := by
      calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
        _ = 1 := by rw [hc2]; group
    have hc₁A : g * c * g⁻¹ ∈ A := F.perfect_inv D₁ hD₁N hD₁ _ hc₁ hc₁2
    have hc₁1 : g * c * g⁻¹ ≠ 1 := by
      intro h
      apply hc1
      calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hcomm : c * t' = t' * c := mem_centralizer_singleton_iff.mp (hDle hcD).2
    have hconj : IsConj d.t (g * c * g⁻¹ * d.t) := by
      have h1 : IsConj d.t (t' * c) := hc.trans (isConj_iff.mpr ⟨b, hbt⟩)
      refine h1.trans (isConj_iff.mpr ⟨g, ?_⟩)
      calc g * (t' * c) * g⁻¹ = g * (c * t') * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * d.t := by rw [← hgt]; group
    exact Facts.alpha_of_exists_mul_t F d hq2 hR hc₁A hc₁2 hc₁1 hconj

end Alpha

section AlphaCons

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {q : ℕ} {V₁ V₂ : Subgroup G}

theorem exists_u₀ (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) :
    ∃ u : G, u ∈ d.V ⊓ centralizer (d.V : Set G) ∧ u ∈ centralizer (d.P : Set G) ∧ u ≠ 1 ∧
      u * u = 1 ∧ IsConj d.t (u * d.t) := by
  obtain ⟨t', ht'z, ht'c, ht'ne⟩ := hα
  have ht'2 := d.mul_self_of_isConj ht'c
  rcases Facts.central_mem_U_or F d hq hR ht'z ht'2 with h | h
  · exact (Facts.not_isConj_of_mem F d hq hR h.1.2 ht'c).elim
  · have ht2 := d.t_mul_self
    have hcomm : t' * d.t = d.t * t' := (mem_centralizer_iff.mp ht'z.2 d.t d.t_mem_P).symm
    refine ⟨t' * d.t, h, mul_mem ht'z.2 d.t_mem_centralizer_P, ?_, ?_, ?_⟩
    · intro h1
      apply ht'ne
      have := congrArg (· * d.t) h1
      simpa [mul_assoc, ht2] using this
    · calc t' * d.t * (t' * d.t) = t' * (d.t * t') * d.t := by group
        _ = t' * (t' * d.t) * d.t := by rw [hcomm]
        _ = (t' * t') * (d.t * d.t) := by group
        _ = 1 := by rw [ht'2, ht2, one_mul]
    · have : t' * d.t * d.t = t' := by rw [mul_assoc, ht2, mul_one]
      rw [this]
      exact ht'c

theorem isConj_mul_t (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) {a : G} (haA : a ∈ A) (ha2 : a * a = 1) : IsConj d.t (a * d.t) := by
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
  obtain ⟨u, hu, -, hu1, hu2, hut⟩ := Facts.exists_u₀ F d hq hR hα
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨c, hc, hcu⟩ := F.invol_conj u hu.1.2 a haA huo hao
  have hct : c * d.t * c⁻¹ = d.t := by
    rw [d.comm_t_of_mem hc, mul_inv_cancel_right]
  refine hut.trans (isConj_iff.mpr ⟨c, ?_⟩)
  calc c * (u * d.t) * c⁻¹ = (c * u * c⁻¹) * (c * d.t * c⁻¹) := by group
    _ = a * d.t := by rw [hcu, hct]

theorem not_isConj_iff_mem (F : FusionFacts A q) (d : Datum A) (hq : 4 < q)
    (hR : Radicals d.V V₁ V₂ q) (hα : d.Alpha) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) {x : G}
    (hx : x ∈ W ⊔ zpowers d.t) : ¬ IsConj d.t x ↔ x ∈ W := by
  obtain ⟨hWV, hWe, -⟩ := hR.property hW
  constructor
  · intro hnc
    by_contra hxW
    have hxt : x * d.t ∈ W := ((d.mem_adj_iff hWV).mp hx).resolve_left hxW
    have h2 : (x * d.t) * (x * d.t) = 1 := by rw [← sq]; exact hWe.2 _ hxt
    have h3 := Facts.isConj_mul_t F d hq hR hα (hWV hxt).2 h2
    rw [mul_assoc, d.t_mul_self, mul_one] at h3
    exact hnc h3
  · intro hxW
    exact Facts.not_isConj_of_mem F d hq hR (hWV hxW).2

theorem conj_mem_V_of_mem (F : FusionFacts A q) (d : Datum A) (hq : 4 < q)
    (hR : Radicals d.V V₁ V₂ q) (hα : d.Alpha) {n : G} (hn : n ∈ normalizer (d.P : Set G))
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) {v : G} (hv : v ∈ W) : n * v * n⁻¹ ∈ d.V := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  have hmem : n * v * n⁻¹ ∈ (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom :=
    ⟨v, mem_sup_left hv, by simp [MulAut.conj_apply]⟩
  have hnc : ¬ IsConj d.t (n * v * n⁻¹) := by
    intro h
    refine Facts.not_isConj_of_mem F d hq hR (hWV hv).2 (h.trans (isConj_iff.mpr ⟨n⁻¹, ?_⟩))
    group
  rcases Facts.map_conj_adj F d hq hR hn hW with h | h
  · rw [h] at hmem
    exact hR.le₁ ((Facts.not_isConj_iff_mem F d hq hR hα (Or.inl rfl) hmem).mp hnc)
  · rw [h] at hmem
    exact hR.le₂ ((Facts.not_isConj_iff_mem F d hq hR hα (Or.inr rfl) hmem).mp hnc)

theorem mem_normalizer_V (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) {n : G} (hn : n ∈ normalizer (d.P : Set G)) :
    n ∈ normalizer (d.V : Set G) := by
  have hfwd : ∀ m ∈ normalizer (d.P : Set G), ∀ v ∈ d.V, m * v * m⁻¹ ∈ d.V := by
    intro m hm v hv
    have h1 : V₁.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      rintro _ ⟨w, hw, rfl⟩
      exact Facts.conj_mem_V_of_mem F d hq hR hα hm (Or.inl rfl) hw
    have h2 : V₂.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      rintro _ ⟨w, hw, rfl⟩
      exact Facts.conj_mem_V_of_mem F d hq hR hα hm (Or.inr rfl) hw
    have h3 : d.V.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      calc d.V.map (MulAut.conj m).toMonoidHom
          = (V₁ ⊔ V₂).map (MulAut.conj m).toMonoidHom := by rw [hR.sup_eq]
        _ = V₁.map (MulAut.conj m).toMonoidHom ⊔ V₂.map (MulAut.conj m).toMonoidHom :=
          Subgroup.map_sup _ _ _
        _ ≤ d.V := sup_le h1 h2
    have := h3 (Subgroup.mem_map_of_mem _ hv)
    simpa [MulAut.conj_apply] using this
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd n hn x hx, fun hx => ?_⟩
  have := hfwd n⁻¹ (inv_mem hn) _ hx
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem conj_V_le_A (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) {g : G} (hg : g⁻¹ * d.t * g ∈ d.P ⊓ centralizer (d.P : Set G)) {v : G}
    (hv : v ∈ d.V) : g * v * g⁻¹ ∈ A := by
  have hconj : IsConj d.t (g⁻¹ * d.t * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  obtain ⟨n, hn, hnt⟩ := OddStandard.Seitz77.exists_normalizer_conj_of_mem_center
    d.P_isSylow_centralizer hg hconj
  have hct : g * n⁻¹ * d.t * (g * n⁻¹)⁻¹ = d.t := by
    calc g * n⁻¹ * d.t * (g * n⁻¹)⁻¹ = g * (n⁻¹ * d.t * n) * g⁻¹ := by group
      _ = g * (g⁻¹ * d.t * g) * g⁻¹ := by rw [hnt]
      _ = d.t := by group
  have hc : g * n⁻¹ ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hct
  have hcN : g * n⁻¹ ∈ normalizer (A : Set G) := (OddStandard.centralizer_t_facts d.sector).1 hc
  have hnv : n * v * n⁻¹ ∈ A :=
    ((mem_normalizer_iff.mp (Facts.mem_normalizer_V F d hq hR hα hn) v).mp hv).2
  have e : g * v * g⁻¹ = (g * n⁻¹) * (n * v * n⁻¹) * (g * n⁻¹)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp hcN _).mp hnv

theorem sg_eq_zpowers (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) : sg A d.R = zpowers d.t := by
  obtain ⟨g, a, hgS, hord, ha1, hcard, ht⟩ := OddStandard.exists_generator_sg d.sector
  have hz : zpowers d.t ≤ sg A d.R := zpowers_le.mpr (OddStandard.t_mem_sg d.sector)
  by_cases ha : a = 1
  · refine (Subgroup.eq_of_le_of_card_ge hz ?_).symm
    rw [Nat.card_zpowers, d.sector.t_order, hcard, ha]
    norm_num
  exfalso
  have h4 : 4 ≤ Nat.card (sg A d.R) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨w, hwR, hww⟩ := OddStandard.exists_sq_eq_t d.sector h4
  have hα' : d.Alpha := hα
  obtain ⟨t', ht'z, ht'c, ht'ne⟩ := hα
  obtain ⟨n, hn, hnt⟩ := OddStandard.Seitz77.exists_normalizer_conj_of_mem_center
    d.P_isSylow_centralizer ht'z ht'c
  have hwP : w ∈ d.P := d.hRP hwR
  have hwK : w ∈ centralizer (A : Set G) := OddStandard.sg_le_centralizer hwR
  have hw'P : n⁻¹ * w * n ∈ d.P := (mem_normalizer_iff''.mp hn w).mp hwP
  have hw'V : ∀ v ∈ d.V, (n⁻¹ * w * n) * v = v * (n⁻¹ * w * n) := by
    intro v hv
    have hv' : n * v * n⁻¹ ∈ d.V :=
      (mem_normalizer_iff.mp (Facts.mem_normalizer_V F d hq hR hα' hn) v).mp hv
    have h := mem_centralizer_iff.mp hwK (n * v * n⁻¹) hv'.2
    calc n⁻¹ * w * n * v = n⁻¹ * (w * (n * v * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * v * n⁻¹) * w) * n := by rw [← h]
      _ = v * (n⁻¹ * w * n) := by group
  have hw'N : n⁻¹ * w * n ∈ normalizer (A : Set G) ⊓ centralizer (d.V : Set G) :=
    ⟨d.P_le_normalizer hw'P, mem_centralizer_iff.mpr fun v hv => (hw'V v hv).symm⟩
  have hmem := F.cent_sylow d.V d.V_isSylow hw'N
  obtain ⟨u, hu, k, hk, hw'⟩ := OddStandard.Seitz77.mem_sup_of_commute
    (V := d.V ⊓ centralizer (d.V : Set G)) (R := centralizer (A : Set G))
    (fun u hu k hk => mem_centralizer_iff.mp hk u hu.1.2) hmem
  have hkP : k ∈ d.P := by
    have : k = u⁻¹ * (n⁻¹ * w * n) := by rw [hw']; group
    rw [this]
    exact d.P.mul_mem (d.P.inv_mem hu.1.1) hw'P
  have hkR : k ∈ sg A d.R := by
    rw [← d.P_inf_centralizer_eq]
    exact ⟨hkP, hk⟩
  have hu2 : u * u = 1 := hR.mul_self_of_mem_center hu
  have huk : u * k = k * u := mem_centralizer_iff.mp hk u hu.1.2
  have ht'kk : t' = k * k := by
    calc t' = n⁻¹ * (w * w) * n := by rw [← hnt, hww]
      _ = (n⁻¹ * w * n) * (n⁻¹ * w * n) := by group
      _ = (u * k) * (u * k) := by rw [hw']
      _ = (u * u) * (k * k) := by
        calc u * k * (u * k) = u * (k * u) * k := by group
          _ = u * (u * k) * k := by rw [huk]
          _ = (u * u) * (k * k) := by group
      _ = k * k := by rw [hu2, one_mul]
  have hord' : orderOf t' = 2 := by
    rw [OddStandard.Seitz77.orderOf_eq_of_isConj ht'c]
    exact d.sector.t_order
  exact ht'ne (OddStandard.eq_t_of_orderOf_eq_two d.sector (ht'kk ▸ mul_mem hkR hkR) hord')

theorem two_dvd_index (F : FusionFacts A q) (d : Datum A) (hq : 4 < q) (hR : Radicals d.V V₁ V₂ q)
    (hα : d.Alpha) : 2 ∣ d.P.index := by
  by_contra hodd
  have hodd' := OddStandard.Seitz77.odd_card_normalizer_class d.P_le_centralizer hodd
  have ht2 := d.t_mul_self
  have hcls : ∀ x : G, (∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n) →
      x ∈ d.P ⊓ centralizer (d.P : Set G) ∧ IsConj d.t x := by
    rintro x ⟨n, hn, rfl⟩
    refine ⟨⟨(mem_normalizer_iff''.mp hn d.t).mp d.t_mem_P,
      mem_centralizer_iff.mpr fun p hp => ?_⟩, isConj_iff.mpr ⟨n⁻¹, by group⟩⟩
    have hp' : n * p * n⁻¹ ∈ d.P := (mem_normalizer_iff.mp hn p).mp hp
    have h := d.P_comm_t hp'
    calc p * (n⁻¹ * d.t * n) = n⁻¹ * ((n * p * n⁻¹) * d.t) * n := by group
      _ = n⁻¹ * (d.t * (n * p * n⁻¹)) * n := by rw [h]
      _ = n⁻¹ * d.t * n * p := by group
  have hmemCU : ∀ x : G, (∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n) →
      x * d.t ∈ d.CU := by
    intro x hx
    obtain ⟨hxz, hxc⟩ := hcls x hx
    have hx2 := d.mul_self_of_isConj hxc
    rcases Facts.central_mem_U_or F d hq hR hxz hx2 with h | h
    · exact (Facts.not_isConj_of_mem F d hq hR h.1.2 hxc).elim
    · exact ⟨h, mul_mem hxz.2 d.t_mem_centralizer_P⟩
  let f : {x : G // ∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n} → ↥d.CU :=
    fun x => ⟨x.1 * d.t, hmemCU x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (mul_right_cancel this)
    · rintro ⟨u, hu⟩
      have hu2 := hR.mul_self_of_mem_center hu.1
      have hconj := Facts.isConj_mul_t F d hq hR hα hu.1.1.2 hu2
      have hz : u * d.t ∈ d.P ⊓ centralizer (d.P : Set G) :=
        ⟨d.P.mul_mem hu.1.1.1 d.t_mem_P, mul_mem hu.2 d.t_mem_centralizer_P⟩
      obtain ⟨n, hn, hnt⟩ := OddStandard.Seitz77.exists_normalizer_conj_of_mem_center
        d.P_isSylow_centralizer hz hconj
      refine ⟨⟨u * d.t, n, hn, hnt.symm⟩, Subtype.ext ?_⟩
      show u * d.t * d.t = u
      rw [mul_assoc, ht2, mul_one]
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [hcard] at hodd'
  obtain ⟨u₀, hu₀, hu₀P, hu₀1, -, -⟩ := Facts.exists_u₀ F d hq hR hα
  have hCUP : d.CU ≤ d.P := fun x hx => hx.1.1.1
  have hP2 : IsPGroup 2 ↥d.CU := d.hP.isPGroup.to_le hCUP
  rcases hP2.card_eq_or_dvd with h1 | h2
  · have : d.CU = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hmem : u₀ ∈ d.CU := ⟨hu₀, hu₀P⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hu₀1 hmem
  · exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)

theorem mul_t_mem_U_of_isConj (F : FusionFacts A q) (d : Datum A) (hq : 4 < q)
    (hR : Radicals d.V V₁ V₂ q) {x : G} (hx : x ∈ d.P ⊓ centralizer (d.P : Set G))
    (hxc : IsConj d.t x) : x * d.t ∈ d.V ⊓ centralizer (d.V : Set G) := by
  rcases Facts.central_mem_U_or F d hq hR hx (d.mul_self_of_isConj hxc) with h | h
  · exact (Facts.not_isConj_of_mem F d hq hR h.1.2 hxc).elim
  · exact h

end AlphaCons

end Facts

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem four_lt (h : Hyp G A f) : 4 < 2 ^ f :=
  calc 4 < 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.three_le

theorem exists_conj_commuting (h : Hyp G A f) (d : Datum A) :
    ∃ g : G, g⁻¹ * d.t * g ≠ d.t ∧ g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g) := by
  have := h.simple
  exact SeitzReduction.F4Pilot.exists_conj_ne_commute_of_isSimpleGroup h.nonab d.sector.t_order

theorem exists_radicals (h : Hyp G A f) (d : Datum A) :
    ∃ V₁ V₂ : Subgroup G, Radicals d.V V₁ V₂ (2 ^ f) :=
  h.facts.radicals d.V d.V_isSylow

theorem alpha (h : Hyp G A f) (d : Datum A) : d.Alpha := by
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  exact Facts.alpha h.facts.toFusionFacts d h.four_lt hR (h.exists_conj_commuting d)

theorem not_isConj_of_mem (h : Hyp G A f) (d : Datum A) {x : G} (hxA : x ∈ A) :
    ¬ IsConj d.t x := by
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  exact Facts.not_isConj_of_mem h.facts.toFusionFacts d h.four_lt hR hxA

theorem not_isConj_iff_mem (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) {x : G}
    (hx : x ∈ W ⊔ zpowers d.t) : ¬ IsConj d.t x ↔ x ∈ W :=
  Facts.not_isConj_iff_mem h.facts.toFusionFacts d h.four_lt hR (h.alpha d) hW hx

theorem conj_V_le_A (h : Hyp G A f) (d : Datum A) {g : G}
    (hg : g⁻¹ * d.t * g ∈ d.P ⊓ centralizer (d.P : Set G)) {v : G} (hv : v ∈ d.V) :
    g * v * g⁻¹ ∈ A := by
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  exact Facts.conj_V_le_A h.facts.toFusionFacts d h.four_lt hR (h.alpha d) hg hv

theorem exists_u₀ (h : Hyp G A f) (d : Datum A) :
    ∃ u : G, u ∈ d.V ⊓ centralizer (d.V : Set G) ∧ u ∈ centralizer (d.P : Set G) ∧ u ≠ 1 ∧
      u * u = 1 ∧ IsConj d.t (u * d.t) := by
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  exact Facts.exists_u₀ h.facts.toFusionFacts d h.four_lt hR (h.alpha d)

theorem seitz21 (h : Hyp G A f) (d : Datum A) :
    sg A d.R = zpowers d.t ∧
    (∀ u ∈ d.V ⊓ centralizer (d.V : Set G), IsConj d.t (u * d.t)) ∧
    (∀ x ∈ A, ¬ IsConj d.t x) ∧ 2 ∣ d.P.index ∧
    (∀ g : G, g * d.t * g⁻¹ ∈ d.P ⊓ centralizer (d.P : Set G) → g * d.t * g⁻¹ ≠ d.t →
      d.V ≤ A.map (MulAut.conj g).toMonoidHom) ∧
    ∀ x ∈ d.P ⊓ centralizer (d.P : Set G), IsConj d.t x →
      x * d.t ∈ d.V ⊓ centralizer (d.V : Set G) := by
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  have F := h.facts.toFusionFacts
  have hq := h.four_lt
  have hα := h.alpha d
  refine ⟨Facts.sg_eq_zpowers F d hq hR hα, fun u hu => ?_, fun x hx => Facts.not_isConj_of_mem F d hq hR hx,
    Facts.two_dvd_index F d hq hR hα, fun g hg _ v hv => ?_,
    fun x hx hxc => Facts.mul_t_mem_U_of_isConj F d hq hR hx hxc⟩
  · exact Facts.isConj_mul_t F d hq hR hα hu.1.2 (hR.mul_self_of_mem_center hu)
  · have hg' : g⁻¹⁻¹ * d.t * g⁻¹ ∈ d.P ⊓ centralizer (d.P : Set G) := by rwa [inv_inv]
    have hmem := Facts.conj_V_le_A F d hq hR hα hg' hv
    refine ⟨g⁻¹ * v * g⁻¹⁻¹, hmem, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
