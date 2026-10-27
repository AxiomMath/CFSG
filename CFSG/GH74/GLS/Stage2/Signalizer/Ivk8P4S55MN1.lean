module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem n1_closure_inv {Y : Type} [Group Y] {b : MulAut Y} {R₀ : Subgroup Y} {r : Y}
    (hr : r ∈ R₀) {x : MulAut Y}
    (hx : x ∈ closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹}) :
    MulAut.conj r * x * (MulAut.conj r)⁻¹ ∈
      closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨r', hr', rfl⟩ := hy
    refine Subgroup.subset_closure ⟨r * r', R₀.mul_mem hr hr', ?_⟩
    simp only [map_mul]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have : MulAut.conj r * (x * y) * (MulAut.conj r)⁻¹ =
        (MulAut.conj r * x * (MulAut.conj r)⁻¹) * (MulAut.conj r * y * (MulAut.conj r)⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : MulAut.conj r * x⁻¹ * (MulAut.conj r)⁻¹ =
        (MulAut.conj r * x * (MulAut.conj r)⁻¹)⁻¹ := by
      group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem pCfg_innSub_of_n1 {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥) {p : ℕ}
    {b : MulAut Y} {R₀ : Subgroup Y} (h : N1Config Y p b R₀) : N1PCfg p (innSub Y) := by
  obtain ⟨hp, hp2, hbo, hR, hX⟩ := h
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : Y →* MulAut Y := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective_of_center_bot hc
  set X : Subgroup (MulAut Y) := closure {c' : MulAut Y | ∃ r ∈ R₀,
    c' = MulAut.conj r * b * (MulAut.conj r)⁻¹} with hXdef
  have hbX : b ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
  refine ⟨R₀.map c, X, ?_, hX, ?_, ?_⟩
  · have h2 : (⊤ : Subgroup Y).map c = innSub Y := (MonoidHom.range_eq_map c).symm
    have h3 : IsSylowOf 2 (R₀.map c) ((⊤ : Subgroup Y).map c) :=
      (isSylowOf_map_iff c hinj).2 hR
    rwa [h2] at h3
  · intro hbot
    rw [hbot, Subgroup.mem_bot] at hbX
    rw [hbX, orderOf_one] at hbo
    exact hp.one_lt.ne hbo
  · intro g hg
    obtain ⟨r, hr, rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => n1_closure_inv hr hx
    · intro hx
      have h3 := n1_closure_inv (R₀.inv_mem hr) hx
      have e : MulAut.conj r⁻¹ * (MulAut.conj r * x * (MulAut.conj r)⁻¹) *
          (MulAut.conj r⁻¹)⁻¹ = x := by
        simp only [map_inv]
        group
      rwa [e] at h3

theorem pCfg_of_n1_aut {Y : Type} [Group Y] [Finite Y] {G : Type*} [Group G] [Finite G]
    (Θ : G ≃* MulAut Y) {I : Subgroup G} (hI : I.map Θ.toMonoidHom = innSub Y)
    (hc : center Y = ⊥) {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} (h : N1Config Y p b R₀) :
    N1PCfg p I := by
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have h1 := pCfg_map Θ.symm (pCfg_innSub_of_n1 hc h)
  have h2 : (innSub Y).map Θ.symm.toMonoidHom = I := by
    rw [← hI, Subgroup.map_map]
    have : Θ.symm.toMonoidHom.comp Θ.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rwa [h2] at h1

theorem pCfg_of_n1_of_le_inner {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥) {p : ℕ}
    {b : MulAut Y} {R₀ : Subgroup Y}
    (hXI : closure {c' : MulAut Y | ∃ r ∈ R₀, c' = MulAut.conj r * b * (MulAut.conj r)⁻¹} ≤
      innSub Y)
    (h : N1Config Y p b R₀) : N1PCfg p (⊤ : Subgroup Y) := by
  obtain ⟨hp, hp2, hbo, hR, hX⟩ := h
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have : Fact p.Prime := ⟨hp⟩
  set c : Y →* MulAut Y := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective_of_center_bot hc
  set X : Subgroup (MulAut Y) := closure {c' : MulAut Y | ∃ r ∈ R₀,
    c' = MulAut.conj r * b * (MulAut.conj r)⁻¹} with hXdef
  have hXc : X ≤ c.range := hXI
  have hbX : b ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
  refine ⟨R₀, X.comap c, hR, ?_, ?_, ?_⟩
  · refine IsPGroup.comap_of_ker_isPGroup hX c ?_
    rw [(MonoidHom.ker_eq_bot_iff c).2 hinj]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup Y) = p ^ 0)
  · intro hbot
    obtain ⟨y, hy⟩ := hXc hbX
    have hyW : y ∈ X.comap c := by
      rw [Subgroup.mem_comap]
      rw [show c y = b from hy]
      exact hbX
    rw [hbot, Subgroup.mem_bot] at hyW
    rw [hyW, map_one] at hy
    have : orderOf b = 1 := by rw [← hy, orderOf_one]
    rw [hbo] at this
    exact hp.one_lt.ne' this
  · intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := n1_closure_inv hr hy
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact h1
    · intro hy
      have hy' : c (r * y * r⁻¹) ∈ X := hy
      have h2 : c y = c r⁻¹ * c (r * y * r⁻¹) * (c r⁻¹)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      have h3 := n1_closure_inv (R₀.inv_mem hr) hy'
      rw [Subgroup.mem_comap, h2]
      simpa only [map_inv] using h3

theorem pCfg_of_n1_of_mem_inner {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥) {p : ℕ}
    {b : MulAut Y} {R₀ : Subgroup Y} (hb : b ∈ innSub Y) (h : N1Config Y p b R₀) :
    N1PCfg p (⊤ : Subgroup Y) := by
  refine pCfg_of_n1_of_le_inner hc ((Subgroup.closure_le _).2 ?_) h
  rintro c' ⟨r, -, rfl⟩
  exact mul_mem (mul_mem ⟨r, rfl⟩ hb) (inv_mem ⟨r, rfl⟩)

theorem pCfg_of_n1_inner {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y}
    (h : N1Config Y p b R₀) : N1PCfg p (⊤ : Subgroup Y) := by
  have hp := h.1
  have hp2 := h.2.1
  have hXp := h.2.2.2.2
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_bot hc
  have hcardI : Nat.card ↥(innSub Y) = Nat.card Y := by
    have hrange : innSub Y = (MulAut.conj : Y →* MulAut Y).range := rfl
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine pCfg_of_n1_of_le_inner hc ?_ h
  refine CFSG.Sporadic.SmallOddCore.odd_card_map_le_of_index_le_two (innSub Y) ?_ ?_
  · rw [hcardI]
    exact hcard
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    rw [hn]
    exact Odd.pow (hp.odd_of_ne_two hp2)

theorem pCfg_top_of_n1_equiv {Y G : Type} [Group Y] [Group G] [Finite G] (e : Y ≃* G)
    (hc : center G = ⊥) (hcard : Nat.card (MulAut G) ≤ 2 * Nat.card G) {p : ℕ}
    {b : MulAut Y} {R₀ : Subgroup Y} (h : N1Config Y p b R₀) : N1PCfg p (⊤ : Subgroup G) := by
  have hYfin : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hcY : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := congrArg e (hz (e.symm g))
      simpa using this
    rw [hc, Subgroup.mem_bot] at hz'
    exact e.injective (by simpa using hz')
  have hcardY : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    have h1 : Nat.card (MulAut Y) = Nat.card (MulAut G) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h2 : Nat.card Y = Nat.card G := Nat.card_congr e.toEquiv
    rw [h1, h2]
    exact hcard
  have hpc := pCfg_map e (pCfg_of_n1_inner hcY hcardY h)
  have htop : (⊤ : Subgroup Y).map e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact e.surjective
  rwa [htop] at hpc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
