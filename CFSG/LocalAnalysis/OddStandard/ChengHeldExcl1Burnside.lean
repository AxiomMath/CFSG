module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Pi
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Tools
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupConj

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.not_isConj_q_pi_of_field_zero
    (hα : α ≤ 1) (hα0 : α = 0) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hE : chExcl1OK = true) (hk : ∀ k', (c.rep k').isSome → k' = Kind.field) :
    ¬ IsConj d.q c.pi := by
  intro hfus
  obtain ⟨g, hg, hgX⟩ := d.exists_conj_config h hfus
  obtain ⟨hqX, hqc⟩ := d.q_mem_X h
  have hqcomm : ∀ x ∈ d.X, x * d.q = d.q * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (hqc hx)
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hπX : c.pi ∈ d.X := d.S_le_X c.mem.1
  have hX : IsSylowOf 2 d.X (⊤ : Subgroup G) := c.X_sylow_G_of_facts hα h hP hQ
  have hmemX₂ : ∀ x, x ∈ CFSG.conjugate d.X g ↔ g * x * g⁻¹ ∈ d.X := fun x => mem_conjugate_iff
  have hX₂syl : IsSylowOf 2 (CFSG.conjugate d.X g) (⊤ : Subgroup G) := by
    have := isSylowOf_conjugate hX g
    have htop : CFSG.conjugate (⊤ : Subgroup G) g = ⊤ := by
      ext x
      simp [mem_conjugate_iff]
    rwa [htop] at this
  have hHX : (d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) ≤ d.X := inf_le_left
  have hHX₂ : (d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) ≤ CFSG.conjugate d.X g :=
    fun x hx => (hmemX₂ x).2 (hgX x hx.1 (mem_centralizer_singleton_iff.1 hx.2))
  have hcard : Nat.card d.X ≤ 2 * Nat.card ↥(d.X ⊓ centralizer ({c.pi} : Set G)) :=
    card_le_two_mul_centralizer hqcomm hqq (c.cj_pi_of_X hα h hP hQ hk)
  have hcard₂ : Nat.card (CFSG.conjugate d.X g) ≤
      2 * Nat.card ↥(d.X ⊓ centralizer ({c.pi} : Set G)) := by
    rw [card_conjugate]
    exact hcard
  have h1 : d.X ≤ normalizer ((d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_card_le_two_mul hHX hcard
  have h2 : CFSG.conjugate d.X g ≤
      normalizer ((d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_card_le_two_mul hHX₂ hcard₂
  obtain ⟨n, hnN, hn⟩ := exists_mem_normalizer_conj_of_isSylowOf_top hX hX₂syl h1 h2
  have hπX₂ : c.pi ∈ CFSG.conjugate d.X g :=
    hHX₂ ⟨hπX, mem_centralizer_singleton_iff.2 rfl⟩
  have hπcentral : ∀ x ∈ CFSG.conjugate d.X g, x * c.pi = c.pi * x := by
    intro x hx
    have hx' := (hmemX₂ x).1 hx
    have h3 := hqcomm _ hx'
    calc x * c.pi = g⁻¹ * ((g * x * g⁻¹) * d.q) * g := by rw [← hg]; group
      _ = g⁻¹ * (d.q * (g * x * g⁻¹)) * g := by rw [h3]
      _ = c.pi * x := by rw [← hg]; group
  have hζX : n⁻¹ * c.pi * n ∈ d.X := (hn c.pi).1 hπX₂
  have hζc : ∀ a ∈ d.X, a * (n⁻¹ * c.pi * n) = (n⁻¹ * c.pi * n) * a := by
    intro a ha
    have ha₂ : n * a * n⁻¹ ∈ CFSG.conjugate d.X g := (hn _).2 (by
      have : n⁻¹ * (n * a * n⁻¹) * n = a := by group
      rw [this]
      exact ha)
    have h3 := hπcentral _ ha₂
    calc a * (n⁻¹ * c.pi * n) = n⁻¹ * ((n * a * n⁻¹) * c.pi) * n := by group
      _ = n⁻¹ * (c.pi * (n * a * n⁻¹)) * n := by rw [h3]
      _ = (n⁻¹ * c.pi * n) * a := by group
  have hζS : n⁻¹ * c.pi * n ∈ centralizer (d.S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact hζc s (d.S_le_X hs)
  have hζQ : n⁻¹ * c.pi * n ∈ d.Q := c.centralizer_X_S_le_Q hα h hP hQ ⟨hζX, hζS⟩
  have hπ2 : c.pi * c.pi = 1 := by simpa [pow_two] using c.frame.pi2
  have hζ2 : (n⁻¹ * c.pi * n) * (n⁻¹ * c.pi * n) = 1 := by
    calc (n⁻¹ * c.pi * n) * (n⁻¹ * c.pi * n) = n⁻¹ * (c.pi * c.pi) * n := by group
      _ = 1 := by rw [hπ2]; group
  have hζ1 : n⁻¹ * c.pi * n ≠ 1 := fun h1 => c.pi_ne_one (by
    have h2 : n⁻¹ * c.pi * n = n⁻¹ * 1 * n := by rw [h1]; group
    exact mul_left_cancel (mul_right_cancel h2))
  have hordζ : orderOf (n⁻¹ * c.pi * n) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hζ2) hζ1
  have hζq : n⁻¹ * c.pi * n = d.q :=
    d.eq_q_of_mem_centralizer h (d.Q_le_centralizer hζQ) hordζ
  have hπeq : c.pi = n * d.q * n⁻¹ := by
    calc c.pi = n * (n⁻¹ * c.pi * n) * n⁻¹ := by group
      _ = n * d.q * n⁻¹ := by rw [hζq]
  have hfix := c.conj_q_of_normalizer hα hα0 h hP hQ hS2 hE hk hnN
  exact c.pi_ne_q hα h hP hQ (hπeq.trans hfix)

end CFSG.OddStandard.ChengHeld
