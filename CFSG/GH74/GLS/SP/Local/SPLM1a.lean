module

public import CFSG.GH74.GLS.SP.Local.SPLWt6

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section R1

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem SPLNot3.X₂_le_R₂ : D.X₂ ≤ D.R₂ := le_sup_left.trans le_sup_left

omit [Finite G] in
theorem X₂_comm_X₃ (h3 : SPL3M2 D) : ∀ x ∈ D.X₂, ∀ y ∈ D.X₃, x * y = y * x := by
  intro x hx y hy
  have hx' : x ∈ (center ↥D.R₂).map D.R₂.subtype := by rw [h3.R₂_center]; exact hx
  obtain ⟨u, hu, rfl⟩ := hx'
  have := Subgroup.mem_center_iff.mp hu ⟨y, X₃_le_R₂ D hy⟩
  exact congrArg Subtype.val this.symm

theorem X₁_comm_X₂ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    ∀ x ∈ D.X₁, ∀ y ∈ D.X₂, x * y = y * x := fun x hx y hy =>
  hs.comps.comm x (h3.X₁_le hx) y (X₂_le_K₂ D hs h3.toSPL3X hy)

theorem R₁_comm (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    ∀ a ∈ D.R₁, ∀ b ∈ D.R₁, a * b = b * a := by
  have c12 := X₁_comm_X₂ D hs h3
  have c13 := h3.X₁_X₃
  have c23 := X₂_comm_X₃ D h3
  have c11 := h3.X₁_eab.1
  have c22 := (X₂_eab D h3).1
  have c33 := (X₃_eab D h3).1
  have hX : ∀ x : G, (x ∈ D.X₁ ∨ x ∈ D.X₂ ∨ x ∈ D.X₃) → D.R₁ ≤ centralizer ({x} : Set G) := by
    intro x hx
    refine sup_le (sup_le (fun y hy => ?_) (fun y hy => ?_)) (fun y hy => ?_)
    · rw [mem_centralizer_singleton_iff]
      rcases hx with hx | hx | hx
      · exact c11 y hy x hx
      · exact c12 y hy x hx
      · exact c13 y hy x hx
    · rw [mem_centralizer_singleton_iff]
      rcases hx with hx | hx | hx
      · exact (c12 x hx y hy).symm
      · exact c22 y hy x hx
      · exact c23 y hy x hx
    · rw [mem_centralizer_singleton_iff]
      rcases hx with hx | hx | hx
      · exact (c13 x hx y hy).symm
      · exact (c23 x hx y hy).symm
      · exact c33 y hy x hx
  have hR : D.R₁ ≤ centralizer (D.R₁ : Set G) := by
    refine sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro y hy
      have := mem_centralizer_singleton_iff.mp (hX x (Or.inl hx) hy)
      exact this
    · rw [mem_centralizer_iff]
      intro y hy
      have := mem_centralizer_singleton_iff.mp (hX x (Or.inr (Or.inl hx)) hy)
      exact this
    · rw [mem_centralizer_iff]
      intro y hy
      have := mem_centralizer_singleton_iff.mp (hX x (Or.inr (Or.inr hx)) hy)
      exact this
  intro a ha b hb
  exact (mem_centralizer_iff.mp (hR hb) a ha)

omit [Finite G] in
theorem normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro g
  have hc : ∀ a ∈ A, ∀ c ∈ B, c * a * c⁻¹ = a := fun a ha c hc => by
    rw [← h a ha c hc]; group
  constructor
  · intro hg
    rw [hc g hg b hb]; exact hg
  · intro hg
    have := hc _ hg b⁻¹ (B.inv_mem hb)
    have e : b⁻¹ * (b * g * b⁻¹) * b⁻¹⁻¹ = g := by group
    rw [e] at this
    rw [this]; exact hg

theorem X₁_inf_R₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.X₁ ⊓ D.R₂ = ⊥ := by
  rcases inf_irred (irred_X₁ D hs h1 h3) (H_R₂ D hs h1 h3) h3.H_X₁ with h | h
  · rw [inf_comm]; exact h
  · exfalso
    have hP : D.P = D.R₂ := le_antisymm (sup_le h le_rfl) le_sup_right
    have := h3.P_card
    rw [hP, h3.R₂_card] at this
    have hq : 1 < D.q := by have := hs.q_ge; omega
    have : D.q ^ 3 < D.q ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
    omega

theorem X₂_inf_X₃' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.X₂ ⊓ D.X₃ = ⊥ := by
  rcases inf_irred (irred_X₂ D hs h1 h3) h3.H_X₃ (H_X₂ D hs h1 h3.toSPL3X) with h | h
  · rw [inf_comm]; exact h
  · exfalso
    have heq : D.X₂ = D.X₃ := Subgroup.eq_of_le_of_card_ge h (by rw [X₂_card D h3, X₃_card D h3])
    apply ker_ne_23 D hs h1 h3
    rw [heq]

theorem R₁_card_three (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    Nat.card ↥D.R₁ = D.q ^ 3 := by
  have c := R₁_comm D hs h3
  have hX12 : D.X₁ ⊓ D.X₂ = ⊥ := X₁_inf_X₂ D hs h3
  have h12 : Nat.card ↥(D.X₁ ⊔ D.X₂ : Subgroup G) = D.q ^ 2 := by
    have hn := normalizer_of_commute (A := D.X₁) (B := D.X₂)
      (fun a ha b hb => c a (D.X₁_le_R₁ ha) b (D.X₂_le_R₁ hb))
    have := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hn
    rw [hX12, Subgroup.card_bot, h3.X₁_card, X₂_card D h3] at this
    rw [pow_two]; omega
  have hX3 : (D.X₁ ⊔ D.X₂) ⊓ D.X₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy12, hy3⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup_of_commute
      (fun a ha b hb => X₁_comm_X₂ D hs h3 a ha b hb) hy12
    have hx₁R : x₁ ∈ D.R₂ := by
      have : x₁ = (x₁ * x₂) * x₂⁻¹ := by group
      rw [this]
      exact D.R₂.mul_mem (X₃_le_R₂ D hy3) (D.R₂.inv_mem (D.X₂_le_R₂ hx₂))
    have : x₁ ∈ D.X₁ ⊓ D.R₂ := ⟨hx₁, hx₁R⟩
    rw [X₁_inf_R₂ D hs h1 h3] at this
    have hx1 : x₁ = 1 := Subgroup.mem_bot.mp this
    subst hx1
    have : x₂ ∈ D.X₂ ⊓ D.X₃ := ⟨hx₂, by simpa using hy3⟩
    rw [X₂_inf_X₃' D hs h1 h3] at this
    have hx2 : x₂ = 1 := Subgroup.mem_bot.mp this
    subst hx2
    simp
  have hn2 := normalizer_of_commute (A := D.X₁ ⊔ D.X₂) (B := D.X₃)
    (fun a ha b hb => c a (sup_le (D.X₁_le_R₁) (D.X₂_le_R₁) ha) b (D.X₃_le_R₁ hb))
  have := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hn2
  rw [hX3, Subgroup.card_bot, h12, X₃_card D h3] at this
  show Nat.card ↥(D.X₁ ⊔ D.X₂ ⊔ D.X₃ : Subgroup G) = D.q ^ 3
  rw [pow_succ]; omega

theorem R₁_exp (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) : ∀ x ∈ D.R₁, x ^ D.p = 1 := by
  have c := R₁_comm D hs h3
  intro x hx
  have hx' : x ∈ (D.X₁ ⊔ D.X₂ : Subgroup G) ⊔ D.X₃ := hx
  obtain ⟨u, hu, x₃, hx₃, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => c a (sup_le (D.X₁_le_R₁) (D.X₂_le_R₁) ha) b (D.X₃_le_R₁ hb)) hx'
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => X₁_comm_X₂ D hs h3 a ha b hb) hu
  have h12 : Commute x₁ x₂ := X₁_comm_X₂ D hs h3 x₁ hx₁ x₂ hx₂
  have h13 : Commute x₁ x₃ := h3.X₁_X₃ x₁ hx₁ x₃ hx₃
  have h23 : Commute x₂ x₃ := X₂_comm_X₃ D h3 x₂ hx₂ x₃ hx₃
  rw [(Commute.mul_left h13 h23).mul_pow, h12.mul_pow, h3.X₁_eab.2 x₁ hx₁,
    (X₂_eab D h3).2 x₂ hx₂, (X₃_eab D h3).2 x₃ hx₃]
  simp

theorem X₄_inf_R₁' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.X₄ ⊓ D.R₁ = ⊥ := by
  rcases inf_irred (irred_X₄ D hs h1 h3) (H_R₁ D hs h1 h3) (H_X₄ D hs h1 h3) with h | h
  · rw [inf_comm]; exact h
  · exfalso
    have hP : D.P = D.R₁ := by
      apply le_antisymm _ (D.R₁_le_P)
      show D.X₁ ⊔ (D.X₂ ⊔ D.X₃ ⊔ D.X₄) ≤ D.R₁
      exact sup_le (D.X₁_le_R₁) (sup_le (sup_le (D.X₂_le_R₁) (D.X₃_le_R₁)) h)
    have := h3.P_card
    rw [hP, R₁_card_three D hs h1 h3] at this
    have hq : 1 < D.q := by have := hs.q_ge; omega
    have : D.q ^ 3 < D.q ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
    omega

theorem P_decomp' (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∀ p ∈ D.P, ∃ r ∈ D.R₁, ∃ x ∈ D.X₄, p = r * x := by
  have hinf := X₄_inf_R₁' D hs h1 h3
  let f : ↥D.R₁ × ↥D.X₄ → ↥D.P := fun t =>
    ⟨(t.1 : G) * t.2, D.P.mul_mem (D.R₁_le_P t.1.2) (D.X₄_le_P t.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨r, x⟩ ⟨r', x'⟩ h
    have h' : (r : G) * x = r' * x' := congrArg Subtype.val h
    have hm : (r' : G)⁻¹ * r = x' * (x : G)⁻¹ := by
      calc (r' : G)⁻¹ * r = (r' : G)⁻¹ * (r * x) * (x : G)⁻¹ := by group
        _ = (r' : G)⁻¹ * (r' * x') * (x : G)⁻¹ := by rw [h']
        _ = x' * (x : G)⁻¹ := by group
    have hmem : (r' : G)⁻¹ * r ∈ D.X₄ ⊓ D.R₁ := by
      refine ⟨?_, D.R₁.mul_mem (D.R₁.inv_mem r'.2) r.2⟩
      rw [hm]; exact D.X₄.mul_mem x'.2 (D.X₄.inv_mem x.2)
    rw [hinf] at hmem
    have h1' : (r' : G)⁻¹ * r = 1 := Subgroup.mem_bot.mp hmem
    have hrr : (r : G) = r' := (inv_mul_eq_one.mp h1').symm
    have hxx : (x : G) = x' := by
      have : (x : G) = (r : G)⁻¹ * (r * x) := by group
      rw [this, h', ← hrr]; group
    exact Prod.ext (Subtype.ext hrr) (Subtype.ext hxx)
  have hcard : Nat.card (↥D.R₁ × ↥D.X₄) = Nat.card ↥D.P := by
    rw [Nat.card_prod, R₁_card_three D hs h1 h3, X₄_card D h3, h3.P_card]
    ring
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  intro p hp
  obtain ⟨⟨r, x⟩, hrx⟩ := hbij.2 ⟨p, hp⟩
  exact ⟨r, r.2, x, x.2, (congrArg Subtype.val hrx).symm⟩

theorem R₁_normal_P (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∀ x ∈ D.P, ∀ r ∈ D.R₁, x * r * x⁻¹ ∈ D.R₁ := by
  have hHR := H_R₁ D hs h1 h3
  have hHP := H_P D hs h1 h3
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = normalizer (D.R₁ : Set G) ⊓ D.P := ⟨_, rfl⟩
  have hRN : D.R₁ ≤ N := by rw [hN]; exact le_inf Subgroup.le_normalizer D.R₁_le_P
  have hNP : N ≤ D.P := by rw [hN]; exact inf_le_right
  have hNH : Normalizes D.H N := by
    intro h hh n hn
    rw [hN] at hn ⊢
    refine ⟨?_, hHP h hh n hn.2⟩
    apply mem_normalizer_of_conj_le
    intro r hr
    have hr' : h⁻¹ * r * h ∈ D.R₁ := by
      have := hHR h⁻¹ (D.H.inv_mem hh) r hr
      simpa using this
    have hnr := (mem_normalizer_iff.mp hn.1 _).mp hr'
    have := hHR h hh _ hnr
    have e : h * (n * (h⁻¹ * r * h) * n⁻¹) * h⁻¹ = (h * n * h⁻¹) * r * (h * n * h⁻¹)⁻¹ := by group
    rw [e] at this
    exact this
  have hlt : D.R₁ < N := by
    have hpg : IsPGroup D.p ↥D.P := h3.P_pGroup
    have : Fact D.p.Prime := ⟨hs.prime⟩
    have : Group.IsNilpotent ↥D.P := hpg.isNilpotent
    have hne : D.R₁.subgroupOf D.P ≠ ⊤ := by
      intro h
      have hPR : D.P ≤ D.R₁ := fun x hx => by
        have : (⟨x, hx⟩ : ↥D.P) ∈ D.R₁.subgroupOf D.P := by rw [h]; exact Subgroup.mem_top _
        exact this
      have hP : D.P = D.R₁ := le_antisymm hPR D.R₁_le_P
      have := h3.P_card
      rw [hP, R₁_card_three D hs h1 h3] at this
      have hq : 1 < D.q := by have := hs.q_ge; omega
      have : D.q ^ 3 < D.q ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
      omega
    have hlt' := Group.normalizerCondition_of_isNilpotent (D.R₁.subgroupOf D.P)
      (lt_top_iff_ne_top.mpr hne)
    obtain ⟨y, hy, hyn⟩ := IsConcreteLE.exists_of_lt hlt'
    rw [IsConcreteLE.lt_iff_le_and_exists]
    refine ⟨hRN, (y : G), ?_, ?_⟩
    · rw [hN]
      refine ⟨?_, y.2⟩
      apply mem_normalizer_of_conj_le
      intro r hr
      have := (mem_normalizer_iff.mp hy ⟨r, D.R₁_le_P hr⟩).mp (by
        rw [Subgroup.mem_subgroupOf]; exact hr)
      exact this
    · intro hyR
      exact hyn hyR
  rcases inf_irred (irred_X₄ D hs h1 h3) hNH (H_X₄ D hs h1 h3) with hbot | hle
  · exfalso
    have hNR : N ≤ D.R₁ := by
      intro n hn
      obtain ⟨r, hr, x, hx, hnrx⟩ := P_decomp' D hs h1 h3 n (hNP hn)
      have hxN : x ∈ N := by
        have : x = r⁻¹ * n := by rw [hnrx]; group
        rw [this]; exact N.mul_mem (N.inv_mem (hRN hr)) hn
      have : x ∈ N ⊓ D.X₄ := ⟨hxN, hx⟩
      rw [hbot] at this
      have hx1 : x = 1 := Subgroup.mem_bot.mp this
      rw [hnrx, hx1, mul_one]; exact hr
    exact absurd hlt (not_lt_of_ge hNR)
  · have hPN : D.P ≤ N := by
      calc D.P = D.R₁ ⊔ D.X₄ := D.P_eq_R₁_sup_X₄
        _ ≤ N := sup_le hRN hle
    intro x hx r hr
    have : x ∈ normalizer (D.R₁ : Set G) := by
      have := hPN hx
      rw [hN] at this
      exact this.1
    exact (mem_normalizer_iff.mp this r).mp hr

end R1

end CFSG.GH74.GLS.SP.Local
