module

public import CFSG.GH74.GLS.SP.Local.SPLL34b

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.IVK.L2Torus
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

theorem conjHom_apply {G : Type} [Group G] (h x : G) :
    (MulAut.conj h).toMonoidHom x = h * x * h⁻¹ := by
  simp [MulAut.conj_apply]

theorem eq_sl2U_of_mem_upperSub {F : Type} [Field F] {x : SL2m F} (hx : x ∈ SL2Root.upperSub F) :
    ∃ s : F, x = sl2U s := by
  obtain ⟨h00, h11, h10⟩ := SL2Root.mem_upperSub.mp hx
  refine ⟨x.1 0 1, ?_⟩
  apply CFSG.GH74.GLS.Stage4.Hex.sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2U, h00, h11, h10]

theorem card_eq_pow_two_mul {G : Type} [Group G] [Finite G] (C V T : Subgroup G) (hVC : V ≤ C)
    (hVn : ∀ g ∈ C, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hT2 : IsPGroup 2 ↥T)
    (hCVT : ∀ g ∈ C, ∃ v ∈ V, ∃ s ∈ T, g = v * s) :
    ∃ k : ℕ, Nat.card ↥C = 2 ^ k * Nat.card ↥V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V' : Subgroup ↥C := V.subgroupOf C
  have hV'n : V'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥C) : G) ∈ V
    exact hVn g g.2 n hn⟩
  have hQ : IsPGroup 2 (↥C ⧸ V') := by
    intro q
    refine QuotientGroup.induction_on q (fun g' => ?_)
    · obtain ⟨v, hv, s, hsT, hdec⟩ := hCVT g' g'.2
      have hsC : s ∈ C := by
        have : s = v⁻¹ * (g' : G) := by rw [hdec]; group
        rw [this]; exact C.mul_mem (C.inv_mem (hVC hv)) g'.2
      obtain ⟨j, hj⟩ := hT2 ⟨s, hsT⟩
      refine ⟨j, ?_⟩
      have hj' : s ^ (2 ^ j) = 1 := congrArg Subtype.val hj
      have hg'eq : (QuotientGroup.mk g' : ↥C ⧸ V') = QuotientGroup.mk (⟨s, hsC⟩ : ↥C) := by
        rw [QuotientGroup.eq]
        show ((g' : G)⁻¹ * s) ∈ V
        have e : (g' : G)⁻¹ * s = s⁻¹ * v⁻¹ * s⁻¹⁻¹ := by rw [hdec]; group
        rw [e]
        exact hVn s⁻¹ (C.inv_mem hsC) v⁻¹ (V.inv_mem hv)
      rw [hg'eq, ← QuotientGroup.mk_pow]
      have : (⟨s, hsC⟩ : ↥C) ^ (2 ^ j) = 1 := Subtype.ext hj'
      rw [this, QuotientGroup.mk_one]
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  refine ⟨n, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V', hn,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv]

section L34c

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem exists_V_plus (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) (hq : D.q % 4 = 1) :
    ∃ V : Subgroup G, V ≤ D.C₁ ∧ (∀ g ∈ D.C₁, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
      Odd (Nat.card ↥V) ∧ (∀ g ∈ D.C₁, Odd (orderOf g) → g ∈ V) ∧
      ∃ k : ℕ, Nat.card ↥D.C₁ = 2 ^ k * Nat.card ↥V := by
  classical
  obtain ⟨V₀, hV₀C, hV₀n, hV₀odd, -, hV₀all, hV₀T⟩ := exists_V₀ D hs hc h3
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, -, -⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  have : Fintype F := Fintype.ofFinite F
  have hsq : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    have : Fintype.card F = D.q := by rw [← Nat.card_eq_fintype_card, hFq]
    rw [this]; omega
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr
    exact one_ne_zero (neg_eq_zero.mp hr)
  obtain ⟨hk, hhk⟩ : ∃ hk : ↥D.K₁, ε hk = sl2D (Units.mk0 r hr0) := ⟨ε.symm (sl2D (Units.mk0 r hr0)), by simp⟩
  set h : G := (hk : G) with hh
  have hhK : h ∈ D.K₁ := hk.2
  have hinvX : ∀ a ∈ D.X₁, h * a * h⁻¹ = a⁻¹ := by
    intro a ha
    let kk : ↥D.K₁ := ⟨a, h3.X₁_le ha⟩
    obtain ⟨s, hs'⟩ := eq_sl2U_of_mem_upperSub ((hE1 kk).mp ha)
    have h1' : ε (hk * kk * hk⁻¹) = ε kk⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hhk, hs', sl2D_conj_sl2U, sl2U_inv']
      congr 1
      have : ((Units.mk0 r hr0 : Fˣ) : F) ^ 2 = -1 := by
        rw [Units.val_mk0, sq]; exact hr.symm
      rw [this]; ring
    have := congrArg Subtype.val (ε.injective h1')
    exact this
  have hconjY : ∀ y ∈ D.Y₀, h * y * h⁻¹ ∈ D.Y₁ := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Y₀_decomp D hs h3 hy
    have hb : D.t * a * D.t⁻¹ ∈ D.K₂ := X₂_le_K₂ D hs h3 (t_mem_X₂ D hs ha)
    have hcomm : h * (D.t * a * D.t⁻¹) = (D.t * a * D.t⁻¹) * h := hs.comps.comm h hhK _ hb
    have e : h * (a * (D.t * a * D.t⁻¹)) * h⁻¹ = a⁻¹ * (D.t * (a⁻¹)⁻¹ * D.t⁻¹) := by
      calc h * (a * (D.t * a * D.t⁻¹)) * h⁻¹
          = (h * a * h⁻¹) * (h * (D.t * a * D.t⁻¹) * h⁻¹) := by group
        _ = a⁻¹ * (D.t * a * D.t⁻¹) := by rw [hinvX a ha, hcomm]; group
        _ = a⁻¹ * (D.t * (a⁻¹)⁻¹ * D.t⁻¹) := by rw [inv_inv]
    rw [e]
    exact Y₁_diag D h3 (D.X₁.inv_mem ha)
  have hmap : D.Y₀.map (MulAut.conj h).toMonoidHom ≤ D.Y₁ := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hconjY y hy
  have hcard : Nat.card ↥(D.Y₀.map (MulAut.conj h).toMonoidHom) = Nat.card ↥D.Y₁ := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, Y₀_card D hs h3, h3.Y₁_card]
  have hY₁eq : D.Y₀.map (MulAut.conj h).toMonoidHom = D.Y₁ :=
    Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  have hC : ∀ g : G, g ∈ D.C₁ ↔ h⁻¹ * g * h ∈ D.C₀ := by
    intro g
    rw [mem_C₁, mem_C₀]
    constructor
    · intro hg y hy
      have hy' : h * y * h⁻¹ ∈ D.Y₁ := hconjY y hy
      have := hg _ hy'
      calc y * (h⁻¹ * g * h) = h⁻¹ * ((h * y * h⁻¹) * g) * h := by group
        _ = h⁻¹ * (g * (h * y * h⁻¹)) * h := by rw [this]
        _ = (h⁻¹ * g * h) * y := by group
    · intro hg y hy
      rw [← hY₁eq] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      have := hg y₀ hy₀
      have e : ((MulAut.conj h).toMonoidHom y₀) = h * y₀ * h⁻¹ := conjHom_apply h y₀
      rw [e]
      calc h * y₀ * h⁻¹ * g = h * (y₀ * (h⁻¹ * g * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * g * h) * y₀) * h⁻¹ := by rw [this]
        _ = g * (h * y₀ * h⁻¹) := by group
  have hC₁eq : D.C₁ = D.C₀.map (MulAut.conj h).toMonoidHom := by
    ext g
    rw [hC g]
    constructor
    · intro hg
      refine ⟨h⁻¹ * g * h, hg, ?_⟩
      rw [conjHom_apply]; group
    · rintro ⟨g₀, hg₀, rfl⟩
      have e : h⁻¹ * ((MulAut.conj h).toMonoidHom g₀) * h = g₀ := by rw [conjHom_apply]; group
      rw [e]; exact hg₀
  obtain ⟨k, hk₀⟩ := card_eq_pow_two_mul D.C₀ V₀ D.T₀ hV₀C hV₀n (T0_pgroup D hs hc) hV₀T
  refine ⟨V₀.map (MulAut.conj h).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v₀, hv₀, rfl⟩
    rw [hC]
    have e : h⁻¹ * ((MulAut.conj h).toMonoidHom v₀) * h = v₀ := by rw [conjHom_apply]; group
    rw [e]; exact hV₀C hv₀
  · rintro g hg _ ⟨v₀, hv₀, rfl⟩
    have hg' : h⁻¹ * g * h ∈ D.C₀ := (hC g).mp hg
    refine ⟨(h⁻¹ * g * h) * v₀ * (h⁻¹ * g * h)⁻¹, hV₀n _ hg' v₀ hv₀, ?_⟩
    rw [conjHom_apply, conjHom_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]; exact hV₀odd
  · intro g hg hodd
    have hg' : h⁻¹ * g * h ∈ D.C₀ := (hC g).mp hg
    have hodd' : Odd (orderOf (h⁻¹ * g * h)) := by
      have := orderOf_conj' h⁻¹ g
      simp only [inv_inv] at this
      rw [this]; exact hodd
    refine ⟨h⁻¹ * g * h, hV₀all _ hg' hodd', ?_⟩
    rw [conjHom_apply]; group
  · refine ⟨k, ?_⟩
    rw [hC₁eq, Subgroup.card_map_of_injective (MulAut.conj h).injective,
      Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hk₀

theorem t_not_mem_K (hs : SPLSetup D.toSPLNot0) : D.t ∉ D.K := by
  intro ht
  have hn : D.t ∈ normalizer (D.K₁ : Set G) := hs.comps.le_normalizer₁ ht
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  exact hs.comps.ne (h.symm.trans hs.syl.t_swap)

theorem K_normalizes (hs : SPLSetup D.toSPLNot0) {g : G} (hg : g ∈ D.K) :
    (∀ k ∈ D.K₁, g * k * g⁻¹ ∈ D.K₁) ∧ (∀ k ∈ D.K₂, g * k * g⁻¹ ∈ D.K₂) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hg
  constructor
  · intro k hk
    have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
      have : b * k = k * b := (hs.comps.comm k hk b hb).symm
      calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
        _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [this]
        _ = a * k * a⁻¹ := by group
    rw [e]; exact D.K₁.mul_mem (D.K₁.mul_mem ha hk) (D.K₁.inv_mem ha)
  · intro k hk
    have hbk : b * k * b⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hb hk) (D.K₂.inv_mem hb)
    have e : a * b * k * (a * b)⁻¹ = b * k * b⁻¹ := by
      have h2 : a * (b * k * b⁻¹) = (b * k * b⁻¹) * a := hs.comps.comm a ha _ hbk
      calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
        _ = b * k * b⁻¹ := by rw [h2]; group
    rw [e]; exact hbk

theorem comp_inverts (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {κ₁ κ₂ : G} (hκ₁ : κ₁ ∈ D.K₁)
    (hκ₂ : κ₂ ∈ D.K₂) (hinv : ∀ y ∈ D.Y₁, (κ₁ * κ₂) * y * (κ₁ * κ₂)⁻¹ = y⁻¹) :
    ∀ u ∈ D.X₁, κ₁ * u * κ₁⁻¹ = u⁻¹ := by
  intro u hu
  have hb : D.t * u⁻¹ * D.t⁻¹ ∈ D.X₂ := t_mem_X₂ D hs (D.X₁.inv_mem hu)
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = D.t * u⁻¹ * D.t⁻¹ := ⟨_, rfl⟩
  rw [← hbdef] at hb
  have hy : u * b ∈ D.Y₁ := by rw [hbdef]; exact Y₁_diag D h3 hu
  have h := hinv _ hy
  have huK : u ∈ D.K₁ := h3.X₁_le hu
  have hbK : b ∈ D.K₂ := X₂_le_K₂ D hs h3 hb
  have hub : u * b = b * u := X₁_X₂_comm D hs h3 u hu b hb
  have hκ₂u : κ₂ * u = u * κ₂ := (hs.comps.comm u huK κ₂ hκ₂).symm
  have hU' : κ₁ * u * κ₁⁻¹ ∈ D.K₁ := D.K₁.mul_mem (D.K₁.mul_mem hκ₁ huK) (D.K₁.inv_mem hκ₁)
  have hB' : κ₂ * b * κ₂⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hκ₂ hbK) (D.K₂.inv_mem hκ₂)
  have hκ₁B : κ₁ * (κ₂ * b * κ₂⁻¹) = (κ₂ * b * κ₂⁻¹) * κ₁ := hs.comps.comm κ₁ hκ₁ _ hB'
  have hexp : (κ₁ * κ₂) * (u * b) * (κ₁ * κ₂)⁻¹ = (κ₁ * u * κ₁⁻¹) * (κ₂ * b * κ₂⁻¹) := by
    calc (κ₁ * κ₂) * (u * b) * (κ₁ * κ₂)⁻¹ = κ₁ * ((κ₂ * u) * b * κ₂⁻¹) * κ₁⁻¹ := by group
      _ = κ₁ * (u * (κ₂ * b * κ₂⁻¹)) * κ₁⁻¹ := by rw [hκ₂u]; group
      _ = (κ₁ * u) * (κ₁⁻¹ * (κ₁ * (κ₂ * b * κ₂⁻¹)) * κ₁⁻¹ ) := by group
      _ = (κ₁ * u) * (κ₁⁻¹ * ((κ₂ * b * κ₂⁻¹) * κ₁) * κ₁⁻¹) := by rw [hκ₁B]
      _ = (κ₁ * u * κ₁⁻¹) * (κ₂ * b * κ₂⁻¹) := by group
  have hinvy : (u * b)⁻¹ = u⁻¹ * b⁻¹ := by
    rw [hub, mul_inv_rev]
  rw [hexp, hinvy] at h
  have hrel : u * (κ₁ * u * κ₁⁻¹) = b⁻¹ * (κ₂ * b * κ₂⁻¹)⁻¹ := by
    have : κ₁ * u * κ₁⁻¹ = u⁻¹ * b⁻¹ * (κ₂ * b * κ₂⁻¹)⁻¹ := by
      calc κ₁ * u * κ₁⁻¹ = (κ₁ * u * κ₁⁻¹) * (κ₂ * b * κ₂⁻¹) * (κ₂ * b * κ₂⁻¹)⁻¹ := by group
        _ = u⁻¹ * b⁻¹ * (κ₂ * b * κ₂⁻¹)⁻¹ := by rw [h]
    rw [this]; group
  have hmem : u * (κ₁ * u * κ₁⁻¹) ∈ D.K₁ ⊓ D.K₂ :=
    ⟨D.K₁.mul_mem huK hU', by rw [hrel]; exact D.K₂.mul_mem (D.K₂.inv_mem hbK) (D.K₂.inv_mem hB')⟩
  rw [hs.comps.inf_eq] at hmem
  rcases eq_one_or_z hs hmem with h' | h'
  · exact eq_inv_of_mul_eq_one_right h'
  · exfalso
    have hκz : κ₁ * u * κ₁⁻¹ = u⁻¹ * D.z := by
      calc κ₁ * u * κ₁⁻¹ = u⁻¹ * (u * (κ₁ * u * κ₁⁻¹)) := by group
        _ = u⁻¹ * D.z := by rw [h']
    have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
    have hp1 : u ^ D.p = 1 := h3.X₁_eab.2 u hu
    have hcomm : Commute u⁻¹ D.z := (show Commute u D.z from hs.comps.cz₁ huK).inv_left
    have hzz : D.z * D.z = 1 := z_mul_z D hs
    have hzp : D.z ^ D.p = D.z := by
      obtain ⟨j, hj⟩ := hpodd
      rw [hj, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
    have h5 : (κ₁ * u * κ₁⁻¹) ^ D.p = 1 := by rw [conj_pow, hp1]; group
    rw [hκz, hcomm.mul_pow, inv_pow, hp1, inv_one, one_mul, hzp] at h5
    exact z_ne_one D hs h5

theorem inv_X₁_false (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D)
    (hq3 : D.q % 4 = 3) {κ : G} (hκ : κ ∈ D.K₁) (hinv : ∀ u ∈ D.X₁, κ * u * κ⁻¹ = u⁻¹) : False := by
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, -, -⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ↥D.K₁, ε u₀ = sl2U (1 : F) := ⟨ε.symm (sl2U 1), by simp⟩
  have hu₀X : (u₀ : G) ∈ D.X₁ := (hE1 u₀).mpr (by
    rw [hu₀]; simp [SL2Root.mem_upperSub])
  have h := hinv _ hu₀X
  let κk : ↥D.K₁ := ⟨κ, hκ⟩
  have h' : κk * u₀ * κk⁻¹ = u₀⁻¹ := Subtype.ext h
  have h2 := congrArg ε h'
  rw [map_mul, map_mul, map_inv, map_inv, hu₀, sl2U_inv'] at h2
  obtain ⟨-, hsq⟩ := conj_sl2U_form h2
  have hsq' : IsSquare (-1 : F) := ⟨(ε κk).1 0 0, by rw [← sq]; exact hsq.symm⟩
  rw [FiniteField.isSquare_neg_one_iff] at hsq'
  apply hsq'
  rw [← Nat.card_eq_fintype_card, hFq]
  exact hq3

theorem two_elem_cen (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) (hq3 : D.q % 4 = 3) {g : G} (hgC₁ : g ∈ D.C₁)
    (hgz : g * D.z = D.z * g) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) : g ∈ zpowers D.z := by
  classical
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  have hgC : g ∈ Cz D.z := mem_centralizer_singleton_iff.mpr hgz
  have hti : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right htt
  have hKnorm : ∀ c ∈ D.C, ∀ x, x ∈ D.K ↔ c * x * c⁻¹ ∈ D.K := by
    intro c hcC x
    constructor
    · intro hx; exact hs.comps.conj_sup_mem hcC hx
    · intro hx
      have := hs.comps.conj_sup_mem (Subgroup.inv_mem _ hcC) hx
      have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rw [e] at this
      exact this
  have hKt : zpowers D.t ≤ normalizer (D.K : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    exact hKnorm D.t (t_mem_Cz hs) x
  have hS_le : ∀ s ∈ (D.S : Subgroup G), s ∈ D.K ⊔ zpowers D.t := by
    intro s hsS
    rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem
        (t_not_mem_K D hs) hs.syl.index s hsS with h | h
    · exact Subgroup.mem_sup_left h
    · have : s = (s * D.t) * D.t := by
        calc s = s * (D.t * D.t) := by rw [htt, mul_one]
          _ = (s * D.t) * D.t := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (mem_zpowers _))
  have hFN : ∀ y ∈ D.F, ∀ x ∈ D.K ⊔ zpowers D.t, y * x * y⁻¹ ∈ D.K ⊔ zpowers D.t := by
    intro y hy x hx
    obtain ⟨κ, hκ, τ, hτ, rfl⟩ := mem_sup_of_le_normalizer hKt hx
    have hyt : y * D.t = D.t * y := mem_centralizer_singleton_iff.mp (hc.F_eq hy)
    have hyτ : y * τ * y⁻¹ = τ := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hτ
      have hcomm : Commute y D.t := hyt
      rw [(hcomm.zpow_right j).eq]; group
    have hyκ : y * κ * y⁻¹ ∈ D.K := (hKnorm y (F_le_C hs hy) κ).mp hκ
    have e : y * (κ * τ) * y⁻¹ = (y * κ * y⁻¹) * τ := by
      calc y * (κ * τ) * y⁻¹ = (y * κ * y⁻¹) * (y * τ * y⁻¹) := by group
        _ = (y * κ * y⁻¹) * τ := by rw [hyτ]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyκ) (Subgroup.mem_sup_right hτ)
  obtain ⟨k, hk, s, hsS, y, hyF, hdec⟩ := hs.gen g hgC
  have hksN : k * s ∈ D.K ⊔ zpowers D.t :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (hS_le s hsS)
  have hgN : g ∈ D.K ⊔ zpowers D.t :=
    mem_of_mul_of_coprime_orders (D.K ⊔ zpowers D.t) hksN (hFN y hyF) hdec
      (pow_orderOf_eq_one y) hgm
      (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr (F_odd D.toSPLNot0 hyF)))
  obtain ⟨κ, hκK, τ, hτ, hgκτ⟩ := mem_sup_of_le_normalizer hKt hgN
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hτ
  have ht2 : D.t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rcases Int.even_or_odd' i with ⟨k', rfl | rfl⟩
  ·
    have h1' : D.t ^ (2 * k') = 1 := by rw [zpow_mul, ht2, one_zpow]
    rw [h1', mul_one] at hgκτ
    have hgK : g ∈ D.K := hgκτ ▸ hκK
    obtain ⟨hgK₁, hgK₂⟩ := K_normalizes D hs hgK
    obtain ⟨x, hxX, j, hg_eq⟩ := cen_z_of_normalizes D hs h1 h3 hgC hgK₁ hgK₂
      (Y₁_family D hs h3 hgC₁).1 (Y₁_family D hs h3 hgC₁).2
    have hxK : x ∈ D.K := X_le_K' D hs h3 hxX
    have hcom : Commute x (D.z ^ j) :=
      Commute.zpow_right (z_cen_K D hs x hxK).symm j
    have hxp : x ^ D.p = 1 := X_exp D hs h3 x hxX
    have hxa : x ^ (2 ^ m) ∈ zpowers D.z := by
      have h5 : x ^ (2 ^ m) * (D.z ^ j) ^ (2 ^ m) = 1 := by
        rw [← hcom.mul_pow, ← hg_eq]; exact hgm
      have : x ^ (2 ^ m) = ((D.z ^ j) ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h5
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.zpow_mem _ (mem_zpowers _) _) _)
    have hxz : x ∈ zpowers D.z :=
      mem_of_pow_mem_of_coprime (zpowers D.z)
        (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hpodd)) hxa hxp
    rw [hg_eq]
    exact Subgroup.mul_mem _ hxz (Subgroup.zpow_mem _ (mem_zpowers _) _)
  ·
    exfalso
    have h2 : D.t ^ (2 * k') = 1 := by rw [zpow_mul, ht2, one_zpow]
    have h3' : D.t ^ (2 * k' + 1) = D.t := by rw [zpow_add_one, h2, one_mul]
    rw [h3'] at hgκτ
    have hκeq : κ = g * D.t := by
      rw [hgκτ]
      calc κ = κ * (D.t * D.t) := by rw [htt, mul_one]
        _ = κ * D.t * D.t := by group
    have hκinv : ∀ y ∈ D.Y₁, κ * y * κ⁻¹ = y⁻¹ := by
      intro y hy
      have hcy : g * y⁻¹ = y⁻¹ * g := by
        have := (mem_C₁ D).mp hgC₁ y⁻¹ (D.Y₁.inv_mem hy)
        exact this.symm
      have hty : D.t * y * D.t⁻¹ = y⁻¹ := h3.Y₁_inv y hy
      rw [hκeq]
      calc g * D.t * y * (g * D.t)⁻¹ = g * (D.t * y * D.t⁻¹) * g⁻¹ := by group
        _ = g * y⁻¹ * g⁻¹ := by rw [hty]
        _ = y⁻¹ := by rw [hcy]; group
    have hκK : κ ∈ D.K := hκK
    obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hκ12⟩ := mem_sup_of_commute hs.comps.comm hκK
    have hinvc : ∀ y ∈ D.Y₁, (κ₁ * κ₂) * y * (κ₁ * κ₂)⁻¹ = y⁻¹ := by
      intro y hy; rw [← hκ12]; exact hκinv y hy
    have hX₁inv := comp_inverts D hs h3 hκ₁ hκ₂ hinvc
    exact inv_X₁_false D hs h1 h3 hq3 hκ₁ hX₁inv

theorem exists_V_minus (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) (hq3 : D.q % 4 = 3) :
    ∃ V : Subgroup G, V ≤ D.C₁ ∧ (∀ g ∈ D.C₁, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
      Odd (Nat.card ↥V) ∧ (∀ g ∈ D.C₁, Odd (orderOf g) → g ∈ V) ∧
      ∃ k : ℕ, Nat.card ↥D.C₁ = 2 ^ k * Nat.card ↥V := by
  classical
  have hzz := z_mul_z D hs
  have hzC₁ : D.z ∈ D.C₁ := z_mem_C₁ D hs h3
  have hzle : zpowers D.z ≤ D.C₁ := zpowers_le.mpr hzC₁
  have hz2 : IsPGroup 2 ↥(zpowers D.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs.syl.z_inv, pow_one])
  have hzcomm : ∀ s ∈ zpowers D.z, s * D.z = D.z * s := by
    intro s hs'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hs'
    exact ((Commute.refl D.z).zpow_left j).eq
  have hmax : ∀ S : Subgroup G, S ≤ D.C₁ → IsPGroup 2 ↥S → zpowers D.z ≤ S →
      S = zpowers D.z := by
    refine sylow2_of_isolated D.C₁ (zpowers D.z) D.z (1 : G) hzle hz2 (mem_zpowers _) hzz hzcomm
      ?_ ?_ ?_
    · intro S hSC hS2 hzS hSt
      refine le_antisymm (fun s hsS => ?_) hzS
      obtain ⟨m, hm⟩ := hS2 ⟨s, hsS⟩
      have hm' : s ^ (2 ^ m) = 1 := congrArg Subtype.val hm
      exact two_elem_cen D hs h1 hc h3 hq3 (hSC hsS) (hSt s hsS) hm'
    · intro s hsT hs2 hsz hs1
      exfalso
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hsT
      rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
      · apply hs1
        rw [zpow_mul, zpow_two, hzz, one_zpow]
      · apply hsz
        have h2 : D.z ^ (2 * k) = 1 := by rw [zpow_mul, zpow_two, hzz, one_zpow]
        rw [zpow_add_one, h2, one_mul]
    · intro h
      exact z_ne_one D hs (isConj_one_right.mp h)
  obtain ⟨V, hVC, hVn, hVodd, hVall, hVcard⟩ :=
    exists_normal_two_complement_of_order_two D.C₁ D.z hzC₁ hs.syl.z_inv hmax
  exact ⟨V, hVC, hVn, hVodd, hVall, 1, by rw [pow_one]; exact hVcard⟩

theorem l34_core (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2)
    (h3 : SPL3X D) : L34Concl D := by
  have hex : ∃ V : Subgroup G, V ≤ D.C₁ ∧ (∀ g ∈ D.C₁, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
      Odd (Nat.card ↥V) ∧ (∀ g ∈ D.C₁, Odd (orderOf g) → g ∈ V) ∧
      ∃ k : ℕ, Nat.card ↥D.C₁ = 2 ^ k * Nat.card ↥V := by
    by_cases hq1 : D.q % 4 = 1
    · exact exists_V_plus D hs h1 hc h3 hq1
    · have hq3 : D.q % 4 = 3 := by
        obtain ⟨k, hk⟩ := hs.odd_q
        omega
      exact exists_V_minus D hs h1 hc h3 hq3
  obtain ⟨V, hVC, hVn, hVodd, hVall, hVcard⟩ := hex
  have hcomm := comm_eq_Y₁ D hs h1 hc h3 V hVC hVn hVodd hVall
  exact ⟨V, hVC, ⟨fun n hn g => hVn g g.2 n hn⟩, hVodd, hVcard, hcomm⟩

end L34c

theorem splInL34 : SPLInL34 := by
  intro G _ _ _ D hs h1 hc _ h3 _
  exact l34_core D hs h1 hc h3

end CFSG.GH74.GLS.SP.Local
