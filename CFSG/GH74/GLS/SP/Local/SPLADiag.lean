module

public import CFSG.GH74.GLS.SP.Local.SPLWt3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SPLNot3.Y₀ (D : SPLNot3 G) : Subgroup G := centralizer ({D.t} : Set G) ⊓ D.X

section Diag

variable (D : SPLNot3 G)

@[expose] noncomputable def diagHom (hs : SPLSetup D.toSPLNot0) : ↥D.K₁ →* G where
  toFun k := (k : G) * (D.t * k * D.t⁻¹)
  map_one' := by simp
  map_mul' k k' := by
    have hc : (k' : G) * (D.t * (k : G) * D.t⁻¹) = (D.t * (k : G) * D.t⁻¹) * (k' : G) :=
      hs.comps.comm _ k'.2 _ (t_conj_K₁ D hs _ k.2)
    show (k : G) * k' * (D.t * ((k : G) * k') * D.t⁻¹) =
      ((k : G) * (D.t * k * D.t⁻¹)) * ((k' : G) * (D.t * k' * D.t⁻¹))
    have e1 : D.t * ((k : G) * k') * D.t⁻¹ = (D.t * k * D.t⁻¹) * (D.t * k' * D.t⁻¹) := by group
    rw [e1]
    calc (k : G) * k' * ((D.t * k * D.t⁻¹) * (D.t * k' * D.t⁻¹))
        = k * (k' * (D.t * k * D.t⁻¹)) * (D.t * k' * D.t⁻¹) := by group
      _ = k * ((D.t * k * D.t⁻¹) * k') * (D.t * k' * D.t⁻¹) := by rw [hc]
      _ = _ := by group

theorem diagHom_range_le (hs : SPLSetup D.toSPLNot0) :
    (diagHom D hs).range ≤ centralizer ({D.t} : Set G) ⊓ D.K := by
  rintro _ ⟨k, rfl⟩
  have htt := t_mul_t D hs
  have hu : D.t * (k : G) * D.t⁻¹ ∈ D.K₂ := t_conj_K₁ D hs _ k.2
  have hcomm : (k : G) * (D.t * (k : G) * D.t⁻¹) = (D.t * (k : G) * D.t⁻¹) * (k : G) :=
    hs.comps.comm _ k.2 _ hu
  refine ⟨?_, ?_⟩
  · show _ ∈ centralizer ({D.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    show (k : G) * (D.t * k * D.t⁻¹) * D.t = D.t * ((k : G) * (D.t * k * D.t⁻¹))
    have e : D.t * ((k : G) * (D.t * k * D.t⁻¹)) * D.t⁻¹ = (k : G) * (D.t * k * D.t⁻¹) := by
      have e2 : D.t * ((k : G) * (D.t * k * D.t⁻¹)) * D.t⁻¹ =
          (D.t * k * D.t⁻¹) * ((D.t * D.t) * k * (D.t * D.t)⁻¹) := by group
      rw [e2, htt]
      simp only [inv_one, mul_one, one_mul]
      exact hcomm.symm
    calc (k : G) * (D.t * k * D.t⁻¹) * D.t
        = (D.t * ((k : G) * (D.t * k * D.t⁻¹)) * D.t⁻¹) * D.t := by rw [e]
      _ = _ := by group
  · exact mul_mem (le_sup_left (a := D.K₁) (b := D.K₂) k.2) (le_sup_right (a := D.K₁) (b := D.K₂) hu)

theorem diagHom_range_perfect (hs : SPLSetup D.toSPLNot0) :
    ⁅(diagHom D hs).range, (diagHom D hs).range⁆ = (diagHom D hs).range := by
  have hperf : ⁅(⊤ : Subgroup ↥D.K₁), (⊤ : Subgroup ↥D.K₁)⁆ = ⊤ := by
    exact hs.comps.quasi₁.1.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

theorem diag_mem_I (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {k : G} (hk : k ∈ D.K₁) :
    k * (D.t * k * D.t⁻¹) ∈ D.I := by
  have h1 : (diagHom D hs).range ≤
      ⁅centralizer ({D.t} : Set G) ⊓ D.K, centralizer ({D.t} : Set G) ⊓ D.K⁆ := by
    calc (diagHom D hs).range = ⁅(diagHom D hs).range, (diagHom D hs).range⁆ :=
          (diagHom_range_perfect D hs).symm
      _ ≤ _ := Subgroup.commutator_mono (diagHom_range_le D hs) (diagHom_range_le D hs)
  rw [show D.I = D.toSPLNot2.I from rfl, hc.I_der]
  exact h1 ⟨⟨k, hk⟩, rfl⟩

omit [Finite G] in
theorem z_ne_one (hs : SPLSetup D.toSPLNot0) : D.z ≠ 1 := by
  intro h
  have := hs.syl.z_inv
  rw [show D.z = 1 from h, orderOf_one] at this
  exact absurd this (by norm_num)

omit [Finite G] in
theorem I_le_C (hc : SPL2Ct D.toSPLNot2) : D.I ≤ centralizer ({D.t} : Set G) ⊓ D.K := by
  rw [show D.I = D.toSPLNot2.I from rfl, hc.I_der]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

omit [Finite G] in
theorem I_le_K (hc : SPL2Ct D.toSPLNot2) : D.I ≤ D.K := fun _ hx => (I_le_C D hc hx).2

omit [Finite G] in
theorem I_le_Ct (hc : SPL2Ct D.toSPLNot2) : D.I ≤ D.Ct := fun _ hx => (I_le_C D hc hx).1

omit [Finite G] in
theorem z_cen_K (hs : SPLSetup D.toSPLNot0) : ∀ k ∈ D.K, D.z * k = k * D.z := by
  intro k hk
  have : D.K ≤ centralizer ({D.z} : Set G) :=
    sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hk))
      (fun k hk => mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ hk))
  exact (mem_centralizer_singleton_iff.mp (this hk)).symm

omit [Finite G] in
theorem z_cen_I (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∀ i ∈ D.I, D.z * i = i * D.z := fun i hi => z_cen_K D hs i (I_le_K D hc hi)

end Diag

section XPart

variable (D : SPLNot3 G)

theorem X₁_X₂_comm (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    ∀ a ∈ D.X₁, ∀ b ∈ D.X₂, a * b = b * a :=
  fun a ha b hb => hs.comps.comm a (h3.X₁_le ha) b (X₂_le_K₂ D hs h3 hb)

theorem X₁_inf_X₂' (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X₁ ⊓ D.X₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hK : x ∈ D.K₁ ⊓ D.K₂ := ⟨h3.X₁_le hx1, X₂_le_K₂ D hs h3 hx2⟩
  rw [hs.comps.inf_eq] at hK
  rcases eq_one_or_z hs hK with h | h
  · exact Subgroup.mem_bot.mpr h
  · exfalso
    subst h
    have hzz : D.z * D.z = 1 := z_mul_z D hs
    exact z_ne_one D hs (eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) (h3.X₁_eab.2 _ hx1)
      (inv_eq_of_mul_eq_one_right hzz))

theorem unique_decomp (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {a a' b b' : G} (ha : a ∈ D.X₁)
    (ha' : a' ∈ D.X₁) (hb : b ∈ D.X₂) (hb' : b' ∈ D.X₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hmem : a'⁻¹ * a ∈ D.X₁ ⊓ D.X₂ := by
    refine ⟨D.X₁.mul_mem (D.X₁.inv_mem ha') ha, ?_⟩
    have e : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [e]; exact D.X₂.mul_mem hb' (D.X₂.inv_mem hb)
  rw [X₁_inf_X₂' D hs h3] at hmem
  have h1 : a'⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
  have h2 : a = a' := (inv_mul_eq_one.mp h1).symm
  refine ⟨h2, ?_⟩
  subst h2
  exact mul_left_cancel h

omit [Finite G] in
theorem t_mem_X₂ (hs : SPLSetup D.toSPLNot0) {a : G} (ha : a ∈ D.X₁) :
    D.t * a * D.t⁻¹ ∈ D.X₂ := by
  show _ ∈ conjBy D.t D.X₁
  rw [mem_conjBy_iff]
  have htt := t_mul_t D hs
  have e : D.t * (D.t * a * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * a * (D.t * D.t)⁻¹ := by group
  rw [e, htt]; simpa using ha

omit [Finite G] in
theorem t_mem_X₁ {b : G} (hb : b ∈ D.X₂) : D.t * b * D.t⁻¹ ∈ D.X₁ := mem_conjBy_iff.mp hb

theorem diag_mem_Y₀ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {a : G} (ha : a ∈ D.X₁) :
    a * (D.t * a * D.t⁻¹) ∈ D.Y₀ := by
  have htt := t_mul_t D hs
  have hX₂ := t_mem_X₂ D hs ha
  refine ⟨?_, mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hX₂)⟩
  show _ ∈ centralizer ({D.t} : Set G)
  rw [mem_centralizer_singleton_iff]
  have hcomm : a * (D.t * a * D.t⁻¹) = (D.t * a * D.t⁻¹) * a := X₁_X₂_comm D hs h3 a ha _ hX₂
  have e : D.t * (a * (D.t * a * D.t⁻¹)) * D.t⁻¹ = a * (D.t * a * D.t⁻¹) := by
    have e2 : D.t * (a * (D.t * a * D.t⁻¹)) * D.t⁻¹ =
        (D.t * a * D.t⁻¹) * ((D.t * D.t) * a * (D.t * D.t)⁻¹) := by group
    rw [e2, htt]
    simp only [inv_one, mul_one, one_mul]
    exact hcomm.symm
  calc a * (D.t * a * D.t⁻¹) * D.t
      = (D.t * (a * (D.t * a * D.t⁻¹)) * D.t⁻¹) * D.t := by rw [e]
    _ = _ := by group

theorem Y₀_decomp (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {y : G} (hy : y ∈ D.Y₀) :
    ∃ a ∈ D.X₁, y = a * (D.t * a * D.t⁻¹) := by
  have htt := t_mul_t D hs
  have hyc : D.t * y * D.t⁻¹ = y := by
    have := mem_centralizer_singleton_iff.mp hy.1
    calc D.t * y * D.t⁻¹ = (D.t * y) * D.t⁻¹ := rfl
      _ = (y * D.t) * D.t⁻¹ := by rw [this]
      _ = y := by group
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute (X₁_X₂_comm D hs h3) hy.2
  have ha2 : D.t * a * D.t⁻¹ ∈ D.X₂ := t_mem_X₂ D hs ha
  have hb1 : D.t * b * D.t⁻¹ ∈ D.X₁ := t_mem_X₁ D hb
  have e1 : D.t * y * D.t⁻¹ = (D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹) := by rw [hab]; group
  have e2 : y = (D.t * b * D.t⁻¹) * (D.t * a * D.t⁻¹) := by
    rw [← hyc, e1]
    exact (X₁_X₂_comm D hs h3 _ hb1 _ ha2).symm
  have hu := unique_decomp D hs h3 ha hb1 hb ha2 (hab.symm.trans e2)
  refine ⟨a, ha, ?_⟩
  rw [hab, hu.2]

theorem Y₀_le_I (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    D.Y₀ ≤ D.I := fun y hy => by
  obtain ⟨a, ha, rfl⟩ := Y₀_decomp D hs h3 hy
  exact diag_mem_I D hs hc (h3.X₁_le ha)

theorem Y₀_card (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : Nat.card ↥D.Y₀ = D.q := by
  have hbij : Function.Bijective (fun a : ↥D.X₁ =>
      (⟨(a : G) * (D.t * a * D.t⁻¹), diag_mem_Y₀ D hs h3 a.2⟩ : ↥D.Y₀)) := by
    constructor
    · intro a a' h
      have h' : (a : G) * (D.t * a * D.t⁻¹) = (a' : G) * (D.t * a' * D.t⁻¹) := congrArg Subtype.val h
      exact Subtype.ext (unique_decomp D hs h3 a.2 a'.2 (t_mem_X₂ D hs a.2) (t_mem_X₂ D hs a'.2) h').1
    · intro y
      obtain ⟨a, ha, hya⟩ := Y₀_decomp D hs h3 y.2
      exact ⟨⟨a, ha⟩, Subtype.ext hya.symm⟩
  rw [← h3.X₁_card]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

end XPart

section H0W

variable (D : SPLNot3 G)

theorem H₀_le_I (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2) :
    D.H₀ ≤ D.I := by
  show zpowers (D.h₁ * D.h₂) ≤ D.I
  rw [zpowers_le]
  exact diag_mem_I D hs hc h1.h₁_mem

theorem w_mem_I (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2) :
    D.w ∈ D.I := diag_mem_I D hs hc h1.w₁_mem

theorem w_mul_w (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) : D.w * D.w = 1 := by
  have hc := w₁_w₂_comm D hs h1
  have e : D.w * D.w = (D.w₁ * D.w₁) * (D.w₂ * D.w₂) := by
    show (D.w₁ * D.w₂) * (D.w₁ * D.w₂) = _
    calc (D.w₁ * D.w₂) * (D.w₁ * D.w₂) = D.w₁ * (D.w₂ * D.w₁) * D.w₂ := by group
      _ = D.w₁ * (D.w₁ * D.w₂) * D.w₂ := by rw [← hc]
      _ = _ := by group
  rw [e, h1.w₁_sq, w₂_sq D hs h1]
  exact z_mul_z D hs

theorem w_inv_h₁h₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w * (D.h₁ * D.h₂) * D.w⁻¹ = (D.h₁ * D.h₂)⁻¹ := by
  have e1 : D.w₁ * D.h₁ * D.w₁⁻¹ = D.h₁⁻¹ := h1.w₁_inv D.h₁ (mem_zpowers _)
  have e2 : D.w₂ * D.h₂ * D.w₂⁻¹ = D.h₂⁻¹ := by
    show (D.t * D.w₁ * D.t⁻¹) * (D.t * D.h₁ * D.t⁻¹) * (D.t * D.w₁ * D.t⁻¹)⁻¹ = (D.t * D.h₁ * D.t⁻¹)⁻¹
    have : (D.t * D.w₁ * D.t⁻¹) * (D.t * D.h₁ * D.t⁻¹) * (D.t * D.w₁ * D.t⁻¹)⁻¹ =
        D.t * (D.w₁ * D.h₁ * D.w₁⁻¹) * D.t⁻¹ := by group
    rw [this, e1]; group
  have e3 : D.w₁ * D.h₂ = D.h₂ * D.w₁ := hs.comps.comm _ h1.w₁_mem _ (h₂_mem D hs h1)
  have e4 : D.h₁ * D.w₂ = D.w₂ * D.h₁ := hs.comps.comm _ (h1.h₁_mem) _ (w₂_mem_K₂ D hs h1)
  have e5 : D.h₁ * D.h₂ = D.h₂ * D.h₁ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  have c1 : D.w₂ * D.h₁ * D.w₂⁻¹ = D.h₁ := by rw [← e4]; group
  have c2 : D.w₁ * D.h₂⁻¹ * D.w₁⁻¹ = D.h₂⁻¹ := by
    have : D.w₁ * D.h₂⁻¹ = D.h₂⁻¹ * D.w₁ := by
      calc D.w₁ * D.h₂⁻¹ = D.h₂⁻¹ * (D.h₂ * D.w₁) * D.h₂⁻¹ := by group
        _ = D.h₂⁻¹ * (D.w₁ * D.h₂) * D.h₂⁻¹ := by rw [← e3]
        _ = D.h₂⁻¹ * D.w₁ := by group
    rw [this]; group
  calc D.w * (D.h₁ * D.h₂) * D.w⁻¹
      = D.w₁ * ((D.w₂ * D.h₁ * D.w₂⁻¹) * (D.w₂ * D.h₂ * D.w₂⁻¹)) * D.w₁⁻¹ := by
        show (D.w₁ * D.w₂) * (D.h₁ * D.h₂) * (D.w₁ * D.w₂)⁻¹ = _
        group
    _ = D.w₁ * (D.h₁ * D.h₂⁻¹) * D.w₁⁻¹ := by rw [c1, e2]
    _ = (D.w₁ * D.h₁ * D.w₁⁻¹) * (D.w₁ * D.h₂⁻¹ * D.w₁⁻¹) := by group
    _ = D.h₁⁻¹ * D.h₂⁻¹ := by rw [e1, c2]
    _ = (D.h₁ * D.h₂)⁻¹ := by
        rw [mul_inv_rev]
        have : D.h₂⁻¹ * D.h₁⁻¹ = D.h₁⁻¹ * D.h₂⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, e5]
        rw [this]

theorem w_inv_H₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H₀, D.w * h * D.w⁻¹ = h⁻¹ := by
  intro h hh
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
  rw [← conj_zpow, w_inv_h₁h₂ D hs h1, inv_zpow', zpow_neg]

theorem t_cen_h₁h₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.t * (D.h₁ * D.h₂) * D.t⁻¹ = D.h₁ * D.h₂ := by
  have htt := t_mul_t D hs
  have e5 : D.h₁ * D.h₂ = D.h₂ * D.h₁ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  have : D.t * (D.h₁ * D.h₂) * D.t⁻¹ = D.h₂ * ((D.t * D.t) * D.h₁ * (D.t * D.t)⁻¹) := by
    show D.t * (D.h₁ * (D.t * D.h₁ * D.t⁻¹)) * D.t⁻¹ =
      (D.t * D.h₁ * D.t⁻¹) * ((D.t * D.t) * D.h₁ * (D.t * D.t)⁻¹)
    group
  rw [this, htt]
  simp only [inv_one, mul_one, one_mul]
  exact e5.symm

theorem t_cen_H₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H₀, D.t * h * D.t⁻¹ = h := by
  intro h hh
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
  rw [← conj_zpow, t_cen_h₁h₂ D hs h1]

theorem w_not_mem_H₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) : D.w ∉ D.H₀ := by
  intro hw
  have hwH : D.w ∈ D.H := SPLNot1.H₀_le_H D.toSPLNot1 hw
  have hcomm := H₁_H₂_comm D hs h1
  obtain ⟨a₁, ha₁, a₂, ha₂, hw12⟩ := mem_sup_of_commute hcomm hwH
  have h1K : a₁ ∈ D.K₁ := H₁_le_K₁ D h1 ha₁
  have h2K : a₂ ∈ D.K₂ := H₂_le_K₂ D hs h1 ha₂
  have hK2 : D.w₂ ∈ D.K₂ := w₂_mem_K₂ D hs h1
  have hmem : a₁⁻¹ * D.w₁ ∈ D.K₁ ⊓ D.K₂ := by
    refine ⟨D.K₁.mul_mem (D.K₁.inv_mem h1K) h1.w₁_mem, ?_⟩
    have e : a₁⁻¹ * D.w₁ = a₂ * D.w₂⁻¹ := by
      have : D.w₁ * D.w₂ = a₁ * a₂ := hw12
      calc a₁⁻¹ * D.w₁ = a₁⁻¹ * (D.w₁ * D.w₂) * D.w₂⁻¹ := by group
        _ = a₁⁻¹ * (a₁ * a₂) * D.w₂⁻¹ := by rw [this]
        _ = a₂ * D.w₂⁻¹ := by group
    rw [e]; exact D.K₂.mul_mem h2K (D.K₂.inv_mem hK2)
  rw [hs.comps.inf_eq] at hmem
  have hz : D.z ∈ D.H₁ := z_mem_H₁ D h1
  have hw1 : D.w₁ ∈ D.H₁ := by
    have : D.w₁ = a₁ * (a₁⁻¹ * D.w₁) := by group
    rw [this]
    exact D.H₁.mul_mem ha₁ (by
      rcases eq_one_or_z hs hmem with h | h
      · rw [h]; exact D.H₁.one_mem
      · rw [h]; exact hz)
  have hinv := h1.w₁_inv D.w₁ hw1
  have : D.w₁ * D.w₁ = 1 := by
    have e : D.w₁ * D.w₁ * D.w₁⁻¹ = D.w₁⁻¹ := hinv
    calc D.w₁ * D.w₁ = D.w₁ * D.w₁ * D.w₁⁻¹ * D.w₁ := by group
      _ = D.w₁⁻¹ * D.w₁ := by rw [e]
      _ = 1 := by group
  rw [h1.w₁_sq] at this
  exact z_ne_one D hs this

theorem H₀_norm_Y₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) :
    ∀ h ∈ D.H₀, ∀ y ∈ D.Y₀, h * y * h⁻¹ ∈ D.Y₀ := by
  intro h hh y hy
  obtain ⟨a, ha, rfl⟩ := Y₀_decomp D hs h3 hy
  have hha : h * a * h⁻¹ ∈ D.X₁ := h3.H_X₁ h (SPLNot1.H₀_le_H D.toSPLNot1 hh) a ha
  have e : h * (a * (D.t * a * D.t⁻¹)) * h⁻¹ =
      (h * a * h⁻¹) * (D.t * (h * a * h⁻¹) * D.t⁻¹) := by
    have hth : D.t * h * D.t⁻¹ = h := t_cen_H₀ D hs h1 h hh
    have : D.t * (h * a * h⁻¹) * D.t⁻¹ = h * (D.t * a * D.t⁻¹) * h⁻¹ := by
      calc D.t * (h * a * h⁻¹) * D.t⁻¹
          = (D.t * h * D.t⁻¹) * (D.t * a * D.t⁻¹) * (D.t * h⁻¹ * D.t⁻¹) := by group
        _ = h * (D.t * a * D.t⁻¹) * h⁻¹ := by
          rw [hth]
          have : D.t * h⁻¹ * D.t⁻¹ = h⁻¹ := by
            have := congrArg (fun x => x⁻¹) hth
            simpa [mul_assoc] using this
          rw [this]
    rw [this]; group
  rw [e]
  exact diag_mem_Y₀ D hs h3 hha

end H0W

end CFSG.GH74.GLS.SP.Local
