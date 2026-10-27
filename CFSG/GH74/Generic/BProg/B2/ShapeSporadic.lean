module

public import CFSG.GH74.Generic.BProg.B2.ShapeOrders
public import CFSG.GH74.Generic.S1.KL5LyRee
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.SmallOddCore.McLAut

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace ShapeSporadic

theorem card_dvd_factorial {k : ℕ} (G : Subgroup (Equiv.Perm (Fin k))) :
    Nat.card ↥G ∣ Nat.factorial k := by
  have h1 : Nat.card ↥G ∣ Nat.card (Equiv.Perm (Fin k)) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (Equiv.Perm (Fin k)) = Nat.factorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rwa [h2] at h1

theorem mem_of_inner_eq_top {N X : Type} [Group N] [Group X] {H : Subgroup N} [H.Normal]
    (ψ : ↥H ≃* X) (hX : inner X = ⊤) (hf : ∀ n : N, (∀ x ∈ H, n * x = x * n) → n = 1) (t : N) :
    t ∈ H := by
  have hβ : MulAut.congr ψ (MulAut.conjNormal t) ∈ inner X := by rw [hX]; trivial
  obtain ⟨g, hg⟩ := hβ
  set h₀ : ↥H := ψ.symm g with hh₀
  have key : ∀ x : ↥H, (h₀ : N) * x * (h₀ : N)⁻¹ = t * x * t⁻¹ := by
    intro x
    have h1 := congrArg (fun α : MulAut X => α (ψ x)) hg
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    have h2 : h₀ * x * h₀⁻¹ = MulAut.conjNormal t x := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, hh₀, MulEquiv.apply_symm_apply, h1]
    have h3 := congrArg Subtype.val h2
    simpa [MulAut.conjNormal_apply] using h3
  have hcomm : ∀ x ∈ H, (h₀ : N)⁻¹ * t * x = x * ((h₀ : N)⁻¹ * t) := by
    intro x hx
    calc (h₀ : N)⁻¹ * t * x = (h₀ : N)⁻¹ * (t * x * t⁻¹) * t := by group
      _ = (h₀ : N)⁻¹ * ((h₀ : N) * x * (h₀ : N)⁻¹) * t := by rw [← key ⟨x, hx⟩]
      _ = x * ((h₀ : N)⁻¹ * t) := by group
  have h1 := hf _ hcomm
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact h₀.2

theorem card_centralizer_ly {N : Type} [Group N] {H : Subgroup N} (hn : H.Normal)
    (hf : ∀ n : N, (∀ x ∈ H, n * x = x * n) → n = 1) {t : N} (ht : orderOf t = 2)
    (he : NativeSporadic.IsSporadic ↥H .Ly) :
    Nat.card ↥(H ⊓ centralizer ({t} : Set N)) = 39916800 := by
  have := hn
  obtain ⟨ψ⟩ := he
  have htH : t ∈ H := mem_of_inner_eq_top (X := NativeSporadic.Ly) ψ
    CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput hf t
  have h1 := CFSG.GH74.Generic.S1.kl5_card_centralizer_ly (S := ↥H) ⟨ψ⟩ (y := ⟨t, htH⟩)
    (by rw [← ht]; exact Subgroup.orderOf_mk t htH)
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_subtype H ⟨t, htH⟩] at h1
  exact h1

section McL

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore

theorem mcl_card_centralizer
    {τ : Equiv.Perm (Fin 275)} (hτ : τ ∈ mclR) (h2 : orderOf τ = 2) :
    Nat.card ↥(mclP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 275)))) = 40320 ∨
      Nat.card ↥(mclP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 275)))) = 7920 := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hτg⟩ := hcover τ hτ h2
  obtain ⟨-, -, -, -, hcard, -⟩ := hrows r hr
  have hcent : r.centOrder = 40320 ∨ r.centOrder = 7920 := by
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        mclRows.map (fun r => (r.outer, r.classSize, r.centOrder)) :=
      List.mem_map_of_mem hr
    rw [hmap] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have : Nat.card ↥(mclP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 275)))) = r.centOrder := by
    rw [hτg, inf_centralizer_conj mclP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcard]
  rw [this]
  exact hcent

theorem card_centralizer_mcl {N : Type} [Group N] {H : Subgroup N} (hn : H.Normal)
    (hf : ∀ n : N, (∀ x ∈ H, n * x = x * n) → n = 1) {t : N} (ht : orderOf t = 2)
    (he : NativeSporadic.IsSporadic ↥H .McL) :
    Nat.card ↥(H ⊓ centralizer ({t} : Set N)) = 40320 ∨
      Nat.card ↥(H ⊓ centralizer ({t} : Set N)) = 7920 := by
  have := hn
  obtain ⟨ψ⟩ := he
  have hC : centralizer (H : Set N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_centralizer_iff] at hx
    exact hf x (fun y hy => (hx y hy).symm)
  let θ : ↥H ≃* ↥mclP := ψ.trans mclPermEquiv
  have hM : AutModel mclP mclR := mcl_autModel
  have hinj := hM.embed_injective H θ hC
  have hτ : orderOf (hM.embed H θ t) = 2 := by rw [orderOf_injective _ hinj, ht]
  rw [Nat.card_congr (hM.centralizerEquiv H θ hC t).toEquiv]
  exact mcl_card_centralizer (hM.embed_mem H θ t) hτ

end McL

end ShapeSporadic

section Certified


theorem ShapeInCent.false_of_dvd_M0 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) {m : ℕ}
    (hdvd : Nat.card ↥(H ⊓ centralizer ({t} : Set N)) ∣ m)
    (hm : m ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 17 * 19 * 23) (hj : ¬ 7 ∣ m ∨ ¬ 19 ∣ m) :
    False := by
  obtain ⟨Kt, _, hQ, hd⟩ := h.exists_shape_card_dvd hdvd
  refine ShapeOrders.not_dvd_of_qShapeNS hQ (ShapeOrders.smallOrder_of_dvd_M0 hm) ?_ hd
  rintro ⟨h7, h19⟩
  rcases hj with hj | hj
  exacts [hj h7, hj h19]

theorem not_M11_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .M11 := by
  rintro ⟨e⟩
  have h1 : Nat.card ↥H ∣ Nat.factorial 11 := by
    rw [Nat.card_congr e.toEquiv]
    exact ShapeSporadic.card_dvd_factorial NativeSporadic.M11
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1) (by decide)
    (Or.inr (by decide))

theorem not_M12_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .M12 := by
  rintro ⟨e⟩
  have h1 : Nat.card ↥H ∣ Nat.factorial 12 := by
    rw [Nat.card_congr e.toEquiv]
    exact ShapeSporadic.card_dvd_factorial NativeSporadic.M12
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1) (by decide)
    (Or.inr (by decide))

theorem not_M22_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .M22 := by
  intro he
  have h1 := card_of_isSporadic_M22 he
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1.dvd) (by decide)
    (Or.inr (by decide))

theorem not_M23_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .M23 := by
  intro he
  have h1 := card_of_isSporadic_M23 he
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1.dvd) (by decide)
    (Or.inr (by decide))

theorem not_J1_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .J1 := by
  intro he
  have hH : Nat.card ↥H = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := card_of_isSporadic_J1 he
  have hCH : Nat.card ↥(H ⊓ centralizer ({t} : Set N)) ∣ Nat.card ↥H :=
    Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨Kt, _, hQ, hd⟩ := h.exists_shape_card_dvd (m := Nat.card ↥(H ⊓ centralizer ({t} : Set N)))
    dvd_rfl
  have hsmall : ShapeOrders.SmallOrder (Nat.card ↥H) :=
    ShapeOrders.smallOrder_of_dvd_M0 (by rw [hH]; decide)
  rcases hQ with h1 | h3 | h4 | h5
  · exact ShapeOrders.not_dvd_of_qShape13 (Or.inl h1) hsmall (hd.trans hCH)
  · exact ShapeOrders.not_dvd_of_qShape13 (Or.inr h3) hsmall (hd.trans hCH)
  · exact ShapeOrders.not_dvd_of_qShape4 h4 hsmall (hd.trans hCH)
  · have hK : Nat.card Kt = Nat.card ↥H := by rw [ShapeOrders.qShape5_facts h5, hH]; norm_num
    have hle : H ⊓ centralizer ({t} : Set N) ≤ H := inf_le_left
    have heq : H ⊓ centralizer ({t} : Set N) = H :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [← hK]
        exact Nat.le_of_dvd Nat.card_pos hd)
    have htc : ∀ x ∈ H, x * t = t * x := fun x hx => by
      have hx' : x ∈ H ⊓ centralizer ({t} : Set N) := by rw [heq]; exact hx
      exact Subgroup.mem_centralizer_singleton_iff.1 (mem_inf.1 hx').2
    have ht1 : t = 1 := h.faithful t (fun x hx => (htc x hx).symm)
    have := h.inv
    rw [ht1, orderOf_one] at this
    exact absurd this (by norm_num)

theorem not_J2_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .J2 := by
  intro he
  have h1 := card_of_isSporadic_J2 he
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1.dvd) (by decide)
    (Or.inr (by decide))

theorem not_J3_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .J3 := by
  intro he
  have h1 := card_of_isSporadic_J3 he
  exact h.false_of_dvd_M0 ((Subgroup.card_dvd_of_le inf_le_left).trans h1.dvd) (by decide)
    (Or.inl (by decide))

theorem not_McL_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .McL := by
  intro he
  rcases ShapeSporadic.card_centralizer_mcl h.normal h.faithful h.inv he with h1 | h1
  · exact h.false_of_dvd_M0 h1.dvd (by decide) (Or.inr (by decide))
  · exact h.false_of_dvd_M0 h1.dvd (by decide) (Or.inr (by decide))

theorem not_Ly_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) : ¬ NativeSporadic.IsSporadic ↥H .Ly := by
  intro he
  have h1 := ShapeSporadic.card_centralizer_ly h.normal h.faithful h.inv he
  exact h.false_of_dvd_M0 h1.dvd (by decide) (Or.inr (by decide))

end Certified

theorem not_spor_of_shapeInCent
    {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (h : ShapeInCent H t L) (s : TauCeti.SporadicName)
    (hs : s ∈ ({.M11, .M12, .M22, .M23, .J1, .J2, .J3, .McL, .Ly} : Finset TauCeti.SporadicName)) :
    ¬ NativeSporadic.IsSporadic ↥H s := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_M11_of_shapeInCent h
  · exact not_M12_of_shapeInCent h
  · exact not_M22_of_shapeInCent h
  · exact not_M23_of_shapeInCent h
  · exact not_J1_of_shapeInCent h
  · exact not_J2_of_shapeInCent h
  · exact not_J3_of_shapeInCent h
  · exact not_McL_of_shapeInCent h
  · exact not_Ly_of_shapeInCent h

theorem ofLieType_of_shapeInCent
    {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (h : ShapeInCent H t L)
    (htri : CFSG.GH74.Generic.OfLieType ↥H ∨
      (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (↥H ≃* alternatingGroup (Fin n))) ∨
      (∃ s : TauCeti.SporadicName, s ∈ ({.M11, .M12, .M22, .M23, .J1, .J2, .J3, .McL, .Ly} :
        Finset TauCeti.SporadicName) ∧ NativeSporadic.IsSporadic ↥H s)) :
    CFSG.GH74.Generic.OfLieType ↥H := by
  rcases htri with hL | ⟨n, -, hn, e⟩ | ⟨s, hs, hsp⟩
  · exact hL
  · exact absurd e (not_alt_of_shapeInCent h n hn)
  · exact absurd hsp (not_spor_of_shapeInCent h s hs)

end CFSG.GH74.Generic.BProg.B2
