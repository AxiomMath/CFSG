module

public import CFSG.GH74.GLS.SP.Local.SPLGlue

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section BruhatCore

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem w₂_conj_mem_H (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) {u : G} (hu : u ∈ D.H) :
    D.w₂⁻¹ * u * D.w₂ ∈ D.H := by
  have htinv := t_inv D hs
  have e : D.w₂⁻¹ * u * D.w₂ =
      D.t * (D.w₁⁻¹ * (D.t⁻¹ * u * D.t) * D.w₁) * D.t⁻¹ := by
    show (D.t * D.w₁ * D.t⁻¹)⁻¹ * u * (D.t * D.w₁ * D.t⁻¹) = _
    group
  rw [e]
  refine t_norm_H D hs h1 _ (w₁_inv_norm_H D hs h1 _ ?_)
  have := t_norm_H D hs h1 u hu
  rw [htinv] at this ⊢
  exact this

theorem n_mem_tH (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    {a : G} (haz : a⁻¹ * D.z * a = D.z * D.t)
    (haw : ∃ u ∈ D.H, a⁻¹ * D.w * a = u * D.w) :
    ∃ δ ∈ D.H, (a * D.w₁)⁻¹ * (D.z * D.w) * (a * D.w₁) = D.t * δ := by
  obtain ⟨u, hu, hauw⟩ := haw
  have hcomm := w₁_w₂_comm D hs h1
  have htt := t_mul_t D hs
  have htinv := t_inv D hs
  have hz2 := z_mul_z D hs
  have hzt := t_comm_z D hs
  have hzu : D.z * u = u * D.z :=
    H_comm D hs h1 D.z (z_mem_H D h1) u hu
  refine ⟨D.w₂⁻¹ * u * D.w₂, w₂_conj_mem_H D hs h1 hu, ?_⟩
  have hw₁₂ : D.w₁ * D.w₂ = D.w₂ * D.w₁ := hcomm
  have hww : D.w * D.w₁ = D.z * D.w₂ := by
    show D.w₁ * D.w₂ * D.w₁ = D.z * D.w₂
    calc D.w₁ * D.w₂ * D.w₁ = D.w₁ * (D.w₂ * D.w₁) := by group
      _ = D.w₁ * (D.w₁ * D.w₂) := by rw [← hw₁₂]
      _ = (D.w₁ * D.w₁) * D.w₂ := by group
      _ = D.z * D.w₂ := by rw [h1.w₁_sq]
  have e1 : (a * D.w₁)⁻¹ * (D.z * D.w) * (a * D.w₁) =
      D.w₁⁻¹ * ((a⁻¹ * D.z * a) * (a⁻¹ * D.w * a)) * D.w₁ := by group
  rw [e1, haz, hauw]
  have e2 : D.w₁⁻¹ * (D.z * D.t * (u * D.w)) * D.w₁ =
      D.w₁⁻¹ * (D.z * D.t * u * (D.w * D.w₁)) := by group
  rw [e2, hww]
  have e3 : D.z * D.t * u * (D.z * D.w₂) = D.t * u * D.w₂ := by
    calc D.z * D.t * u * (D.z * D.w₂) = D.z * (D.t * u * D.z) * D.w₂ := by group
      _ = D.z * (D.t * (u * D.z)) * D.w₂ := by group
      _ = D.z * (D.t * (D.z * u)) * D.w₂ := by rw [← hzu]
      _ = D.z * ((D.t * D.z) * u) * D.w₂ := by group
      _ = D.z * ((D.z * D.t) * u) * D.w₂ := by rw [hzt]
      _ = (D.z * D.z) * D.t * u * D.w₂ := by group
      _ = D.t * u * D.w₂ := by rw [hz2]; group
  rw [e3]
  have e4 : D.w₁⁻¹ * (D.t * u * D.w₂) = (D.w₁⁻¹ * D.t * D.w₂) * (D.w₂⁻¹ * u * D.w₂) := by group
  rw [e4]
  have e5 : D.w₁⁻¹ * D.t * D.w₂ = D.t := by
    show D.w₁⁻¹ * D.t * (D.t * D.w₁ * D.t⁻¹) = D.t
    calc D.w₁⁻¹ * D.t * (D.t * D.w₁ * D.t⁻¹) = D.w₁⁻¹ * (D.t * D.t) * D.w₁ * D.t⁻¹ := by group
      _ = D.t⁻¹ := by rw [htt]; group
      _ = D.t := htinv
  rw [e5]

end BruhatCore

section Transfer

variable {G : Type} [Group G]

theorem conjBy_conj_eq (g m : G) (Y : Subgroup G) :
    conjBy (g⁻¹ * m * g) (conjBy g Y) = conjBy g (conjBy m Y) := by
  rw [conjBy_conjBy, conjBy_conjBy]
  congr 1
  group

theorem bruhat_transfer {H Y B₁ X₄ : Subgroup G} {g m t δ : G} (hX₄ : X₄ = conjBy g Y)
    (hδ : δ ∈ H) (hn : g⁻¹ * m * g = t * δ) (htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    (hHX : ∀ h ∈ H, ∀ x ∈ X₄, h * x * h⁻¹ ∈ X₄)
    (hBr : ∀ y ∈ conjBy m Y, y ≠ 1 → y ∈ (B₁ : Set G) * {m} * (B₁ : Set G))
    (hB₁ : ∀ b ∈ B₁, g⁻¹ * b * g ∈ (X₄ : Set G) * (H : Set G)) :
    ∀ y ∈ conjBy t X₄, y ≠ 1 → y ∈ (X₄ : Set G) * (H : Set G) * {t} * (X₄ : Set G) := by
  have hnorm : ∀ h ∈ H, ∀ x ∈ conjBy t X₄, h * x * h⁻¹ ∈ conjBy t X₄ := by
    intro h hh x hx
    rw [mem_conjBy_iff] at hx ⊢
    have e : t * (h * x * h⁻¹) * t⁻¹ = (t * h * t⁻¹) * (t * x * t⁻¹) * (t * h * t⁻¹)⁻¹ := by group
    rw [e]
    exact hHX _ (htH h hh) _ hx
  have hC : conjBy t X₄ = conjBy g (conjBy m Y) := by
    have h1 : conjBy (g⁻¹ * m * g) X₄ = conjBy g (conjBy m Y) := by
      rw [hX₄]; exact conjBy_conj_eq g m Y
    rw [← h1, hn, ← conjBy_conjBy]
    exact (conjBy_eq_of_mem hnorm hδ).symm
  intro y hy hy1
  rw [hC, mem_conjBy_iff] at hy
  have hy' : g * y * g⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, h]; group
  obtain ⟨_, ⟨b₁, hb₁, m', hm', rfl⟩, b₂, hb₂, hy2⟩ := (hBr _ hy hy')
  have hm : m' = m := hm'
  simp only [hm] at hy2
  have hy3 : y = (g⁻¹ * b₁ * g) * (g⁻¹ * m * g) * (g⁻¹ * b₂ * g) := by
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, ← hy2]; group
  obtain ⟨x₁, hx₁, k₁, hk₁, hc₁⟩ := hB₁ b₁ hb₁
  obtain ⟨x₂, hx₂, k₂, hk₂, hc₂⟩ := hB₁ b₂ hb₂
  rw [← hc₁, hn, ← hc₂] at hy3
  have hk₃ : δ * k₂ ∈ H := H.mul_mem hδ hk₂
  have hx₂' : δ * x₂ * δ⁻¹ ∈ X₄ := hHX δ hδ x₂ hx₂
  have hx₂'' : (δ * k₂)⁻¹ * (δ * x₂ * δ⁻¹) * (δ * k₂) ∈ X₄ := by
    have := hHX (δ * k₂)⁻¹ (H.inv_mem hk₃) _ hx₂'
    simpa using this
  have hκ : k₁ * (t * (δ * k₂) * t⁻¹) ∈ H := H.mul_mem hk₁ (htH _ hk₃)
  refine ⟨x₁ * (k₁ * (t * (δ * k₂) * t⁻¹)) * t, ⟨x₁ * (k₁ * (t * (δ * k₂) * t⁻¹)),
    ⟨x₁, hx₁, k₁ * (t * (δ * k₂) * t⁻¹), hκ, rfl⟩, t, rfl, rfl⟩,
    (δ * k₂)⁻¹ * (δ * x₂ * δ⁻¹) * (δ * k₂), hx₂'', ?_⟩
  rw [hy3]
  group

theorem commutator_le_of_normalizes {H P : Subgroup G} (hHN : H ≤ normalizer (P : Set G))
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {x y : G} (hx : x ∈ H ⊔ P) (hy : y ∈ H ⊔ P) :
    ⁅x, y⁆ ∈ P := by
  have hB : H ⊔ P ≤ normalizer (P : Set G) := sup_le hHN Subgroup.le_normalizer
  have hmul : ((H ⊔ P : Subgroup G) : Set G) = (H : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H P hHN
  have hx' : x ∈ (H : Set G) * (P : Set G) := by rw [← hmul]; exact hx
  have hy' : y ∈ (H : Set G) * (P : Set G) := by rw [← hmul]; exact hy
  obtain ⟨a₁, ha₁, p₁, hp₁, rfl⟩ := hx'
  obtain ⟨a₂, ha₂, p₂, hp₂, rfl⟩ := hy'
  have ha₁' : a₁ ∈ H := ha₁
  have ha₂' : a₂ ∈ H := ha₂
  have hp₁' : p₁ ∈ P := hp₁
  have hp₂' : p₂ ∈ P := hp₂
  have hN : (P.subgroupOf (H ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : P ≤ H ⊔ P)).mpr hB
  let f := QuotientGroup.mk' (P.subgroupOf (H ⊔ P))
  let A₁ : ↥(H ⊔ P) := ⟨a₁, (le_sup_left : H ≤ H ⊔ P) ha₁'⟩
  let A₂ : ↥(H ⊔ P) := ⟨a₂, (le_sup_left : H ≤ H ⊔ P) ha₂'⟩
  let P₁ : ↥(H ⊔ P) := ⟨p₁, (le_sup_right : P ≤ H ⊔ P) hp₁'⟩
  let P₂ : ↥(H ⊔ P) := ⟨p₂, (le_sup_right : P ≤ H ⊔ P) hp₂'⟩
  have hfP : ∀ (z : ↥(H ⊔ P)), (z : G) ∈ P → f z = 1 := by
    intro z hz
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hz)
  have hX : f (A₁ * P₁) = f A₁ := by rw [map_mul, hfP P₁ hp₁', mul_one]
  have hY : f (A₂ * P₂) = f A₂ := by rw [map_mul, hfP P₂ hp₂', mul_one]
  have hcA : ⁅A₁, A₂⁆ = 1 := by
    have : A₁ * A₂ = A₂ * A₁ := Subtype.ext (hab a₁ ha₁' a₂ ha₂')
    rw [commutatorElement_def, this]
    group
  have hcomm : f ⁅A₁ * P₁, A₂ * P₂⁆ = 1 := by
    rw [map_commutatorElement, hX, hY, ← map_commutatorElement, hcA, map_one]
  have hmem := (QuotientGroup.eq_one_iff _).mp hcomm
  have e : ((⁅A₁ * P₁, A₂ * P₂⁆ : ↥(H ⊔ P)) : G) = ⁅a₁ * p₁, a₂ * p₂⁆ := by
    simp [commutatorElement_def, A₁, A₂, P₁, P₂]
  rw [Subgroup.mem_subgroupOf, e] at hmem
  exact hmem

theorem t_not_mem_B {p : ℕ} (hp : p.Prime) {H P B₁ J : Subgroup G} {g m t δ : G}
    (hHN : H ≤ normalizer (P : Set G)) (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hP : IsPGroup p ↥P) (hJ : J ≤ Subgroup.closure ((B₁ : Set G) ∪ {m})) (hperf : ⁅J, J⁆ = J)
    (hJp : ¬ IsPGroup p ↥J) (hB₁ : ∀ b ∈ B₁, g⁻¹ * b * g ∈ H ⊔ P) (hn : g⁻¹ * m * g = t * δ)
    (hδ : δ ∈ H) : t ∉ H ⊔ P := by
  intro ht
  have : Fact p.Prime := ⟨hp⟩
  have hnB : g⁻¹ * m * g ∈ H ⊔ P := by
    rw [hn]
    exact (H ⊔ P).mul_mem ht ((le_sup_left : H ≤ H ⊔ P) hδ)
  have hJ₁ : ∀ j ∈ J, g⁻¹ * j * g ∈ H ⊔ P := by
    intro j hj
    refine Subgroup.closure_induction (p := fun j _ => g⁻¹ * j * g ∈ H ⊔ P) ?_ ?_ ?_ ?_ (hJ hj)
    · rintro x (hx | hx)
      · exact hB₁ x hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hnB
    · simp
    · intro x y _ _ hx hy
      have e : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
      rw [e]; exact (H ⊔ P).mul_mem hx hy
    · intro x _ hx
      have e : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
      rw [e]; exact (H ⊔ P).inv_mem hx
  have hJP : ∀ j ∈ J, g⁻¹ * j * g ∈ P := by
    have hle : ⁅J, J⁆ ≤ P.comap (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_comap]
      have := commutator_le_of_normalizes hHN hab (hJ₁ x hx) (hJ₁ y hy)
      simpa [MulAut.conj_apply, commutatorElement_def, mul_assoc] using this
    intro j hj
    have := hle (hperf ▸ hj)
    rw [Subgroup.mem_comap] at this
    simpa [MulAut.conj_apply] using this
  apply hJp
  rw [IsPGroup.iff_orderOf]
  intro j
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g⁻¹ * (j : G) * g, hJP j j.2⟩
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe, ← hk, Subgroup.orderOf_mk]
  have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (j : G)
  simpa [MulAut.conj_apply] using this.symm

end Transfer

section L5Facts

variable {G : Type} [Group G]

structure SPLJBruhat (D : SPLNot4 G) : Prop where
  J_perf : ⁅D.J, D.J⁆ = D.J
  J_notP : ¬ IsPGroup D.p ↥D.J
  H₀_norm : ∀ h ∈ D.H₀, ∀ y ∈ D.Y₁, h * y * h⁻¹ ∈ D.Y₁
  bruhat_J : ∀ x ∈ D.J, x ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) ∨
    x ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) * {D.z * D.w} * ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G)
  opp : ∀ y ∈ conjBy (D.z * D.w) D.Y₁, y ≠ 1 →
    y ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) * {D.z * D.w} * ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G)

section L5Core

variable (D : SPLNot4 G)

theorem X₄_eq_conjBy : D.X₄ = conjBy (D.a * D.w₁) D.Y₁ := by
  show conjBy D.w₁ (conjBy D.a D.Y₁) = _
  rw [conjBy_conjBy]

theorem H₀_le_H : D.H₀ ≤ D.H := by
  show zpowers (D.h₁ * D.h₂) ≤ D.H₁ ⊔ D.H₂
  rw [Subgroup.zpowers_le]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers _)) (Subgroup.mem_sup_right (mem_zpowers _))

theorem H₀_mul_set (hJ : SPLJBruhat D) :
    ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) = (D.Y₁ : Set G) * (D.H₀ : Set G) := by
  refine Subgroup.coe_mul_of_right_le_normalizer_left D.Y₁ D.H₀ ?_
  intro h hh
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hJ.H₀_norm h hh y hy
  · intro hy
    have := hJ.H₀_norm h⁻¹ (D.H₀.inv_mem hh) _ hy
    simpa [mul_assoc] using this

theorem X₄_le_P : D.X₄ ≤ D.P :=
  le_trans (le_sup_right : D.X₄ ≤ D.X₂ ⊔ D.X₃ ⊔ D.X₄) (le_sup_right : D.R₂ ≤ D.X₁ ⊔ D.R₂)

theorem H_le_normalizer_P [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D.toSPLNot3) : D.H ≤ normalizer (D.P : Set G) := by
  have hP : Normalizes D.H D.P := by
    show Normalizes D.H (D.X₁ ⊔ (D.X₂ ⊔ D.X₃ ⊔ D.X₄))
    exact normalizes_sup h3.H_X₁
      (normalizes_sup (normalizes_sup (H_X₂ D.toSPLNot3 hs h1 h3.toSPL3X) h3.H_X₃)
        (H_X₄ D.toSPLNot3 hs h1 h3))
  exact le_normalizer_of_normalizes hP

theorem l5_core [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D.toSPLNot3) (hA : SPL3A D.toSPLNot3) (hJ : SPLJBruhat D) :
    (∀ y ∈ conjBy D.t D.X₄, y ≠ 1 →
      y ∈ (D.X₄ : Set G) * (D.H : Set G) * {D.t} * (D.X₄ : Set G)) ∧
    D.B ⊓ (D.H ⊔ zpowers D.t) = D.H ∧ ¬ conjBy D.t D.B ≤ D.B := by
  obtain ⟨u, hu0, hu2, hasq, hauw⟩ := hA.a_u
  obtain ⟨δ, hδ, hn⟩ := n_mem_tH D.toSPLNot3 hs h1 hA.a_z ⟨u, H₀_le_H D hu0, hauw⟩
  have hX₄ := X₄_eq_conjBy D
  have hB₁ : ∀ b ∈ D.Y₁ ⊔ D.H₀, (D.a * D.w₁)⁻¹ * b * (D.a * D.w₁) ∈
      (D.X₄ : Set G) * (D.H : Set G) := by
    intro b hb
    have hb' : b ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) := hb
    rw [H₀_mul_set D hJ] at hb'
    obtain ⟨y, hy, h₀, hh₀, rfl⟩ := hb'
    refine ⟨(D.a * D.w₁)⁻¹ * y * (D.a * D.w₁), ?_, (D.a * D.w₁)⁻¹ * h₀ * (D.a * D.w₁), ?_, ?_⟩
    · rw [hX₄, SetLike.mem_coe, mem_conjBy_iff]
      have e : (D.a * D.w₁) * ((D.a * D.w₁)⁻¹ * y * (D.a * D.w₁)) * (D.a * D.w₁)⁻¹ = y := by group
      rw [e]; exact hy
    · have h1' := hA.a_H₀ h₀ hh₀
      have h2' := w₁_inv_norm_H D.toSPLNot3 hs h1 _ (H₀_le_H D h1')
      have e : (D.a * D.w₁)⁻¹ * h₀ * (D.a * D.w₁) = D.w₁⁻¹ * (D.a⁻¹ * h₀ * D.a) * D.w₁ := by group
      rw [e]; exact h2'
    · group
  have hbr := bruhat_transfer (H := D.H) (Y := D.Y₁) (B₁ := D.Y₁ ⊔ D.H₀) (X₄ := D.X₄)
    (g := D.a * D.w₁) (m := D.z * D.w) (t := D.t) (δ := δ) hX₄ hδ hn
    (t_norm_H D.toSPLNot3 hs h1) (H_X₄ D.toSPLNot3 hs h1 h3) hJ.opp hB₁
  have hBP : ∀ b ∈ D.Y₁ ⊔ D.H₀, (D.a * D.w₁)⁻¹ * b * (D.a * D.w₁) ∈ D.H ⊔ D.P := by
    intro b hb
    obtain ⟨x, hx, k, hk, hxk⟩ := hB₁ b hb
    rw [← hxk]
    exact (D.H ⊔ D.P).mul_mem ((le_sup_right : D.P ≤ D.H ⊔ D.P) (X₄_le_P D hx))
      ((le_sup_left : D.H ≤ D.H ⊔ D.P) hk)
  have hJcl : D.J ≤ Subgroup.closure (((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) ∪ {D.z * D.w}) := by
    intro x hx
    rcases hJ.bruhat_J x hx with hx1 | ⟨_, ⟨b₁, hb₁, m', hm', rfl⟩, b₂, hb₂, hx2⟩
    · exact Subgroup.subset_closure (Or.inl hx1)
    · have hm : m' = D.z * D.w := hm'
      have hx2' : b₁ * m' * b₂ = x := hx2
      rw [← hx2', hm]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hb₁))
        (Subgroup.subset_closure (Or.inr rfl))) (Subgroup.subset_closure (Or.inl hb₂))
  have htB : D.t ∉ D.H ⊔ D.P :=
    t_not_mem_B hs.prime (H_le_normalizer_P D hs h1 h3) (H_comm D.toSPLNot3 hs h1) h3.P_pGroup hJcl
      hJ.J_perf hJ.J_notP hBP hn hδ
  have htt := t_mul_t D.toSPLNot3 hs
  have hBN : D.B ⊓ (D.H ⊔ zpowers D.t) = D.H := by
    apply le_antisymm
    · rintro x ⟨hxB, hxN⟩
      have ht_norm : zpowers D.t ≤ normalizer (D.H : Set G) := by
        rw [Subgroup.zpowers_le]; exact t_mem_normalizer D.toSPLNot3 hs h1
      have hmul := Subgroup.coe_mul_of_right_le_normalizer_left D.H (zpowers D.t) ht_norm
      have hxN' : x ∈ (D.H : Set G) * (zpowers D.t : Set G) := by rw [← hmul]; exact hxN
      obtain ⟨k, hk, τ, hτ, rfl⟩ := hxN'
      have hk' : k ∈ D.H := hk
      have hτ' : τ = 1 ∨ τ = D.t := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hτ
        have h2 : D.t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
        rcases Int.even_or_odd' i with ⟨j, rfl | rfl⟩
        · left; rw [zpow_mul, h2, one_zpow]
        · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
      rcases hτ' with h | h
      · rw [h]; simpa using hk'
      · exfalso
        apply htB
        have hxB' : k * τ ∈ D.H ⊔ D.P := hxB
        have : D.t = k⁻¹ * (k * τ) := by rw [h]; group
        rw [this]
        exact (D.H ⊔ D.P).mul_mem ((D.H ⊔ D.P).inv_mem ((le_sup_left : D.H ≤ D.H ⊔ D.P) hk')) hxB'
    · exact le_inf (le_sup_left : D.H ≤ D.H ⊔ D.P) (le_sup_left : D.H ≤ D.H ⊔ zpowers D.t)
  refine ⟨hbr, hBN, ?_⟩
  intro hle
  have hne : D.X₄ ≠ ⊥ := by
    have := root_ne_bot D.toSPLNot3 hs h3 (i := 1) ⟨by norm_num, by norm_num⟩
    rwa [root_p1] at this
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
  have hxX : (x : G) ∈ D.X₄ := x.2
  set y : G := D.t⁻¹ * (x : G) * D.t with hy
  have hyc : y ∈ conjBy D.t D.X₄ := by
    rw [mem_conjBy_iff]
    have e : D.t * y * D.t⁻¹ = (x : G) := by rw [hy]; group
    rw [e]; exact hxX
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    have : (x : G) = D.t * y * D.t⁻¹ := by rw [hy]; group
    apply Subtype.ext
    rw [this, h]
    simp
  obtain ⟨_, ⟨_, ⟨x₁, hx₁, k, hk, rfl⟩, t', ht', rfl⟩, x₂, hx₂, hyy⟩ := hbr y hyc hy1
  have ht'' : t' = D.t := ht'
  have hyB : y ∈ D.B := by
    have : y ∈ conjBy D.t D.B := by
      rw [mem_conjBy_iff]
      have e : D.t * y * D.t⁻¹ = (x : G) := by rw [hy]; group
      rw [e]
      exact (le_sup_right : D.P ≤ D.H ⊔ D.P) (X₄_le_P D hxX)
    exact hle this
  apply htB
  have hyy' : x₁ * k * t' * x₂ = y := hyy
  have hxB : ∀ z ∈ D.X₄, z ∈ D.H ⊔ D.P := fun z hz => (le_sup_right : D.P ≤ D.H ⊔ D.P) (X₄_le_P D hz)
  have hk' : k ∈ D.H ⊔ D.P := (le_sup_left : D.H ≤ D.H ⊔ D.P) hk
  have : D.t = (x₁ * k)⁻¹ * y * x₂⁻¹ := by
    rw [← hyy', ht'']; group
  rw [this]
  exact (D.H ⊔ D.P).mul_mem ((D.H ⊔ D.P).mul_mem ((D.H ⊔ D.P).inv_mem
    ((D.H ⊔ D.P).mul_mem (hxB _ hx₁) hk')) hyB) ((D.H ⊔ D.P).inv_mem (hxB _ hx₂))

end L5Core

end L5Facts

end CFSG.GH74.GLS.SP.Local
