module

public import CFSG.GH74.GLS.SP.Local.SPLStages
public import CFSG.GH74.GLS.SP.Local.SPLCor
public import CFSG.GH74.GLS.SP.Local.Gen

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section Conj

variable {H A B : Subgroup G}

theorem conjBy_eq_of_mem (hA : Normalizes H A) {h : G} (hh : h ∈ H) : conjBy h A = A := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    simpa [mul_assoc] using hA h⁻¹ (H.inv_mem hh) _ hx
  · intro hx
    exact hA h hh x hx

theorem Normalizes.map_conjBy (hA : Normalizes H A) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    Normalizes H (conjBy g A) := by
  intro h hh x hx
  rw [mem_conjBy_iff] at hx ⊢
  have h1 : g * h * g⁻¹ ∈ H := (mem_normalizer_iff.1 hg h).1 hh
  have e : g * (h * x * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
  rw [e]
  exact hA _ h1 _ hx

theorem conjBy_mul_of_mem (hA : Normalizes H A) {g h : G} (hg : g ∈ normalizer (H : Set G))
    (hh : h ∈ H) : conjBy (g * h) A = conjBy g A := by
  rw [BNPair.conjBy_mul, conjBy_eq_of_mem (hA.map_conjBy hg) hh]

theorem conjBy_eq_self_of_comm {c : G} (hc : ∀ x ∈ A, c * x = x * c) : conjBy c A = A := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have h1 := hc _ hx
    have h2 : c * (c * x * c⁻¹) = c * x := by
      rw [h1]
      group
    have h3 : c * x * c⁻¹ = x := mul_left_cancel h2
    rwa [h3] at hx
  · intro hx
    have h1 := hc _ hx
    have h2 : c * x * c⁻¹ = x := by
      rw [h1]
      group
    rwa [h2]

theorem conjBy_inv_eq (hA : Normalizes H A) {w : G} (hw : w ∈ normalizer (H : Set G))
    (hww : w * w ∈ H) : conjBy w⁻¹ A = conjBy w A := by
  have e : w * (w * w)⁻¹ = w⁻¹ := by group
  rw [← e]
  exact conjBy_mul_of_mem hA hw (H.inv_mem hww)

theorem card_conjBy (g : G) (A : Subgroup G) : Nat.card ↥(conjBy g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjBy_conjBy (g h : G) (A : Subgroup G) : conjBy g (conjBy h A) = conjBy (h * g) A :=
  (BNPair.conjBy_mul h g A).symm

theorem normalizer_of_both {m : G} {H : Subgroup G} (h1 : ∀ h ∈ H, m * h * m⁻¹ ∈ H)
    (h2 : ∀ h ∈ H, m⁻¹ * h * m ∈ H) : m ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact h1 h
  · intro hh
    have := h2 _ hh
    simpa [mul_assoc] using this

end Conj

section Basic

variable (D : SPLNot3 G)

theorem t_mul_t (hs : SPLSetup D.toSPLNot0) : D.t * D.t = 1 := by
  have h := pow_orderOf_eq_one D.t
  rw [hs.syl.t_ord, pow_two] at h
  exact h

theorem t_inv (hs : SPLSetup D.toSPLNot0) : D.t⁻¹ = D.t :=
  inv_eq_of_mul_eq_one_right (t_mul_t D hs)

theorem t_comm_z (hs : SPLSetup D.toSPLNot0) : D.t * D.z = D.z * D.t :=
  hs.syl.comm_z hs.syl.t_mem

theorem t_conj_K₁ [Finite G] (hs : SPLSetup D.toSPLNot0) : ∀ x ∈ D.K₁, D.t * x * D.t⁻¹ ∈ D.K₂ := by
  intro x hx
  have h := hs.syl.t_swap
  rw [← h]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem t_conj_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) : ∀ x ∈ D.K₂, D.t * x * D.t⁻¹ ∈ D.K₁ := by
  intro x hx
  have h := hs.syl.t_swap
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : D.t * y * D.t⁻¹ = x := by simpa [MulAut.conj_apply] using hyx
  rw [← hyx']
  have e : D.t * (D.t * y * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * y * (D.t * D.t)⁻¹ := by group
  rw [e, t_mul_t D hs]
  simpa using hy

theorem H₁_le_K₁ (h1 : SPL2Set D.toSPLNot1) : D.H₁ ≤ D.K₁ := by
  show zpowers D.h₁ ≤ D.K₁
  rw [Subgroup.zpowers_le]
  exact h1.h₁_mem

theorem h₂_mem [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) : D.h₂ ∈ D.K₂ :=
  t_conj_K₁ D hs _ h1.h₁_mem

theorem H₂_le_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) : D.H₂ ≤ D.K₂ := by
  show zpowers D.h₂ ≤ D.K₂
  rw [Subgroup.zpowers_le]
  exact h₂_mem D hs h1

theorem H₁_le_H : D.H₁ ≤ D.H := le_sup_left

theorem H₂_le_H : D.H₂ ≤ D.H := le_sup_right

theorem H₁_H₂_comm [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ a ∈ D.H₁, ∀ b ∈ D.H₂, a * b = b * a := fun a ha b hb =>
  hs.comps.comm a (H₁_le_K₁ D h1 ha) b (H₂_le_K₂ D hs h1 hb)

theorem H₁_comm : ∀ a ∈ D.H₁, ∀ b ∈ D.H₁, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow_self D.h₁ m n).eq

theorem H₂_comm : ∀ a ∈ D.H₂, ∀ b ∈ D.H₂, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow_self D.h₂ m n).eq

theorem H_comm [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ a ∈ D.H, ∀ b ∈ D.H, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hb
  have c11 : Commute a₁ b₁ := H₁_comm D a₁ ha₁ b₁ hb₁
  have c22 : Commute a₂ b₂ := H₂_comm D a₂ ha₂ b₂ hb₂
  have c12 : Commute a₁ b₂ := H₁_H₂_comm D hs h1 a₁ ha₁ b₂ hb₂
  have c21 : Commute a₂ b₁ := (H₁_H₂_comm D hs h1 b₁ hb₁ a₂ ha₂).symm
  exact (((c11.mul_right c12).mul_left (c21.mul_right c22))).eq

end Basic

section BasicB

variable (D : SPLNot3 G)

theorem orderOf_h₂ (h1 : SPL2Set D.toSPLNot1) : orderOf D.h₂ = D.q - 1 := by
  have := orderOf_injective (MulAut.conj D.t).toMonoidHom (MulAut.conj D.t).injective D.h₁
  have e : D.h₂ = (MulAut.conj D.t).toMonoidHom D.h₁ := by
    simp [SPLNot1.h₂, MulAut.conj_apply]
  rw [e, this]
  exact h1.h₁_ord

theorem H_pPrime [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H, ¬ D.p ∣ orderOf h := by
  have hq1 : D.p ∣ D.q := by
    obtain ⟨k, hk, hq⟩ := hs.q_pow
    rw [hq]
    exact dvd_pow_self _ (by omega)
  have hq2 : ¬ D.p ∣ D.q - 1 := by
    intro h
    have h' := Nat.dvd_sub hq1 h
    have : D.q - (D.q - 1) = 1 := by have := hs.q_ge; omega
    rw [this] at h'
    exact hs.prime.one_lt.ne' (Nat.dvd_one.1 h')
  intro h hh hp
  apply hq2
  refine hp.trans ?_
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
  have e1 : a₁ ^ (D.q - 1) = 1 := by
    have := orderOf_dvd_of_mem_zpowers ha₁
    rw [h1.h₁_ord] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have e2 : a₂ ^ (D.q - 1) = 1 := by
    have := orderOf_dvd_of_mem_zpowers ha₂
    rw [orderOf_h₂ D h1] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  apply orderOf_dvd_of_pow_eq_one
  rw [(Commute.mul_pow (H₁_H₂_comm D hs h1 a₁ ha₁ a₂ ha₂ : Commute a₁ a₂)), e1, e2, one_mul]

theorem mem_H₁_conj : ∀ a ∈ D.H₁, D.t * a * D.t⁻¹ ∈ D.H₂ := by
  intro a ha
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have e : D.t * D.h₁ ^ m * D.t⁻¹ = D.h₂ ^ m := by
    rw [SPLNot1.h₂, conj_zpow]
  rw [e]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers D.h₂) m

theorem mem_H₂_conj (hs : SPLSetup D.toSPLNot0) : ∀ a ∈ D.H₂, D.t * a * D.t⁻¹ ∈ D.H₁ := by
  intro a ha
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h0 : D.t * D.h₂ * D.t⁻¹ = D.h₁ := by
    show D.t * (D.t * D.h₁ * D.t⁻¹) * D.t⁻¹ = D.h₁
    have e : D.t * (D.t * D.h₁ * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * D.h₁ * (D.t * D.t)⁻¹ := by group
    rw [e, t_mul_t D hs]
    simp
  have e : D.t * D.h₂ ^ m * D.t⁻¹ = D.h₁ ^ m := by
    rw [← h0, conj_zpow]
  rw [e]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers D.h₁) m

theorem t_norm_H [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H, D.t * h * D.t⁻¹ ∈ D.H := by
  intro h hh
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
  have : D.t * (a₁ * a₂) * D.t⁻¹ = (D.t * a₁ * D.t⁻¹) * (D.t * a₂ * D.t⁻¹) := by group
  rw [this]
  exact Subgroup.mul_mem _ (H₂_le_H D (mem_H₁_conj D a₁ ha₁))
    (H₁_le_H D (mem_H₂_conj D hs a₂ ha₂))

theorem t_mem_normalizer [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.t ∈ normalizer (D.H : Set G) := by
  refine normalizer_of_both (t_norm_H D hs h1) (fun h hh => ?_)
  have := t_norm_H D hs h1 h hh
  rw [t_inv D hs] at this ⊢
  exact this

theorem w₁_norm_H [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H, D.w₁ * h * D.w₁⁻¹ ∈ D.H := by
  intro h hh
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
  have e1 : D.w₁ * a₁ * D.w₁⁻¹ = a₁⁻¹ := h1.w₁_inv a₁ ha₁
  have e2 : D.w₁ * a₂ * D.w₁⁻¹ = a₂ := by
    have := hs.comps.comm D.w₁ h1.w₁_mem a₂ (H₂_le_K₂ D hs h1 ha₂)
    rw [this]
    group
  have : D.w₁ * (a₁ * a₂) * D.w₁⁻¹ = (D.w₁ * a₁ * D.w₁⁻¹) * (D.w₁ * a₂ * D.w₁⁻¹) := by group
  rw [this, e1, e2]
  exact Subgroup.mul_mem _ (H₁_le_H D (Subgroup.inv_mem _ ha₁)) (H₂_le_H D ha₂)

theorem w₁_inv_norm_H [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H, D.w₁⁻¹ * h * D.w₁ ∈ D.H := by
  intro h hh
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
  have e1 : D.w₁⁻¹ * a₁ * D.w₁ = a₁⁻¹ := by
    have := h1.w₁_inv a₁⁻¹ (Subgroup.inv_mem _ ha₁)
    rw [inv_inv] at this
    calc D.w₁⁻¹ * a₁ * D.w₁ = D.w₁⁻¹ * (D.w₁ * a₁⁻¹ * D.w₁⁻¹) * D.w₁ := by rw [this]
      _ = a₁⁻¹ := by group
  have e2 : D.w₁⁻¹ * a₂ * D.w₁ = a₂ := by
    have := hs.comps.comm D.w₁ h1.w₁_mem a₂ (H₂_le_K₂ D hs h1 ha₂)
    calc D.w₁⁻¹ * a₂ * D.w₁ = D.w₁⁻¹ * (a₂ * D.w₁) := by group
      _ = D.w₁⁻¹ * (D.w₁ * a₂) := by rw [this]
      _ = a₂ := by group
  have : D.w₁⁻¹ * (a₁ * a₂) * D.w₁ = (D.w₁⁻¹ * a₁ * D.w₁) * (D.w₁⁻¹ * a₂ * D.w₁) := by group
  rw [this, e1, e2]
  exact Subgroup.mul_mem _ (H₁_le_H D (Subgroup.inv_mem _ ha₁)) (H₂_le_H D ha₂)

theorem w₁_mem_normalizer [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ ∈ normalizer (D.H : Set G) :=
  normalizer_of_both (w₁_norm_H D hs h1) (w₁_inv_norm_H D hs h1)

theorem z_mem_H₁ (h1 : SPL2Set D.toSPLNot1) : D.z ∈ D.H₁ := by
  have hz : D.z ∈ zpowers D.z := Subgroup.mem_zpowers _
  rw [← h1.H_inter] at hz
  exact hz.1

theorem z_mem_H (h1 : SPL2Set D.toSPLNot1) : D.z ∈ D.H := H₁_le_H D (z_mem_H₁ D h1)

theorem w₁_comm_z [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * D.z = D.z * D.w₁ := hs.comps.cz₁ h1.w₁_mem

theorem w₂_mem_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₂ ∈ D.K₂ := t_conj_K₁ D hs _ h1.w₁_mem

theorem w₁_w₂_comm [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * D.w₂ = D.w₂ * D.w₁ := hs.comps.comm _ h1.w₁_mem _ (w₂_mem_K₂ D hs h1)

theorem w₂_sq [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₂ * D.w₂ = D.z := by
  show (D.t * D.w₁ * D.t⁻¹) * (D.t * D.w₁ * D.t⁻¹) = D.z
  have e : (D.t * D.w₁ * D.t⁻¹) * (D.t * D.w₁ * D.t⁻¹) = D.t * (D.w₁ * D.w₁) * D.t⁻¹ := by group
  rw [e, h1.w₁_sq]
  have := t_comm_z D hs
  calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [this]
    _ = D.z := by group

theorem z_mul_z (hs : SPLSetup D.toSPLNot0) : D.z * D.z = 1 := by
  have h := pow_orderOf_eq_one D.z
  rw [hs.syl.z_inv, pow_two] at h
  exact h

theorem rel_w₁tw₁t [Finite G] (hs : SPLSetup D.toSPLNot0) :
    D.w₁ * D.t * D.w₁ * D.t = D.w₁ * D.w₂ := by
  show D.w₁ * D.t * D.w₁ * D.t = D.w₁ * (D.t * D.w₁ * D.t⁻¹)
  rw [t_inv D hs]
  group

theorem rel_w₁tw₁ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * D.t * D.w₁ = D.t * (D.w₁ * D.w₂) := by
  have c := w₁_w₂_comm D hs h1
  have htt := t_mul_t D hs
  symm
  calc D.t * (D.w₁ * D.w₂) = D.t * (D.w₂ * D.w₁) := by rw [c]
    _ = D.t * ((D.t * D.w₁ * D.t) * D.w₁) := by
        show D.t * ((D.t * D.w₁ * D.t⁻¹) * D.w₁) = _
        rw [t_inv D hs]
    _ = (D.t * D.t) * (D.w₁ * D.t * D.w₁) := by group
    _ = D.w₁ * D.t * D.w₁ := by rw [htt]; group

theorem tw₁_sq [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    (D.t * D.w₁) * (D.t * D.w₁) = D.w₁ * D.w₂ := by
  have c := w₁_w₂_comm D hs h1
  calc (D.t * D.w₁) * (D.t * D.w₁) = (D.t * D.w₁ * D.t) * D.w₁ := by group
    _ = D.w₂ * D.w₁ := by
        show (D.t * D.w₁ * D.t) * D.w₁ = (D.t * D.w₁ * D.t⁻¹) * D.w₁
        rw [t_inv D hs]
    _ = D.w₁ * D.w₂ := c.symm

theorem pow_four [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    (D.t * D.w₁) ^ 4 = 1 := by
  have e : (D.t * D.w₁) ^ 4 = ((D.t * D.w₁) * (D.t * D.w₁)) * ((D.t * D.w₁) * (D.t * D.w₁)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [e, tw₁_sq D hs h1]
  have c := w₁_w₂_comm D hs h1
  calc D.w₁ * D.w₂ * (D.w₁ * D.w₂) = D.w₁ * (D.w₂ * D.w₁) * D.w₂ := by group
    _ = D.w₁ * (D.w₁ * D.w₂) * D.w₂ := by rw [← c]
    _ = (D.w₁ * D.w₁) * (D.w₂ * D.w₂) := by group
    _ = 1 := by rw [h1.w₁_sq, w₂_sq D hs h1, z_mul_z D hs]

end BasicB

section Roots

variable (D : SPLNot3 G)

theorem root_p1 : D.root 1 = D.X₄ := by simp [SPLNot3.root]
theorem root_p2 : D.root 2 = D.X₂ := by simp [SPLNot3.root]
theorem root_p3 : D.root 3 = D.X₃ := by simp [SPLNot3.root]
theorem root_p4 : D.root 4 = D.X₁ := by simp [SPLNot3.root]
theorem root_m1 : D.root (-1) = conjBy D.t D.X₄ := by simp [SPLNot3.root]
theorem root_m2 : D.root (-2) = D.X₂' := by simp [SPLNot3.root]
theorem root_m3 : D.root (-3) = conjBy (D.w₁ * D.t * D.w₁) D.X₃ := by simp [SPLNot3.root]
theorem root_m4 : D.root (-4) = D.X₁' := by simp [SPLNot3.root]

theorem root_cases {i : ℤ} (hi : IsRoot 4 i) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = -1 ∨ i = -2 ∨ i = -3 ∨ i = -4 := by
  obtain ⟨h0, h4⟩ := hi
  omega

theorem X₂_le_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X₂ ≤ D.K₂ := by
  intro x hx
  rw [SPLNot3.X₂, mem_conjBy_iff] at hx
  have h := t_conj_K₁ D hs _ (h3.X₁_le hx)
  have e : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
    have : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
    rw [this, t_mul_t D hs]
    simp
  rwa [e] at h

theorem X₂'_le_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X₂' ≤ D.K₂ := by
  intro x hx
  rw [SPLNot3.X₂', mem_conjBy_iff] at hx
  have h := t_conj_K₁ D hs _ (h3.X₁'_le hx)
  have e : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
    have : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
    rw [this, t_mul_t D hs]
    simp
  rwa [e] at h

theorem w₁_comm_of_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) {x : G}
    (hx : x ∈ D.K₂) : D.w₁ * x = x * D.w₁ := hs.comps.comm _ h1.w₁_mem _ hx

theorem H_X₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) :
    Normalizes D.H D.X₂ := h3.H_X₁.map_conjBy (t_mem_normalizer D hs h1)

theorem H_X₂' [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) :
    Normalizes D.H D.X₂' := h3.H_X₁'.map_conjBy (t_mem_normalizer D hs h1)

theorem H_X₄ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    Normalizes D.H D.X₄ := h3.H_X₃.map_conjBy (w₁_mem_normalizer D hs h1)

theorem w₁tw₁_mem_normalizer [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * D.t * D.w₁ ∈ normalizer (D.H : Set G) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (w₁_mem_normalizer D hs h1) (t_mem_normalizer D hs h1))
    (w₁_mem_normalizer D hs h1)

theorem root_normalizes [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) {i : ℤ} (hi : IsRoot 4 i) : Normalizes D.H (D.root i) := by
  rcases root_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [root_p1]; exact H_X₄ D hs h1 h3
  · rw [root_p2]; exact H_X₂ D hs h1 h3.toSPL3X
  · rw [root_p3]; exact h3.H_X₃
  · rw [root_p4]; exact h3.H_X₁
  · rw [root_m1]; exact (H_X₄ D hs h1 h3).map_conjBy (t_mem_normalizer D hs h1)
  · rw [root_m2]; exact H_X₂' D hs h1 h3.toSPL3X
  · rw [root_m3]; exact h3.H_X₃.map_conjBy (w₁tw₁_mem_normalizer D hs h1)
  · rw [root_m4]; exact h3.H_X₁'

theorem root_card (h3 : SPL3M2 D) {i : ℤ} (hi : IsRoot 4 i) : Nat.card ↥(D.root i) = D.q := by
  have hX₃ : Nat.card ↥D.X₃ = D.q := by
    rw [SPLNot3.X₃, card_conjBy]; exact h3.Y₁_card
  have hX₄ : Nat.card ↥D.X₄ = D.q := by
    rw [SPLNot3.X₄, card_conjBy]; exact hX₃
  rcases root_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [root_p1]; exact hX₄
  · rw [root_p2, SPLNot3.X₂, card_conjBy]; exact h3.X₁_card
  · rw [root_p3]; exact hX₃
  · rw [root_p4]; exact h3.X₁_card
  · rw [root_m1, card_conjBy]; exact hX₄
  · rw [root_m2, SPLNot3.X₂', card_conjBy]; exact h3.X₁'_card
  · rw [root_m3, card_conjBy]; exact hX₃
  · rw [root_m4]; exact h3.X₁'_card

theorem root_ne_bot (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) {i : ℤ} (hi : IsRoot 4 i) :
    D.root i ≠ ⊥ := by
  intro h
  have := root_card D h3 hi
  rw [h, Subgroup.card_bot] at this
  have := hs.q_ge
  omega

end Roots

section Cor

variable (D : SPLNot3 G)

theorem w₁_inv_eq (h1 : SPL2Set D.toSPLNot1) : D.w₁⁻¹ = D.w₁ * D.z⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  calc D.w₁ * (D.w₁ * D.z⁻¹) = (D.w₁ * D.w₁) * D.z⁻¹ := by group
    _ = 1 := by rw [h1.w₁_sq]; group

theorem w₁_sq_mem_H (h1 : SPL2Set D.toSPLNot1) : D.w₁ * D.w₁ ∈ D.H := by
  rw [h1.w₁_sq]
  exact z_mem_H D h1

theorem act₁_aux [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) :
    conjBy D.t⁻¹ (D.root 1) = D.root (-1) ∧ conjBy D.t⁻¹ (D.root (-1)) = D.root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 4 → conjBy D.t⁻¹ (D.root i) = D.root (6 - i) ∧
        conjBy D.t⁻¹ (D.root (-i)) = D.root (-(6 - i)) := by
  have ht := t_inv D hs
  have hcc : ∀ A : Subgroup G, conjBy D.t⁻¹ (conjBy D.t A) = A := by
    intro A
    rw [conjBy_conjBy, mul_inv_cancel, BNPair.conjBy_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [root_p1, root_m1, ht]
  · rw [root_p1, root_m1]
    exact hcc _
  · intro i hi2 hi4
    interval_cases i
    · refine ⟨?_, ?_⟩
      · show conjBy D.t⁻¹ (D.root 2) = D.root 4
        rw [root_p2, root_p4]
        exact hcc D.X₁
      · show conjBy D.t⁻¹ (D.root (-2)) = D.root (-4)
        rw [root_m2, root_m4]
        exact hcc D.X₁'
    · refine ⟨?_, ?_⟩
      · show conjBy D.t⁻¹ (D.root 3) = D.root 3
        rw [root_p3, ht]
        exact h3.t_X₃
      · show conjBy D.t⁻¹ (D.root (-3)) = D.root (-3)
        rw [root_m3, ht, conjBy_conjBy, rel_w₁tw₁t D hs, rel_w₁tw₁ D hs h1,
          BNPair.conjBy_mul D.t (D.w₁ * D.w₂) D.X₃, h3.t_X₃]
    · refine ⟨?_, ?_⟩
      · show conjBy D.t⁻¹ (D.root 4) = D.root 2
        rw [root_p4, root_p2, ht]
        rfl
      · show conjBy D.t⁻¹ (D.root (-4)) = D.root (-2)
        rw [root_m4, root_m2, ht]
        rfl

theorem act₂_aux [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) :
    conjBy D.w₁⁻¹ (D.root 4) = D.root (-4) ∧ conjBy D.w₁⁻¹ (D.root (-4)) = D.root 4 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy D.w₁⁻¹ (D.root i) = D.root (4 - i) ∧
        conjBy D.w₁⁻¹ (D.root (-i)) = D.root (-(4 - i)) := by
  have hn := w₁_mem_normalizer D hs h1
  have hww := w₁_sq_mem_H D h1
  have hw1 := w₁_inv_eq D h1
  refine ⟨?_, ?_, ?_⟩
  · rw [root_p4, root_m4, conjBy_inv_eq h3.H_X₁ hn hww]
    exact h3.X₁'_eq.symm
  · rw [root_m4, root_p4, h3.X₁'_eq, conjBy_conjBy, mul_inv_cancel, BNPair.conjBy_one]
  · intro i hi1 hi3
    interval_cases i
    · refine ⟨?_, ?_⟩
      · show conjBy D.w₁⁻¹ (D.root 1) = D.root 3
        rw [root_p1, root_p3]
        show conjBy D.w₁⁻¹ (conjBy D.w₁ D.X₃) = D.X₃
        rw [conjBy_conjBy, mul_inv_cancel, BNPair.conjBy_one]
      · show conjBy D.w₁⁻¹ (D.root (-1)) = D.root (-3)
        rw [root_m1, root_m3]
        have e1 : conjBy D.t D.X₄ = conjBy (D.w₁ * D.t) D.X₃ := by
          show conjBy D.t (conjBy D.w₁ D.X₃) = _
          rw [conjBy_conjBy]
        rw [e1, conjBy_conjBy, hw1]
        have e2 : D.w₁ * D.t * (D.w₁ * D.z⁻¹) = (D.w₁ * D.t * D.w₁) * D.z⁻¹ := by group
        rw [e2]
        exact conjBy_mul_of_mem h3.H_X₃ (w₁tw₁_mem_normalizer D hs h1)
          (Subgroup.inv_mem _ (z_mem_H D h1))
    · refine ⟨?_, ?_⟩
      · show conjBy D.w₁⁻¹ (D.root 2) = D.root 2
        rw [root_p2]
        refine conjBy_eq_self_of_comm (fun x hx => ?_)
        exact ((Commute.inv_left (w₁_comm_of_K₂ D hs h1 (X₂_le_K₂ D hs h3.toSPL3X hx)) :
          Commute D.w₁⁻¹ x)).eq
      · show conjBy D.w₁⁻¹ (D.root (-2)) = D.root (-2)
        rw [root_m2]
        refine conjBy_eq_self_of_comm (fun x hx => ?_)
        exact ((Commute.inv_left (w₁_comm_of_K₂ D hs h1 (X₂'_le_K₂ D hs h3.toSPL3X hx)) :
          Commute D.w₁⁻¹ x)).eq
    · refine ⟨?_, ?_⟩
      · show conjBy D.w₁⁻¹ (D.root 3) = D.root 1
        rw [root_p3, root_p1]
        exact conjBy_inv_eq h3.H_X₃ hn hww
      · show conjBy D.w₁⁻¹ (D.root (-3)) = D.root (-1)
        rw [root_m3, root_m1]
        have e1 : conjBy D.t D.X₄ = conjBy (D.w₁ * D.t) D.X₃ := by
          show conjBy D.t (conjBy D.w₁ D.X₃) = _
          rw [conjBy_conjBy]
        rw [e1, conjBy_conjBy]
        have e2 : D.w₁ * D.t * D.w₁ * D.w₁⁻¹ = D.w₁ * D.t := by group
        rw [e2]

theorem P_eq_iSup : D.P = ⨆ k ∈ Set.Icc (1 : ℤ) 4, D.root k := by
  apply le_antisymm
  · refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
    · exact le_iSup₂_of_le 4 ⟨by norm_num, by norm_num⟩ (by rw [root_p4])
    · exact le_iSup₂_of_le 2 ⟨by norm_num, by norm_num⟩ (by rw [root_p2])
    · exact le_iSup₂_of_le 3 ⟨by norm_num, by norm_num⟩ (by rw [root_p3])
    · exact le_iSup₂_of_le 1 ⟨by norm_num, by norm_num⟩ (by rw [root_p1])
  · refine iSup₂_le fun k hk => ?_
    obtain ⟨hk1, hk4⟩ := hk
    interval_cases k
    · rw [root_p1]
      exact le_trans (le_sup_right : D.X₄ ≤ D.X₂ ⊔ D.X₃ ⊔ D.X₄) (le_sup_right : D.R₂ ≤ D.X₁ ⊔ D.R₂)
    · rw [root_p2]
      exact le_trans (le_trans (le_sup_left : D.X₂ ≤ D.X₂ ⊔ D.X₃)
        (le_sup_left : D.X₂ ⊔ D.X₃ ≤ D.X₂ ⊔ D.X₃ ⊔ D.X₄)) (le_sup_right : D.R₂ ≤ D.X₁ ⊔ D.R₂)
    · rw [root_p3]
      exact le_trans (le_trans (le_sup_right : D.X₃ ≤ D.X₂ ⊔ D.X₃)
        (le_sup_left : D.X₂ ⊔ D.X₃ ≤ D.X₂ ⊔ D.X₃ ⊔ D.X₄)) (le_sup_right : D.R₂ ≤ D.X₁ ⊔ D.R₂)
    · rw [root_p4]
      exact (le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.R₂)

theorem sl2Pair_K₁ [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) : Stage4.SL2Pair D.H D.w₁ D.X₁ D.X₁' := by
  obtain ⟨Fq, hFq, hfin, hcard, ⟨e⟩⟩ := hs.comps.sl₁
  obtain ⟨k, hk1, hqk⟩ := hs.q_pow
  have hn := w₁_mem_normalizer D hs h1
  have hww := w₁_sq_mem_H D h1
  refine ⟨Fq, hFq, hfin, D.p, k, hs.prime, ?_, ?_, ?_, h3.X₁_ne,
    ⟨(MulEquiv.subgroupCongr h3.K₁_eq.symm).trans (e.trans (specialLinearGroupEquivStatedSL 2 Fq).symm)⟩, D.H₁, H₁_le_H D, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard, hqk]
  · rw [h3.X₁_card, hcard]
  · rw [h3.X₁'_card, hcard]
  · rw [← h3.K₁_eq]
    exact H₁_le_K₁ D h1
  · show Nat.card ↥(zpowers D.h₁) = Nat.card Fq - 1
    rw [Nat.card_zpowers, h1.h₁_ord, hcard]
  · rw [← h3.K₁_eq]
    exact h1.w₁_mem
  · rw [h1.w₁_sq]
    exact z_mem_H₁ D h1
  · intro x hx
    have hc : conjBy D.w₁⁻¹ D.X₁ = D.X₁' := by
      rw [conjBy_inv_eq h3.H_X₁ hn hww]
      exact h3.X₁'_eq.symm
    rw [← hc, mem_conjBy_iff]
    simpa [mul_assoc] using hx

theorem bruhat₂_aux [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) :
    ∀ y ∈ D.root (-4), y ≠ 1 → y ∈ (D.root 4 : Set G) * (D.H : Set G) * {D.w₁} * (D.root 4 : Set G) := by
  rw [root_m4, root_p4]
  have hP := (sl2Pair_K₁ D hs h1 h3).toSL2Phi h3.H_X₁ h3.H_X₁'
  exact hP.bruhat (fun h hh => w₁_norm_H D hs h1 h hh)

end Cor

section Instance

variable (D : SPLNot3 G)

theorem toCor41 [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (h42 : D.L42) (hch : D.CH_diff)
    (hbru : ∀ y ∈ conjBy D.t D.X₄, y ≠ 1 →
      y ∈ (D.X₄ : Set G) * (D.H : Set G) * {D.t} * (D.X₄ : Set G)) :
    Cor41 D.p D.H D.t D.w₁ D.P D.root where
  prime := hs.prime
  comm_H := H_comm D hs h1
  conj_H₁ := t_norm_H D hs h1
  conj_H₂ := w₁_norm_H D hs h1
  sq₁ := by rw [t_mul_t D hs]; exact D.H.one_mem
  sq₂ := w₁_sq_mem_H D h1
  pow := by rw [pow_four D hs h1]; exact D.H.one_mem
  H_pPrime := H_pPrime D hs h1
  U_pGroup := h3.P_pGroup
  U_gen := P_eq_iSup D
  ne_bot := fun i hi => root_ne_bot D hs h3 hi
  invariant := fun i hi h hh x hx => root_normalizes D hs h1 h3 hi h hh x hx
  act₁ := act₁_aux D hs h1 h3
  act₂ := act₂_aux D hs h1 h3
  opp := by
    rw [pow_two, tw₁_sq D hs h1]
    exact hch.2
  L42 := fun Z hZ hH l hl hlm => h42 Z hZ hH l hl hlm
  bruhat₁ := by
    rw [root_m1, root_p1]
    exact hbru
  bruhat₂ := bruhat₂_aux D hs h1 h3

end Instance

end CFSG.GH74.GLS.SP.Local
