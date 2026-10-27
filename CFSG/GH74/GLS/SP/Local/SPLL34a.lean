module

public import CFSG.GH74.GLS.SP.Local.SPLL33c
public import CFSG.GH74.GLS.SP.Local.SPLBurn

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

@[expose] def SPLNot3.C₁ {G : Type} [Group G] (D : SPLNot3 G) : Subgroup G :=
  centralizer (D.Y₁ : Set G)

section L34a

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem mem_C₁ {g : G} : g ∈ D.C₁ ↔ ∀ y ∈ D.Y₁, y * g = g * y :=
  mem_centralizer_iff

omit [Finite G] in
theorem Y₁_diag (h3 : SPL3X D) {u : G} (hu : u ∈ D.X₁) :
    u * (D.t * u⁻¹ * D.t⁻¹) ∈ D.Y₁ := by
  have huX : u ∈ D.X := Subgroup.mem_sup_left hu
  have := Subgroup.commutator_mem_commutator huX (mem_zpowers D.t)
  rw [← h3.Y₁_eq] at this
  simpa [commutatorElement_def, mul_assoc] using this

theorem X_le_C₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X ≤ D.C₁ := fun x hx =>
  (mem_C₁ D).mpr (fun y hy => X_comm D hs h3 y (h3.Y₁_le hy) x hx)

theorem z_mem_C₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.z ∈ D.C₁ :=
  (mem_C₁ D).mpr (fun y hy => (z_cen_K D hs y (X_le_K' D hs h3 (h3.Y₁_le hy))).symm)

omit [Finite G] in
theorem t_conj_C₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {c : G} (hc : c ∈ D.C₁) :
    D.t * c * D.t⁻¹ ∈ D.C₁ := by
  rw [mem_C₁]
  intro y hy
  have htt := t_mul_t D hs
  have hti : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right htt
  have hy' : D.t * y * D.t⁻¹ = y⁻¹ := h3.Y₁_inv y hy
  have e1 : D.t⁻¹ * y * D.t = y⁻¹ := by
    rw [hti]; rw [hti] at hy'; exact hy'
  have h := (mem_C₁ D).mp hc _ (D.Y₁.inv_mem hy)
  have e2 : D.t * y⁻¹ * D.t⁻¹ = y := by rw [← conj_inv, hy', inv_inv]
  calc y * (D.t * c * D.t⁻¹) = D.t * ((D.t⁻¹ * y * D.t) * c) * D.t⁻¹ := by group
    _ = D.t * (y⁻¹ * c) * D.t⁻¹ := by rw [e1]
    _ = D.t * (c * y⁻¹) * D.t⁻¹ := by rw [h]
    _ = (D.t * c * D.t⁻¹) * (D.t * y⁻¹ * D.t⁻¹) := by group
    _ = (D.t * c * D.t⁻¹) * y := by rw [e2]

theorem C_A_Y₁ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) {a : G}
    (ha : a ∈ D.A) (hac : ∀ y ∈ D.Y₁, a * y = y * a) : a = 1 := by
  by_contra ha1
  have hA₀ : zpowers a ≤ D.A := zpowers_le.mpr ha
  have hA₀ne : zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.mp h)
  have hN := hc.N_C (zpowers a) hA₀ hA₀ne
  have hY : ∀ y ∈ D.Y₁, y = 1 := by
    intro y hy
    have hyX : y ∈ D.X := h3.Y₁_le hy
    have hyZ : y ∈ centralizer (zpowers a : Set G) := mem_centralizer_iff.mpr (fun h hh => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
      exact ((show Commute a y from hac y hy).zpow_left j).eq)
    have hyN : y ∈ normalizer (zpowers a : Set G) := Subgroup.centralizer_le_normalizer _ hyZ
    have hyC : y ∈ D.C := mem_centralizer_singleton_iff.mpr
      (z_cen_K D hs y (X_le_K' D hs h3 hyX)).symm
    have hyCt : y ∈ D.C ⊓ D.Ct := by rw [← hN]; exact ⟨hyN, hyC⟩
    have hyt : y * D.t = D.t * y := mem_centralizer_singleton_iff.mp hyCt.2
    have hinv : D.t * y * D.t⁻¹ = y⁻¹ := h3.Y₁_inv y hy
    have hcomm : D.t * y * D.t⁻¹ = y := by rw [← hyt]; group
    have hyy : y⁻¹ = y := by rw [← hinv, hcomm]
    exact eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) (h3.Y₁_eab.2 y hy) hyy
  have hbot : D.Y₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hY
  have hcard := h3.Y₁_card
  rw [hbot, Subgroup.card_bot] at hcard
  have := hs.q_ge
  omega

omit [Finite G] in
theorem Y₁_family (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {c : G} (hc : c ∈ D.C₁) :
    (∀ a ∈ D.X₁, ∃ b ∈ D.X₂, c * (a * b) = (a * b) * c) ∧
      (∀ b ∈ D.X₂, ∃ a ∈ D.X₁, c * (a * b) = (a * b) * c) := by
  have htt := t_mul_t D hs
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · refine ⟨D.t * a⁻¹ * D.t⁻¹, t_mem_X₂ D hs (D.X₁.inv_mem ha), ?_⟩
    exact ((mem_C₁ D).mp hc _ (Y₁_diag D h3 ha)).symm
  · have hb' : D.t * b⁻¹ * D.t⁻¹ ∈ D.X₁ := t_mem_X₁ D (D.X₂.inv_mem hb)
    refine ⟨D.t * b⁻¹ * D.t⁻¹, hb', ?_⟩
    have e : D.t * (D.t * b⁻¹ * D.t⁻¹)⁻¹ * D.t⁻¹ = b := by
      calc D.t * (D.t * b⁻¹ * D.t⁻¹)⁻¹ * D.t⁻¹ = (D.t * D.t) * b * (D.t * D.t)⁻¹ := by group
        _ = b := by rw [htt]; group
    have hy := Y₁_diag D h3 hb'
    rw [e] at hy
    exact ((mem_C₁ D).mp hc _ hy).symm

theorem cen_z_odd_Y₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hc : c ∈ D.C₁) (hcz : c * D.z = D.z * c) (hodd : Odd (orderOf c)) : c ∈ D.X :=
  cen_z_odd D hs h1 h3 hcz hodd (Y₁_family D hs h3 hc).1 (Y₁_family D hs h3 hc).2

theorem odd_mem_A (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {g : G}
    (hg : g ∈ D.A ⊔ D.T₀) (hodd : Odd (orderOf g)) : g ∈ D.A := by
  obtain ⟨a, ha, s, hsT, rfl⟩ := mem_A_sup_T0 D hs hc hg
  obtain ⟨k, hk⟩ := T0_pgroup D hs hc ⟨s, hsT⟩
  have hk' : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  exact mem_of_mul_of_coprime_orders D.A ha
    (fun x hx => A_norm_Ct D hc s (T0_le_Ct D hs hc hsT) x hx) rfl hk' (pow_orderOf_eq_one _)
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))

end L34a

end CFSG.GH74.GLS.SP.Local
