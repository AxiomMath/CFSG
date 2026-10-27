module

public import CFSG.GH74.GLS.SP.Local.SPLC2
public import CFSG.GH74.GLS.SP.Local.SPLADiag

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.IVK.L2Torus
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section L33a

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem orderOf_conj' (a x : G) : orderOf (a * x * a⁻¹) = orderOf x := by
  have := (MulAut.conj a).orderOf_eq x
  simpa [MulAut.conj_apply] using this

theorem X_exp (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : ∀ x ∈ D.X, x ^ D.p = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (X₁_X₂_comm D hs h3) hx
  rw [Commute.mul_pow (X₁_X₂_comm D hs h3 a ha b hb), h3.X₁_eab.2 a ha,
    (isEAb_conjBy h3.X₁_eab D.t).2 b hb, mul_one]

theorem X_le_K' (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X ≤ D.K :=
  sup_le (h3.X₁_le.trans le_sup_left) ((X₂_le_K₂ D hs h3).trans le_sup_right)

theorem exists_x₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hcK₁ : ∀ k ∈ D.K₁, c * k * c⁻¹ ∈ D.K₁) (hcX : ∀ x ∈ D.X₁, c * x * c⁻¹ = x) :
    ∃ x₁ ∈ D.X₁, ∀ k ∈ D.K₁, c * k * c⁻¹ = x₁ * k * x₁⁻¹ := by
  classical
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, -, -⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  have hcK₁' : ∀ k ∈ D.K₁, c⁻¹ * k * c ∈ D.K₁ := conj_inv_mem_of_finite c D.K₁ hcK₁
  let γ : ↥D.K₁ ≃* ↥D.K₁ :=
    { toFun := fun k => ⟨c * k * c⁻¹, hcK₁ k k.2⟩
      invFun := fun k => ⟨c⁻¹ * k * c, hcK₁' k k.2⟩
      left_inv := fun k => Subtype.ext (by show c⁻¹ * (c * (k : G) * c⁻¹) * c = k; group)
      right_inv := fun k => Subtype.ext (by show c * (c⁻¹ * (k : G) * c) * c⁻¹ = k; group)
      map_mul' := fun a b => Subtype.ext (by
        show c * ((a : G) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹)
        group) }
  let α : SL2m F ≃* SL2m F := ε.symm.trans (γ.trans ε)
  have hα : ∀ s : F, α (sl2U s) = sl2U s := by
    intro s
    have hup : sl2U s ∈ SL2Root.upperSub F := by simp [SL2Root.mem_upperSub]
    have hk : ((ε.symm (sl2U s) : ↥D.K₁) : G) ∈ D.X₁ := by
      rw [hE1]; simpa using hup
    have hγ : γ (ε.symm (sl2U s)) = ε.symm (sl2U s) := Subtype.ext (hcX _ hk)
    show ε (γ (ε.symm (sl2U s))) = sl2U s
    rw [hγ]; simp
  obtain ⟨x, hx⟩ := sl2_aut_fixing_U (F := F) (by rw [hFq]; exact hs.q_ge) α hα
  set x₁ : ↥D.K₁ := ε.symm (sl2U x) with hx₁
  have hx₁X : (x₁ : G) ∈ D.X₁ := by
    rw [hE1]; simpa [hx₁] using (by simp [SL2Root.mem_upperSub] : sl2U x ∈ SL2Root.upperSub F)
  refine ⟨x₁, hx₁X, fun k hk => ?_⟩
  have h1' := hx (ε ⟨k, hk⟩)
  have h2 : ε (γ ⟨k, hk⟩) = ε (x₁ * ⟨k, hk⟩ * x₁⁻¹) := by
    have h0 : α (ε ⟨k, hk⟩) = ε (γ ⟨k, hk⟩) := by
      show ε (γ (ε.symm (ε ⟨k, hk⟩))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← h0, h1', map_mul, map_mul, map_inv, hx₁, MulEquiv.apply_symm_apply]
  have h3' := congrArg Subtype.val (ε.injective h2)
  exact h3'

theorem odd_perm (hs : SPLSetup D.toSPLNot0) {c : G} (hcC : c ∈ Cz D.z) (hodd : Odd (orderOf c)) :
    (∀ k ∈ D.K₁, c * k * c⁻¹ ∈ D.K₁) ∧ (∀ k ∈ D.K₂, c * k * c⁻¹ ∈ D.K₂) := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  have hcd : c = (c ^ (m + 1)) * (c ^ (m + 1)) := by
    rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by omega, pow_succ, h1, one_mul]
  have hdC : c ^ (m + 1) ∈ Cz D.z := Subgroup.pow_mem _ hcC _
  have mapmem : ∀ (d : G) (K L : Subgroup G), K.map (MulAut.conj d).toMonoidHom = L →
      ∀ k ∈ K, d * k * d⁻¹ ∈ L := by
    intro d K L e k hk
    have : d * k * d⁻¹ ∈ K.map (MulAut.conj d).toMonoidHom := ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [e] at this
  have hcc : ∀ d : G, c = d * d → ∀ k : G, c * k * c⁻¹ = d * (d * k * d⁻¹) * d⁻¹ := by
    intro d hd k
    rw [hd]
    group
  have hcc' := hcc _ hcd
  rcases hs.comps.perm hdC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcc']; exact mapmem _ _ _ e1 _ (mapmem _ _ _ e1 k hk)
    · rw [hcc']; exact mapmem _ _ _ e2 _ (mapmem _ _ _ e2 k hk)
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcc']; exact mapmem _ _ _ e2 _ (mapmem _ _ _ e1 k hk)
    · rw [hcc']; exact mapmem _ _ _ e1 _ (mapmem _ _ _ e2 k hk)

theorem centralizes_X_of_proj (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {c : G}
    (hcK₁ : ∀ k ∈ D.K₁, c * k * c⁻¹ ∈ D.K₁) (hcK₂ : ∀ k ∈ D.K₂, c * k * c⁻¹ ∈ D.K₂)
    (hY₁ : ∀ a ∈ D.X₁, ∃ b ∈ D.X₂, c * (a * b) = (a * b) * c)
    (hY₂ : ∀ b ∈ D.X₂, ∃ a ∈ D.X₁, c * (a * b) = (a * b) * c) :
    (∀ a ∈ D.X₁, c * a * c⁻¹ = a) ∧ (∀ b ∈ D.X₂, c * b * c⁻¹ = b) := by
  have key : ∀ a ∈ D.X₁, ∀ b ∈ D.X₂, c * (a * b) = (a * b) * c →
      c * a * c⁻¹ = a ∧ c * b * c⁻¹ = b := by
    intro a ha b hb hab
    have haK : a ∈ D.K₁ := h3.X₁_le ha
    have hbK : b ∈ D.K₂ := X₂_le_K₂ D hs h3 hb
    have hκ₁ := hcK₁ a haK
    have hκ₂ := hcK₂ b hbK
    have e : (c * a * c⁻¹) * (c * b * c⁻¹) = a * b := by
      calc (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
        _ = (a * b) * c * c⁻¹ := by rw [hab]
        _ = a * b := by group
    have h1 : a⁻¹ * (c * a * c⁻¹) = b * (c * b * c⁻¹)⁻¹ := by
      calc a⁻¹ * (c * a * c⁻¹) = a⁻¹ * ((c * a * c⁻¹) * (c * b * c⁻¹)) * (c * b * c⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * b) * (c * b * c⁻¹)⁻¹ := by rw [e]
        _ = b * (c * b * c⁻¹)⁻¹ := by group
    have hmem : a⁻¹ * (c * a * c⁻¹) ∈ D.K₁ ⊓ D.K₂ :=
      ⟨D.K₁.mul_mem (D.K₁.inv_mem haK) hκ₁, by
        rw [h1]; exact D.K₂.mul_mem hbK (D.K₂.inv_mem hκ₂)⟩
    rw [hs.comps.inf_eq] at hmem
    have hκa : c * a * c⁻¹ = a := by
      rcases eq_one_or_z hs hmem with h | h
      · have := inv_mul_eq_one.mp h
        exact this.symm
      · exfalso
        have hκz : c * a * c⁻¹ = a * D.z := by rw [← h]; group
        have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
        have hp1 : a ^ D.p = 1 := h3.X₁_eab.2 a ha
        have hcomm : Commute a D.z := hs.comps.cz₁ haK
        have hzz : D.z * D.z = 1 := z_mul_z D hs
        have hzp : D.z ^ D.p = D.z := by
          obtain ⟨j, hj⟩ := hpodd
          rw [hj, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
        have h5 : (c * a * c⁻¹) ^ D.p = 1 := by rw [conj_pow, hp1]; group
        rw [hκz, hcomm.mul_pow, hp1, hzp, one_mul] at h5
        exact z_ne_one D hs h5
    refine ⟨hκa, ?_⟩
    have := e
    rw [hκa] at this
    exact mul_left_cancel this
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb, hab⟩ := hY₁ a ha
    exact (key a ha b hb hab).1
  · obtain ⟨a, ha, hab⟩ := hY₂ b hb
    exact (key a ha b hb hab).2

theorem cen_z_of_normalizes (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hcC : c ∈ Cz D.z) (hcK₁ : ∀ k ∈ D.K₁, c * k * c⁻¹ ∈ D.K₁)
    (hcK₂ : ∀ k ∈ D.K₂, c * k * c⁻¹ ∈ D.K₂)
    (hY₁ : ∀ a ∈ D.X₁, ∃ b ∈ D.X₂, c * (a * b) = (a * b) * c)
    (hY₂ : ∀ b ∈ D.X₂, ∃ a ∈ D.X₁, c * (a * b) = (a * b) * c) :
    ∃ x ∈ D.X, ∃ j : ℤ, c = x * D.z ^ j := by
  obtain ⟨hc1, hc2⟩ := centralizes_X_of_proj D hs h3 hcK₁ hcK₂ hY₁ hY₂
  obtain ⟨x₁, hx₁X, hx₁⟩ := exists_x₁ D hs h1 h3 hcK₁ hc1
  obtain ⟨x₂, hx₂X, hx₂⟩ := exists_x₂ D hs h1 h3 hcK₂ hc2
  have hx₁K : x₁ ∈ D.K₁ := h3.X₁_le hx₁X
  have hx₂K : x₂ ∈ D.K₂ := X₂_le_K₂ D hs h3 hx₂X
  have hx12 : ∀ k ∈ D.K₂, x₁ * k = k * x₁ := fun k hk => hs.comps.comm x₁ hx₁K k hk
  have hx21 : ∀ k ∈ D.K₁, x₂ * k = k * x₂ := fun k hk => (hs.comps.comm k hk x₂ hx₂K).symm
  set c' : G := (x₁ * x₂)⁻¹ * c with hc'
  have hc'K₁ : ∀ k ∈ D.K₁, c' * k = k * c' := by
    intro k hk
    have e1 := hx₁ k hk
    have e2 : x₂⁻¹ * k * x₂ = k := by
      have := hx21 k hk
      calc x₂⁻¹ * k * x₂ = x₂⁻¹ * (k * x₂) := by group
        _ = x₂⁻¹ * (x₂ * k) := by rw [this]
        _ = k := by group
    have : c' * k * c'⁻¹ = k := by
      calc c' * k * c'⁻¹ = x₂⁻¹ * (x₁⁻¹ * (c * k * c⁻¹) * x₁) * x₂ := by rw [hc']; group
        _ = x₂⁻¹ * (x₁⁻¹ * (x₁ * k * x₁⁻¹) * x₁) * x₂ := by rw [e1]
        _ = x₂⁻¹ * k * x₂ := by group
        _ = k := e2
    calc c' * k = (c' * k * c'⁻¹) * c' := by group
      _ = k * c' := by rw [this]
  have hc'K₂ : ∀ k ∈ D.K₂, c' * k = k * c' := by
    intro k hk
    have e1 := hx₂ k hk
    have hx2k : x₂ * k * x₂⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hx₂K hk) (D.K₂.inv_mem hx₂K)
    have e2 : x₁⁻¹ * (x₂ * k * x₂⁻¹) * x₁ = x₂ * k * x₂⁻¹ := by
      have := hx12 _ hx2k
      calc x₁⁻¹ * (x₂ * k * x₂⁻¹) * x₁ = x₁⁻¹ * ((x₂ * k * x₂⁻¹) * x₁) := by group
        _ = x₁⁻¹ * (x₁ * (x₂ * k * x₂⁻¹)) := by rw [this]
        _ = x₂ * k * x₂⁻¹ := by group
    have : c' * k * c'⁻¹ = k := by
      calc c' * k * c'⁻¹ = x₂⁻¹ * (x₁⁻¹ * (c * k * c⁻¹) * x₁) * x₂ := by rw [hc']; group
        _ = x₂⁻¹ * (x₁⁻¹ * (x₂ * k * x₂⁻¹) * x₁) * x₂ := by rw [e1]
        _ = x₂⁻¹ * (x₂ * k * x₂⁻¹) * x₂ := by rw [e2]
        _ = k := by group
    calc c' * k = (c' * k * c'⁻¹) * c' := by group
      _ = k * c' := by rw [this]
  have hc'K : ∀ k ∈ D.K, c' * k = k * c' := by
    intro k hk
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hs.comps.comm hk
    rw [hab]
    calc c' * (a * b) = (c' * a) * b := by group
      _ = (a * c') * b := by rw [hc'K₁ a ha]
      _ = a * (c' * b) := by group
      _ = a * (b * c') := by rw [hc'K₂ b hb]
      _ = a * b * c' := by group
  have hx12C : x₁ * x₂ ∈ Cz D.z :=
    Subgroup.mul_mem _ (mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hx₁K))
      (mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ hx₂K))
  have hc'C : c' ∈ Cz D.z := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx12C) hcC
  have hz : c' ∈ zpowers D.z := cen_C_K hs hc'C hc'K
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hz
  have hc_eq : c = (x₁ * x₂) * D.z ^ j := by rw [hj, hc']; group
  exact ⟨x₁ * x₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₁X) (Subgroup.mem_sup_right hx₂X),
    j, hc_eq⟩

theorem cen_z_odd (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hcz : c * D.z = D.z * c) (hodd : Odd (orderOf c))
    (hY₁ : ∀ a ∈ D.X₁, ∃ b ∈ D.X₂, c * (a * b) = (a * b) * c)
    (hY₂ : ∀ b ∈ D.X₂, ∃ a ∈ D.X₁, c * (a * b) = (a * b) * c) : c ∈ D.X := by
  have hcC : c ∈ Cz D.z := mem_centralizer_singleton_iff.mpr hcz
  obtain ⟨hcK₁, hcK₂⟩ := odd_perm D hs hcC hodd
  obtain ⟨x, hxX, j, hc_eq⟩ := cen_z_of_normalizes D hs h1 h3 hcC hcK₁ hcK₂ hY₁ hY₂
  have hzz : D.z * D.z = 1 := z_mul_z D hs
  have hww : (D.z ^ j) * (D.z ^ j) = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : D.z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
    rw [this, one_zpow]
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  have hxp : x ^ D.p = 1 := X_exp D hs h3 x hxX
  have hcom : Commute x (D.z ^ j) :=
    Commute.zpow_right (z_cen_K D hs x (X_le_K' D hs h3 hxX)).symm j
  have hwpow : ∀ n : ℕ, (D.z ^ j) ^ (2 * n + 1) = D.z ^ j := by
    intro n
    rw [pow_succ, pow_mul, sq, hww, one_pow, one_mul]
  have hzj : D.z ^ j = 1 := by
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨k, hk⟩ := hpodd
    have h1' : x ^ (2 * m + 1) * D.z ^ j = 1 := by
      have := pow_orderOf_eq_one c
      rw [hm, hc_eq, hcom.mul_pow, hwpow] at this
      exact this
    have h2 : D.z ^ j = (x ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1'
    have h3' : (D.z ^ j) ^ D.p = 1 := by
      rw [h2, inv_pow, ← pow_mul]
      have : x ^ ((2 * m + 1) * D.p) = 1 := by rw [Nat.mul_comm (2 * m + 1) D.p, pow_mul, hxp, one_pow]
      rw [this, inv_one]
    have h4 : (D.z ^ j) ^ D.p = D.z ^ j := by rw [hk]; exact hwpow k
    rw [← h4]; exact h3'
  rw [hc_eq, hzj, mul_one]
  exact hxX

end L33a

end CFSG.GH74.GLS.SP.Local
