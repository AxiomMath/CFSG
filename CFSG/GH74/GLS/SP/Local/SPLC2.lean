module

public import CFSG.GH74.GLS.SP.Local.SPLR2Defs
public import CFSG.GH74.GLS.SP.Local.SPLCoordK
public import CFSG.GH74.GLS.SP.Local.SPLKGU
public import CFSG.GH74.GLS.SP.Local.SPLACore
public import CFSG.GH74.GLS.SP.Local.SPLCCK
public import CFSG.GH74.GLS.SP.Local.SPLWt1

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.IVK.L2Torus
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local


section C2

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem X₂_not_le_zpowers (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : ¬ D.X₂ ≤ zpowers D.z := by
  intro h
  have h1 := Subgroup.card_le_of_le h
  rw [Nat.card_zpowers, hs.syl.z_inv, SPLNot3.X₂, card_conjBy, h3.X₁_card] at h1
  have := hs.q_ge
  omega

theorem exists_x₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hcK₂ : ∀ k ∈ D.K₂, c * k * c⁻¹ ∈ D.K₂) (hcX : ∀ x ∈ D.X₂, c * x * c⁻¹ = x) :
    ∃ x₂ ∈ D.X₂, ∀ k ∈ D.K₂, c * k * c⁻¹ = x₂ * k * x₂⁻¹ := by
  classical
  have htt := t_mul_t D hs
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, -, -⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  let φ : ↥D.K₂ ≃* ↥D.K₁ :=
    { toFun := fun k => ⟨D.t * k * D.t⁻¹, t_conj_K₂ D hs k k.2⟩
      invFun := fun k => ⟨D.t * k * D.t⁻¹, t_conj_K₁ D hs k k.2⟩
      left_inv := fun k => Subtype.ext (by
        show D.t * (D.t * (k : G) * D.t⁻¹) * D.t⁻¹ = k
        have : D.t * (D.t * (k : G) * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * k * (D.t * D.t)⁻¹ := by group
        rw [this, htt]; simp)
      right_inv := fun k => Subtype.ext (by
        show D.t * (D.t * (k : G) * D.t⁻¹) * D.t⁻¹ = k
        have : D.t * (D.t * (k : G) * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * k * (D.t * D.t)⁻¹ := by group
        rw [this, htt]; simp)
      map_mul' := fun a b => Subtype.ext (by
        show D.t * ((a : G) * b) * D.t⁻¹ = (D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹)
        group) }
  let ε₂ : ↥D.K₂ ≃* SL2m F := φ.trans ε
  have hε₂X : ∀ k : ↥D.K₂, (k : G) ∈ D.X₂ ↔ ε₂ k ∈ SL2Root.upperSub F := by
    intro k
    have h := hE1 (φ k)
    have hk : ((φ k : ↥D.K₁) : G) ∈ D.X₁ ↔ (k : G) ∈ D.X₂ := by
      show D.t * (k : G) * D.t⁻¹ ∈ D.X₁ ↔ _
      exact mem_conjBy_iff.symm
    exact hk.symm.trans h
  have hcK₂' : ∀ k ∈ D.K₂, c⁻¹ * k * c ∈ D.K₂ := by
    have := conj_inv_mem_of_finite c D.K₂ hcK₂
    exact this
  let γ : ↥D.K₂ ≃* ↥D.K₂ :=
    { toFun := fun k => ⟨c * k * c⁻¹, hcK₂ k k.2⟩
      invFun := fun k => ⟨c⁻¹ * k * c, hcK₂' k k.2⟩
      left_inv := fun k => Subtype.ext (by show c⁻¹ * (c * (k : G) * c⁻¹) * c = k; group)
      right_inv := fun k => Subtype.ext (by show c * (c⁻¹ * (k : G) * c) * c⁻¹ = k; group)
      map_mul' := fun a b => Subtype.ext (by
        show c * ((a : G) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹)
        group) }
  let α : SL2m F ≃* SL2m F := ε₂.symm.trans (γ.trans ε₂)
  have hα : ∀ s : F, α (sl2U s) = sl2U s := by
    intro s
    have hup : sl2U s ∈ SL2Root.upperSub F := by simp [SL2Root.mem_upperSub]
    have hk : ((ε₂.symm (sl2U s) : ↥D.K₂) : G) ∈ D.X₂ := by
      rw [hε₂X]; simpa using hup
    have hγ : γ (ε₂.symm (sl2U s)) = ε₂.symm (sl2U s) := Subtype.ext (hcX _ hk)
    show ε₂ (γ (ε₂.symm (sl2U s))) = sl2U s
    rw [hγ]; simp
  obtain ⟨x, hx⟩ := sl2_aut_fixing_U (F := F) (by rw [hFq]; exact hs.q_ge) α hα
  set x₂ : ↥D.K₂ := ε₂.symm (sl2U x) with hx₂
  have hx₂X : (x₂ : G) ∈ D.X₂ := by
    rw [hε₂X]; simpa [hx₂] using (by simp [SL2Root.mem_upperSub] : sl2U x ∈ SL2Root.upperSub F)
  refine ⟨x₂, hx₂X, fun k hk => ?_⟩
  have h1 := hx (ε₂ ⟨k, hk⟩)
  have h2 : ε₂ (γ ⟨k, hk⟩) = ε₂ (x₂ * ⟨k, hk⟩ * x₂⁻¹) := by
    have h0 : α (ε₂ ⟨k, hk⟩) = ε₂ (γ ⟨k, hk⟩) := by
      show ε₂ (γ (ε₂.symm (ε₂ ⟨k, hk⟩))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← h0, h1, map_mul, map_mul, map_inv, hx₂, MulEquiv.apply_symm_apply]
  have h3' := congrArg Subtype.val (ε₂.injective h2)
  exact h3'

theorem C2_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2)
    (h3 : SPL3X D) : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁ := by
  classical
  have hX₂K₂ := X₂_le_K₂ D hs h3
  apply le_antisymm
  · rintro c ⟨hc2, hcz⟩
    have hcX : ∀ x ∈ D.X₂, c * x * c⁻¹ = x := fun x hx => by
      have := mem_centralizer_iff.mp hc2 x hx
      rw [← this]; group
    have hcC : c ∈ Cz D.z := hcz
    have hnot := X₂_not_le_zpowers D hs h3
    have hfix : ∀ k ∈ D.K₂, c * k * c⁻¹ ∈ D.K₂ := by
      rcases hs.comps.perm hcC with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · intro k hk
        have : c * k * c⁻¹ ∈ D.K₂.map (MulAut.conj c).toMonoidHom :=
          ⟨k, hk, by simp [MulAut.conj_apply]⟩
        rwa [e2] at this
      · exfalso
        apply hnot
        intro x hx
        have : c * x * c⁻¹ ∈ D.K₂.map (MulAut.conj c).toMonoidHom :=
          ⟨x, hX₂K₂ hx, by simp [MulAut.conj_apply]⟩
        rw [e2, hcX x hx] at this
        rw [← hs.comps.inf_eq]
        exact ⟨this, hX₂K₂ hx⟩
    obtain ⟨x₂, hx₂X, hx₂⟩ := exists_x₂ D hs h1 h3 hfix hcX
    have hx₂K₂ : x₂ ∈ D.K₂ := hX₂K₂ hx₂X
    set c' : G := x₂⁻¹ * c with hc'
    have hc'K₂ : ∀ k ∈ D.K₂, c' * k * c'⁻¹ = k := by
      intro k hk
      have := hx₂ k hk
      calc c' * k * c'⁻¹ = x₂⁻¹ * (c * k * c⁻¹) * x₂ := by rw [hc']; group
        _ = x₂⁻¹ * (x₂ * k * x₂⁻¹) * x₂ := by rw [this]
        _ = k := by group
    have hx₂C : x₂ ∈ Cz D.z := mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ hx₂K₂)
    have hc'C : c' ∈ Cz D.z := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂C) hcC
    obtain ⟨k, hk, s, hsS, y, hyF, hdec⟩ := hs.gen c' hc'C
    have hsK : s ∈ D.K := by
      by_contra hsK
      have hkC : k ∈ Cz D.z := K_le_Cz hs.comps hk
      have hsC : s ∈ Cz D.z := hs.gen_syl.S_le_Cz hsS
      have hksC : k * s ∈ Cz D.z := Subgroup.mul_mem _ hkC hsC
      rcases hs.comps.perm hksC with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact swap_not_mem hs hsS hsK hk (Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1)
      · apply hnot
        intro x hx
        have hyx : y * x * y⁻¹ ∈ D.K₂ := F_normalizes_K₂ hs y hyF x (hX₂K₂ hx)
        have hmem : (k * s) * (y * x * y⁻¹) * (k * s)⁻¹ ∈ D.K₂.map (MulAut.conj (k * s)).toMonoidHom :=
          ⟨_, hyx, rfl⟩
        rw [e2] at hmem
        have e : (k * s) * (y * x * y⁻¹) * (k * s)⁻¹ = c' * x * c'⁻¹ := by rw [hdec]; group
        rw [e, hc'K₂ x (hX₂K₂ hx)] at hmem
        rw [← hs.comps.inf_eq]
        exact ⟨hmem, hX₂K₂ hx⟩
    have hKK : D.K₁ ⊔ D.K₂ = D.K := rfl
    have hksK : k * s ∈ D.K := Subgroup.mul_mem _ hk hsK
    obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hκ⟩ := mem_sup_of_commute hs.comps.comm hksK
    have hsS₁ : ∀ q ∈ (D.S : Subgroup G) ⊓ D.K₂, q ∈ D.S₁ := fun q hq =>
      ⟨hq.1, Subgroup.mem_sup_right hq.2⟩
    have hκ₂z : κ₂ ∈ zpowers D.z := by
      refine cen_K₂ hs hκ₂ (fun q hq => ?_)
      have hyq : q * y = y * q := mem_centralizer_iff.mp (F_le_centralizer_S₁ D.toSPLNot0 hyF) q (hsS₁ q hq)
      have hyq' : y * q * y⁻¹ = q := by rw [← hyq]; group
      have h1' := hc'K₂ q hq.2
      rw [hdec, hκ] at h1'
      have e : κ₁ * κ₂ * y * q * (κ₁ * κ₂ * y)⁻¹ = κ₁ * (κ₂ * q * κ₂⁻¹) * κ₁⁻¹ := by
        calc κ₁ * κ₂ * y * q * (κ₁ * κ₂ * y)⁻¹ = κ₁ * κ₂ * (y * q * y⁻¹) * κ₂⁻¹ * κ₁⁻¹ := by group
          _ = κ₁ * (κ₂ * q * κ₂⁻¹) * κ₁⁻¹ := by rw [hyq']; group
      rw [e] at h1'
      have hq2 : κ₂ * q * κ₂⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hκ₂ hq.2) (D.K₂.inv_mem hκ₂)
      have hc1 := hs.comps.comm κ₁ hκ₁ _ hq2
      have h2' : κ₂ * q * κ₂⁻¹ = q := by
        calc κ₂ * q * κ₂⁻¹ = κ₁ * (κ₂ * q * κ₂⁻¹) * κ₁⁻¹ := by rw [hc1]; group
          _ = q := h1'
      calc κ₂ * q = (κ₂ * q * κ₂⁻¹) * κ₂ := by group
        _ = q * κ₂ := by rw [h2']
    have hκ₂K₁ : κ₂ ∈ D.K₁ := Subgroup.zpowers_le.mpr (z_mem_K₁ hs) hκ₂z
    have hyK₂ : ∀ k₂ ∈ D.K₂, y * k₂ * y⁻¹ = k₂ := by
      intro k₂ hk₂
      have h1' := hc'K₂ k₂ hk₂
      rw [hdec, hκ] at h1'
      have hyk : y * k₂ * y⁻¹ ∈ D.K₂ := F_normalizes_K₂ hs y hyF k₂ hk₂
      have hz2 : κ₂ * (y * k₂ * y⁻¹) = (y * k₂ * y⁻¹) * κ₂ := by
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hκ₂z
        exact ((Commute.zpow_left (show Commute D.z (y * k₂ * y⁻¹) from
          (hs.comps.cz₂ hyk).symm) j)).eq
      have hc2' := hs.comps.comm κ₁ hκ₁ _ hyk
      have e : κ₁ * κ₂ * y * k₂ * (κ₁ * κ₂ * y)⁻¹ = κ₁ * (κ₂ * (y * k₂ * y⁻¹) * κ₂⁻¹) * κ₁⁻¹ := by
        group
      rw [e, hz2] at h1'
      rw [mul_assoc (y * k₂ * y⁻¹) κ₂ κ₂⁻¹, mul_inv_cancel, mul_one] at h1'
      calc y * k₂ * y⁻¹ = κ₁ * (y * k₂ * y⁻¹) * κ₁⁻¹ := by rw [hc2']; group
        _ = k₂ := h1'
    have hyt : y * D.t = D.t * y := mem_centralizer_singleton_iff.mp (hc.F_eq hyF)
    have hyK₁ : ∀ k₁ ∈ D.K₁, y * k₁ * y⁻¹ = k₁ := by
      intro k₁ hk₁
      have h2 := hyK₂ _ (t_conj_K₁ D hs k₁ hk₁)
      have e : y * (D.t * k₁ * D.t⁻¹) * y⁻¹ = D.t * (y * k₁ * y⁻¹) * D.t⁻¹ := by
        calc y * (D.t * k₁ * D.t⁻¹) * y⁻¹ = (y * D.t) * k₁ * (D.t⁻¹ * y⁻¹) := by group
          _ = (D.t * y) * k₁ * (D.t⁻¹ * y⁻¹) := by rw [hyt]
          _ = D.t * (y * k₁ * y⁻¹) * D.t⁻¹ := by
            have : D.t⁻¹ * y⁻¹ = y⁻¹ * D.t⁻¹ := by
              have := congrArg (fun x => x⁻¹) hyt
              simp only [mul_inv_rev] at this
              exact this
            rw [this]; group
      rw [e] at h2
      have := mul_left_cancel (mul_right_cancel h2)
      exact this
    have hyKall : ∀ x ∈ D.K, y * x = x * y := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hx
      have h1' : y * a = a * y := by
        have := hyK₁ a ha
        calc y * a = (y * a * y⁻¹) * y := by group
          _ = a * y := by rw [this]
      have h2' : y * b = b * y := by
        have := hyK₂ b hb
        calc y * b = (y * b * y⁻¹) * y := by group
          _ = b * y := by rw [this]
      calc y * (a * b) = (y * a) * b := by group
        _ = (a * y) * b := by rw [h1']
        _ = a * (y * b) := by group
        _ = a * (b * y) := by rw [h2']
        _ = a * b * y := by group
    have hy1 : y = 1 := eq_one_of_mem_F_cen_K hs hyF hyKall
    have hc'K₁ : c' ∈ D.K₁ := by
      rw [hdec, hy1, mul_one, hκ]
      exact D.K₁.mul_mem hκ₁ hκ₂K₁
    have hcc : c = x₂ * c' := by rw [hc']; group
    rw [hcc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₂X) (Subgroup.mem_sup_right hc'K₁)
  · refine sup_le ?_ ?_
    · intro x hx
      refine ⟨?_, mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ (hX₂K₂ hx))⟩
      exact mem_centralizer_iff.mpr (fun x' hx' => (isEAb_conjBy h3.X₁_eab D.t).1 x' hx' x hx)
    · intro k hk
      refine ⟨?_, mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hk)⟩
      exact mem_centralizer_iff.mpr (fun x' hx' => (hs.comps.comm k hk x' (hX₂K₂ hx')).symm)

end C2

theorem splInC2 : SPLInC2 := by
  intro G _ _ _ D hs h1 hc h3
  exact C2_eq D hs h1 hc h3

end CFSG.GH74.GLS.SP.Local
