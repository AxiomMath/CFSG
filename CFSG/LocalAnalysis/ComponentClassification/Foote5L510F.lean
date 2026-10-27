module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

@[expose] def jeSub5 (S : Subgroup G) (M : ℕ) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ S ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = M), E

omit [Finite G] in
theorem jeSub5_le (S : Subgroup G) (M : ℕ) : jeSub5 S M ≤ S :=
  iSup₂_le fun _ hE => hE.1

omit [Finite G] in
theorem le_jeSub5 {S E : Subgroup G} {M : ℕ} (hES : E ≤ S) (hEsq : ∀ e ∈ E, e * e = 1)
    (hEM : Nat.card E = M) : E ≤ jeSub5 S M :=
  le_iSup₂ (f := fun (E : Subgroup G) (_ : E ≤ S ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = M) => E)
    E ⟨hES, hEsq, hEM⟩

theorem mem_normalizer_jeSub5 {S : Subgroup G} {M : ℕ} {y : G}
    (hy : ∀ E : Subgroup G, E ≤ S → (∀ e ∈ E, e * e = 1) → Nat.card E = M →
      ∀ x ∈ E, y * x * y⁻¹ ∈ S) :
    y ∈ normalizer (jeSub5 S M : Set G) := by
  have hle : conjugate (jeSub5 S M) y⁻¹ ≤ jeSub5 S M := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have hmap : (jeSub5 S M).map (MulAut.conj y).toMonoidHom ≤ jeSub5 S M := by
      rw [jeSub5, Subgroup.map_iSup]
      refine iSup_le fun E => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hE => ?_
      have hE' : conjugate E y⁻¹ ≤ S := fun x hx => by
        rw [mem_conjugate_iff, inv_inv] at hx
        have h1 := hy E hE.1 hE.2.1 hE.2.2 _ hx
        rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h1
      have hEsq' : ∀ e ∈ conjugate E y⁻¹, e * e = 1 := fun e he => by
        rw [mem_conjugate_iff, inv_inv] at he
        have h1 := hE.2.1 _ he
        calc e * e = y * ((y⁻¹ * e * y) * (y⁻¹ * e * y)) * y⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have h2 := le_jeSub5 hE' hEsq' (by rw [card_conjugate_eq_card, hE.2.2])
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine h2 ?_
      rw [mem_conjugate_iff, inv_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
      exact hw
    have h1 : y * (y⁻¹ * x * y) * y⁻¹ ∈ (jeSub5 S M).map (MulAut.conj y).toMonoidHom :=
      ⟨_, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h1
    exact hmap h1
  have heq : conjugate (jeSub5 S M) y⁻¹ = jeSub5 S M :=
    eq_of_le_of_card_ge hle (by rw [card_conjugate_eq_card])
  have h1 := mem_normalizer_of_conjugate_eq heq
  simpa using inv_mem h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem mem_jeSub5_of_ext (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {X : Subgroup G}
    (hXS : X ≤ S) (hXsq : ∀ x ∈ X, x * x = 1) (hXR : X ⊓ (S ⊓ L) = ⊥)
    (hXc : ∀ x ∈ X, ∀ r ∈ S ⊓ L, x * r = r * x) {M : ℕ} (hXM : 4 * Nat.card X = M) {r : G}
    (hr : r ∈ S ⊓ L) (hr2 : r * r = 1) : r ∈ jeSub5 S M := by
  by_cases hr1 : r = 1
  · rw [hr1]
    exact one_mem _
  obtain ⟨r', hr', hr'2, hr'1, hrr', hc⟩ : ∃ r' ∈ S ⊓ L, r' * r' = 1 ∧ r' ≠ 1 ∧ r ≠ r' ∧
      r * r' = r' * r := by
    by_cases hrt : r = t
    · obtain ⟨y, hy, hy2, x, hx, hxy⟩ := h.exists_noncentral_involution_R hna
      refine ⟨y, hy, hy2, fun h1 => hxy (by rw [h1, mul_one, one_mul]), fun h1 => hxy ?_, ?_⟩
      · rw [← h1, hrt]
        exact (h.tZ x (mem_inf.mp hx).1)
      · rw [hrt]
        exact (h.tZ y (mem_inf.mp hy).1).symm
    · exact ⟨t, h.tR, by rw [← sq, ← h.t2, pow_orderOf_eq_one], h.t_ne_one, hrt,
        (h.tZ r (mem_inf.mp hr).1)⟩
  set W := kleinFourOfCommutingInvolutions r r' hr2 hr'2 hc with hW
  have hW4 : Nat.card W = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions r r' hr2 hr'2 hr1 hr'1 hrr' hc).card_four
  have hWR : W ≤ S ⊓ L := fun w hw => by
    rcases (mem_kleinFour_iff hr2 hr'2 hc).mp hw with rfl | rfl | rfl | rfl
    · exact mul_mem hr hr'
    · exact hr
    · exact hr'
    · exact one_mem _
  have hWsq : ∀ w ∈ W, w * w = 1 := fun w hw => by
    rcases (mem_kleinFour_iff hr2 hr'2 hc).mp hw with rfl | rfl | rfl | rfl
    · rw [show r * r' * (r * r') = r * (r' * r) * r' by group, ← hc,
        show r * (r * r') * r' = (r * r) * (r' * r') by group, hr2, hr'2, one_mul]
    · exact hr2
    · exact hr'2
    · exact one_mul 1
  have hXW : ∀ x ∈ X, ∀ w ∈ W, x * w = w * x := fun x hx w hw => hXc x hx w (hWR hw)
  have hbot : X ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ X ⊓ (S ⊓ L) := mem_inf.mpr ⟨(mem_inf.mp hx).1, hWR (mem_inf.mp hx).2⟩
    rwa [hXR] at h1
  have hcard : Nat.card ↥(X ⊔ W) = M := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer X W (le_normalizer_of_commute hXW)
      (disjoint_iff.mpr hbot), hW4, ← hXM, mul_comm]
  have hrW : r ∈ W := (mem_kleinFour_iff hr2 hr'2 hc).mpr (Or.inr (Or.inl rfl))
  exact le_jeSub5 (sup_le hXS (hWR.trans inf_le_left))
    (fun y hy => sq_eq_one_of_mem_sup hXsq hWsq hXW hy) hcard (mem_sup_right hrW)

theorem R_le_of_involutions {J : Subgroup G} (hJ : ∀ r ∈ S ⊓ L, r * r = 1 → r ∈ J) :
    S ⊓ L ≤ J := by
  obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
  intro y hy
  obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul_of_dihedral e hy
  exact mul_mem (hJ a ha ha2) (hJ b hb hb2)

end Sec5

end CFSG.ComponentClassification.Foote5
