module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511L

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem eq_of_commute_r_of_mem_sup {r : G} (hrS : r ∈ S) (hr2 : r * r = 1)
    (hrz : r * z = z * r) (hcard : Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ 2) {g : G}
    (hg : g ∈ Q ⊔ zpowers r) (hgr : g * r = r * g) : g = 1 ∨ g = r ∨ g = z ∨ g = r * z := by
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.z2
    rw [h1, orderOf_one] at this
    omega
  have hzCr : z ∈ Q ⊓ centralizer ({r} : Set G) :=
    mem_inf.mpr ⟨h.zQ, mem_centralizer_singleton_iff.mpr hrz.symm⟩
  have hCQ : ∀ q ∈ Q, q * r = r * q → q = 1 ∨ q = z := fun q hq hqr =>
    eq_one_or_eq_of_card_le_two hcard hzCr hz1
      (mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqr⟩)
  rcases mem_or_mul_mem_of_mem_sup hr2 (h.S_le_normalizer_Q hrS) hg with hgQ | hgQ
  · rcases hCQ g hgQ hgr with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  · have hq : (g * r) * r = r * (g * r) := by
      rw [mul_assoc, hr2, mul_one, hgr, ← mul_assoc, hr2, one_mul]
    rcases hCQ _ hgQ hq with h1 | h1
    · right; left
      calc g = g * r * r := by rw [mul_assoc, hr2, mul_one]
        _ = r := by rw [h1, one_mul]
    · right; right; right
      calc g = g * r * r := by rw [mul_assoc, hr2, mul_one]
        _ = r * z := by rw [h1, hrz]

theorem mem_center_D₁ (hQ : 4 < Nat.card Q) {r : G} (hrS : r ∈ S) (hr2 : r * r = 1)
    (hrz : r * z = z * r) (hcard : Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ 2) {x : G}
    (hx : x ∈ Q ⊔ zpowers r) (hxc : ∀ y ∈ Q ⊔ zpowers r, x * y = y * x) : x = 1 ∨ x = z := by
  have hnot : ¬ ∀ q ∈ Q, q * r = r * q := fun hall => by
    have hsub : Q ≤ Q ⊓ centralizer ({r} : Set G) := fun q hq =>
      mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr (hall q hq)⟩
    have := card_le_of_le hsub
    omega
  rcases h.eq_of_commute_r_of_mem_sup hrS hr2 hrz hcard hx
    (hxc r (mem_sup_right (mem_zpowers r))) with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    apply hnot
    intro q hq
    rw [← h1]
    exact (hxc q (mem_sup_left hq)).symm
  · exact Or.inr h1
  · exfalso
    apply hnot
    intro q hq
    have h2 := (hxc q (mem_sup_left hq)).symm
    rw [h1] at h2
    have hqz : q * z = z * q := h.zS q (h.QS hq)
    calc q * r = q * (r * z) * z := by rw [mul_assoc, mul_assoc, h.z_mul_self, mul_one]
      _ = r * z * q * z := by rw [h2]
      _ = r * (z * q) * z := by group
      _ = r * (q * z) * z := by rw [hqz]
      _ = r * q := by rw [mul_assoc, mul_assoc, h.z_mul_self, mul_one]

theorem commute_D₁_D₂ (hQ : 4 < Nat.card Q) {s : G} (hsT : s ∈ T) (hsS : s ∉ S)
    (hsN : s ∈ normalizer (S : Set G)) (hss : s * s ∈ S)
    (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥) {r : G} (hr : r ∈ conjugate (S ⊓ L) s) {x y : G}
    (hx : x ∈ Q ⊔ zpowers r) (hy : y ∈ conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) :
    x * y = y * x := by
  have hr' : s * r * s⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp hr
  have hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r := fun ρ hρ =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ hr
  have hne : conjugate Q 1 ≠ conjugate Q s⁻¹ := by
    intro h1
    rw [conjugate_one] at h1
    have h2 := mem_normalizer_of_conjugate_eq h1.symm
    exact h.not_mem_normalizer_Q hsT hsS (by simpa using inv_mem h2)
  have h58 := (h.lemma58 hQ (one_mem T) (inv_mem hsT) hne).2
  rw [conjugate_one] at h58
  have hrs : s⁻¹ * r * s ∈ S ⊓ L := by
    have h1 := h.conj_mem_R (inv_mem hss) hr'
    rwa [show (s * s)⁻¹ * (s * r * s⁻¹) * (s * s)⁻¹⁻¹ = s⁻¹ * r * s by group] at h1
  have hQC : ∀ q ∈ Q, ∀ y ∈ conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹), q * y = y * q := by
    intro q hq y hy
    have hle : conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) ≤ centralizer ({q} : Set G) :=
      sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (h58 q hq b hb).symm)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (h.commute_Q_R hq hr').symm))
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hrC : ∀ y ∈ conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹), r * y = y * r := by
    intro y hy
    have hle : conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) ≤ centralizer ({r} : Set G) := by
      refine sup_le (fun b hb => mem_centralizer_singleton_iff.mpr ?_)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hrR _ hr').symm))
      rw [mem_conjugate_iff, inv_inv] at hb
      have h1 := h.commute_Q_R hb hrs
      calc b * r = s * ((s⁻¹ * b * s) * (s⁻¹ * r * s)) * s⁻¹ := by group
        _ = s * ((s⁻¹ * r * s) * (s⁻¹ * b * s)) * s⁻¹ := by rw [h1]
        _ = r * b := by group
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hle : Q ⊔ zpowers r ≤ centralizer
      ((conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) : Subgroup G) : Set G) :=
    sup_le (fun q hq => mem_centralizer_iff.mpr fun y hy => (hQC q hq y hy).symm)
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun y hy => (hrC y hy).symm))
  exact (mem_centralizer_iff.mp (hle hx) y hy).symm

omit h [Finite G] in
theorem conjugate_sup_zpowers (Q : Subgroup G) (r s : G) :
    conjugate (Q ⊔ zpowers r) s⁻¹ = conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) := by
  simp only [conjugate]
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 2
  simp [MulAut.conj_apply]

omit h [Finite G] in
theorem mem_D₂_iff {Q : Subgroup G} {r s x : G} :
    x ∈ conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) ↔ s⁻¹ * x * s ∈ Q ⊔ zpowers r := by
  rw [← conjugate_sup_zpowers, mem_conjugate_iff, inv_inv]

end Sec5

end CFSG.ComponentClassification.Foote5
