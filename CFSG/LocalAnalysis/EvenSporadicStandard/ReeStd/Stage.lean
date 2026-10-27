module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Local

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Stage (H : LocalSetting G) (S Λ : Subgroup G) : Prop where
  pgroup : IsPGroup 2 S
  le : Λ ≤ S
  z_mem : H.z ∈ S
  z_not_mem : H.z ∉ Λ
  cover : ∀ s ∈ S, s ∈ Λ ∨ s * H.z ∈ Λ
  E_le : H.E ≤ Λ
  conj : ∀ s ∈ S, s ∉ Λ → IsConj H.z s
  noconj_E : ∀ e ∈ H.E, ¬ IsConj H.z e
  cov : ∀ b ∈ H.B, ∃ c ∈ centralizer ({H.z} : Set G) ⊓ normalizer (S : Set G),
    ∀ e ∈ H.E, c * e * c⁻¹ = b * e * b⁻¹

namespace LocalSetting

variable (H : LocalSetting G)

theorem sq_of_isConj {w : G} (hw : IsConj H.z w) : w * w = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hw
  rw [← hc]
  calc c * H.z * c⁻¹ * (c * H.z * c⁻¹) = c * (H.z * H.z) * c⁻¹ := by group
    _ = 1 := by rw [H.z_mul_self]; group

end LocalSetting

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem z_mul_mem {l : G} (hl : l ∈ Λ) : H.z * l ∈ S ∧ H.z * l ∉ Λ :=
  ⟨mul_mem h.z_mem (h.le hl), fun hh => h.z_not_mem (by
    have := mul_mem hh (inv_mem hl)
    simpa using this)⟩

include h in
theorem z_inv {l : G} (hl : l ∈ Λ) : H.z * l * H.z = l⁻¹ := by
  obtain ⟨h1, h2⟩ := h.z_mul_mem hl
  have := H.sq_of_isConj (h.conj _ h1 h2)
  calc H.z * l * H.z = (H.z * l * (H.z * l)) * l⁻¹ := by group
    _ = l⁻¹ := by rw [this]; group

include h in
theorem comm {a b : G} (ha : a ∈ Λ) (hb : b ∈ Λ) : a * b = b * a := by
  have h1 := h.z_inv (mul_mem ha hb)
  have h2 : H.z * (a * b) * H.z = (H.z * a * H.z) * (H.z * b * H.z) := by
    calc H.z * (a * b) * H.z = H.z * a * (H.z * H.z) * b * H.z := by
          rw [H.z_mul_self]; group
      _ = (H.z * a * H.z) * (H.z * b * H.z) := by group
  rw [h2, h.z_inv ha, h.z_inv hb, mul_inv_rev] at h1
  have : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := h1
  have h3 := congrArg (fun x => (x)⁻¹) this
  simpa using h3.symm

include h in
theorem z_normalizes {l : G} (hl : l ∈ Λ) : H.z * l * H.z⁻¹ ∈ Λ := by
  rw [H.z_inv, h.z_inv hl]
  exact inv_mem hl

include h in
theorem V_le : H.V ≤ S := sup_le (h.E_le.trans h.le) (zpowers_le.2 h.z_mem)

include h in
theorem centralizer_S : centralizer ({H.z} : Set G) ⊓ S = H.V := by
  refine le_antisymm (fun x hx => ?_) (le_inf H.V_le_centralizer h.V_le)
  have hP : IsPGroup 2 (centralizer ({H.z} : Set G) ⊓ S : Subgroup G) := h.pgroup.to_inf_right
  have hcard := (H.star hP inf_le_left).1
  have hV : H.V ≤ centralizer ({H.z} : Set G) ⊓ S := le_inf H.V_le_centralizer h.V_le
  have := Subgroup.eq_of_le_of_card_ge hV (by rw [H.card_V]; exact hcard)
  rw [← this] at hx
  exact hx

include h in
theorem mem_E_of_sq {l : G} (hl : l ∈ Λ) (hsq : l * l = 1) : l ∈ H.E := by
  have hinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hsq
  have hcomm : l * H.z = H.z * l := by
    have := h.z_inv hl
    rw [hinv] at this
    calc l * H.z = H.z * l * H.z * H.z := by rw [this]
      _ = H.z * l := by rw [mul_assoc, H.z_mul_self, mul_one]
  have hC : l ∈ centralizer ({H.z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hlV : l ∈ H.V := h.centralizer_S ▸ (⟨hC, h.le hl⟩ : l ∈ centralizer ({H.z} : Set G) ⊓ S)
  rcases H.mem_V_iff'.1 hlV with h1 | ⟨e, he, rfl⟩
  · exact h1
  · exfalso
    apply h.z_not_mem
    have := mul_mem (inv_mem (h.E_le he)) hl
    simpa using this

include h in
theorem not_isConj_of_mem {l : G} (hl : l ∈ Λ) : ¬ IsConj H.z l := fun hc =>
  h.noconj_E l (h.mem_E_of_sq hl (H.sq_of_isConj hc)) hc

include h in
theorem mul_inv_mem_Λ {a b : G} (ha : a ∈ S) (haΛ : a ∉ Λ) (hb : b ∈ S) (hbΛ : b ∉ Λ) :
    a⁻¹ * b ∈ Λ := by
  have h1 := (h.cover a ha).resolve_left haΛ
  have h2 := (h.cover b hb).resolve_left hbΛ
  have h3 : H.z * (a * H.z)⁻¹ * (b * H.z) * H.z⁻¹ ∈ Λ := by
    have := h.z_normalizes (mul_mem (inv_mem h1) h2)
    simpa [mul_assoc] using this
  have e : a⁻¹ * b = H.z * (a * H.z)⁻¹ * (b * H.z) * H.z⁻¹ := by group
  rw [e]
  exact h3

include h in
theorem N_conj_mem {n s : G} (hn : n ∈ normalizer (S : Set G)) (hs : s ∈ S) (hsΛ : s ∉ Λ) :
    n * s * n⁻¹ ∈ S ∧ n * s * n⁻¹ ∉ Λ := by
  have hmem : n * s * n⁻¹ ∈ S := (mem_normalizer_iff.1 hn s).1 hs
  refine ⟨hmem, fun hΛ => ?_⟩
  have hc : IsConj H.z (n * s * n⁻¹) := (h.conj s hs hsΛ).trans (_root_.isConj_iff.2 ⟨n, rfl⟩)
  exact h.not_isConj_of_mem hΛ hc

include h in
theorem N_normalizes_Λ {n l : G} (hn : n ∈ normalizer (S : Set G)) (hl : l ∈ Λ) :
    n * l * n⁻¹ ∈ Λ := by
  obtain ⟨hzl, hzlΛ⟩ := h.z_mul_mem hl
  obtain ⟨h1, h1Λ⟩ := h.N_conj_mem hn h.z_mem h.z_not_mem
  obtain ⟨h2, h2Λ⟩ := h.N_conj_mem hn hzl hzlΛ
  have := h.mul_inv_mem_Λ h1 h1Λ h2 h2Λ
  have e : (n * H.z * n⁻¹)⁻¹ * (n * (H.z * l) * n⁻¹) = n * l * n⁻¹ := by group
  rwa [e] at this

include h in
theorem relIndex_eq_two : Λ.relIndex S = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨H.z, h.z_mem, fun b hb => ?_⟩
  by_cases hbΛ : b ∈ Λ
  · right
    refine ⟨hbΛ, fun hbz => h.z_not_mem ?_⟩
    have := mul_mem (inv_mem hbΛ) hbz
    simpa using this
  · left
    exact ⟨(h.cover b hb).resolve_left hbΛ, hbΛ⟩

include h in
theorem card_S : Nat.card S = 2 * Nat.card Λ := by
  have := Subgroup.relIndex_mul_card (H := Λ) (K := S)
  rw [h.relIndex_eq_two, inf_eq_left.2 h.le] at this
  omega

end Stage

end CFSG.EvenSporadicStandard.ReeStd
