module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresWords

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy

section General

variable {X : Type} [Group X]

theorem zpow_eq_one_or_self {t : X} (htt : t * t = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · exact Or.inl (by rw [zpow_mul, h2, one_zpow])
  · exact Or.inr (by rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul])

theorem conj_mul_self_eq_one {s : X} (hs : s * s = 1) (g : X) :
    g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
  rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hs, mul_one, mul_inv_cancel]

theorem exists_of_mem_sup_zpowers [Finite X] {V : Subgroup X} {t : X} (htt : t * t = 1)
    (hVt : ∀ v ∈ V, v * t = t * v) {g : X} (hg : g ∈ V ⊔ Subgroup.zpowers t) :
    ∃ v ∈ V, g = v ∨ g = v * t := by
  have hle : V ≤ Subgroup.normalizer (Subgroup.zpowers t : Set X) := fun v hv =>
    mem_normalizer_of_forall_conj_mem fun s hs => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      rw [(Commute.zpow_right (hVt v hv) n).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers t n
  have hg' : g ∈ ((V ⊔ Subgroup.zpowers t : Subgroup X) : Set X) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hg'
  obtain ⟨v, hv, s, hs, rfl⟩ := hg'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  rcases zpow_eq_one_or_self htt n with h | h <;> rw [h]
  · exact ⟨v, hv, Or.inl (mul_one v)⟩
  · exact ⟨v, hv, Or.inr rfl⟩

end General

variable {G : Type} [Group G]

@[expose] noncomputable def e1GBar (Z : Subgroup G) [Z.Normal] (u m y x : G) (τ : G ⧸ Z) :
    Subgroup (G ⧸ Z) :=
  e1VBar Z u m y x ⊔ Subgroup.zpowers (τ * caseC3Word Z u m y x 20 * τ⁻¹)

namespace CaseC3BCD

variable {T Q P₁ S : Subgroup G} {e u y x m : G} {Z : Subgroup G} [Z.Normal]
  (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G] {τ : G ⧸ Z}
  (hτN : τ ∈ e1NBar Z u m y x)
  (hτfpf : ∀ s ∈ e1RBar Z u m y x, s ≠ 1 → s ≠ caseC3Word Z u m y x 40 →
    τ * s * τ⁻¹ ≠ s ∧ τ * s * τ⁻¹ ≠ s * caseC3Word Z u m y x 40)
  (hτ3 : ∀ s ∈ e1RBar Z u m y x, τ ^ 3 * s = s * τ ^ 3)
include hb hτN hτfpf hτ3

theorem e1GBar_prod :
    caseC3Word Z u m y x 20 * (τ * caseC3Word Z u m y x 20 * τ⁻¹) *
        (τ * (τ * caseC3Word Z u m y x 20 * τ⁻¹) * τ⁻¹) = 1 ∨
      caseC3Word Z u m y x 20 * (τ * caseC3Word Z u m y x 20 * τ⁻¹) *
        (τ * (τ * caseC3Word Z u m y x 20 * τ⁻¹) * τ⁻¹) = caseC3Word Z u m y x 40 := by
  set zb := caseC3Word Z u m y x 40 with hzb
  set r := caseC3Word Z u m y x 20 with hr
  set r' := τ * r * τ⁻¹ with hr'
  set r'' := τ * r' * τ⁻¹ with hr''
  have hR := conj_mem_of_mem_e1NBar hτN
  have hrR : r ∈ e1RBar Z u m y x := hb.caseC3Word_mem_e1RBar_iff.mpr (by decide)
  have hr'R := hR r hrR
  have hr''R := hR r' hr'R
  have h3 : τ * r'' * τ⁻¹ = r := by
    have h := hτ3 r hrR
    rw [pow_three] at h
    calc τ * r'' * τ⁻¹ = τ * (τ * τ) * r * (τ * (τ * τ))⁻¹ := by rw [hr'', hr']; group
      _ = r := by rw [h, mul_inv_cancel_right]
  have hpR : r * r' * r'' ∈ e1RBar Z u m y x := Subgroup.mul_mem _ (Subgroup.mul_mem _ hrR hr'R)
    hr''R
  have hconj : τ * (r * r' * r'') * τ⁻¹ = r' * r'' * r := by
    rw [show τ * (r * r' * r'') * τ⁻¹ = (τ * r * τ⁻¹) * (τ * r' * τ⁻¹) * (τ * r'' * τ⁻¹) by group,
      h3]
  have hzz : zb * zb = 1 := hb.forty_mul_self
  by_contra hne
  obtain ⟨hne1, hne2⟩ := hτfpf _ hpR (fun h => hne (Or.inl h)) (fun h => hne (Or.inr h))
  rcases hb.commute_or_of_mem_e1RBar hrR (Subgroup.mul_mem _ hr'R hr''R) with h | h
  · exact hne1 (by rw [hconj, mul_assoc r, h])
  · refine hne2 ?_
    rw [hconj, mul_assoc r, h, mul_assoc (r' * r'' * r), hzz, mul_one]

theorem e1GBar_commute :
    caseC3Word Z u m y x 20 * (τ * caseC3Word Z u m y x 20 * τ⁻¹) =
      τ * caseC3Word Z u m y x 20 * τ⁻¹ * caseC3Word Z u m y x 20 := by
  set zb := caseC3Word Z u m y x 40 with hzb
  set r := caseC3Word Z u m y x 20 with hr
  set r' := τ * r * τ⁻¹ with hr'
  set r'' := τ * r' * τ⁻¹ with hr''
  have hrr : r * r = 1 := hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide)
  have hr'r' : r' * r' = 1 := conj_mul_self_eq_one hrr τ
  have hr''r'' : r'' * r'' = 1 := conj_mul_self_eq_one hr'r' τ
  have hR := conj_mem_of_mem_e1NBar hτN
  have hr''R : r'' ∈ e1RBar Z u m y x :=
    hR _ (hR r (hb.caseC3Word_mem_e1RBar_iff.mpr (by decide)))
  obtain ⟨p, hp, hpc, hpp⟩ : ∃ p, r * r' * r'' = p ∧ p * r'' = r'' * p ∧ p * p = 1 := by
    rcases hb.e1GBar_prod hτN hτfpf hτ3 with h | h
    · exact ⟨1, h, by group, mul_one 1⟩
    · exact ⟨zb, h, (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) _ hr''R,
        hb.forty_mul_self⟩
  have h1 : r * r' = p * r'' := by
    rw [← hp, mul_assoc (r * r'), hr''r'', mul_one]
  have h2 : r * r' * (r * r') = 1 := by
    rw [h1, show p * r'' * (p * r'') = p * (r'' * p) * r'' by group, ← hpc,
      show p * (p * r'') * r'' = p * p * (r'' * r'') by group, hpp, hr''r'', one_mul]
  calc r * r' = r * r' * (r * r') * (r' * r) := by
        rw [show r * r' * (r * r') * (r' * r) = r * r' * (r * (r' * r') * r) by group, hr'r',
          mul_one, hrr, mul_one]
    _ = r' * r := by rw [h2, one_mul]

omit hτfpf hτ3 in
theorem commute_of_mem_e1VBar (hcomm : caseC3Word Z u m y x 20 * (τ * caseC3Word Z u m y x 20 *
      τ⁻¹) = τ * caseC3Word Z u m y x 20 * τ⁻¹ * caseC3Word Z u m y x 20) {v : G ⧸ Z}
    (hv : v ∈ e1VBar Z u m y x) :
    v * (τ * caseC3Word Z u m y x 20 * τ⁻¹) = τ * caseC3Word Z u m y x 20 * τ⁻¹ * v := by
  have hR := conj_mem_of_mem_e1NBar hτN
  have hr'R := hR _ (hb.caseC3Word_mem_e1RBar_iff.mpr (by decide : e1R 20))
  have hz := (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) _ hr'R
  obtain ⟨t, ht, rfl⟩ := hb.mem_e1VBar_iff.mp hv
  rcases ht with rfl | rfl | rfl | rfl
  · rw [caseC3Word_zero, one_mul, mul_one]
  · exact hcomm
  · exact hz
  · rw [show (60 : Fin 64) = c3Mul 20 40 by decide, ← hb.caseC3Word_mul]
    exact (Commute.mul_left (hcomm : Commute _ _) (hz : Commute _ _)).eq

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
