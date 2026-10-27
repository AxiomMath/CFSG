module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsOdd

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def e1Special (gf : Bool) : Fin 64 := if gf then 20 else 28

theorem e1Special_spec : ∀ gf gef : Bool, (gf && gef) = false → (gf || gef) = true →
    e1Sing (e1Special gf) ∧ e1Gen gf gef (e1Special gf) = true ∧
      ∀ w : Fin 64, e1Sing w → e1Gen gf gef w = true →
        c3Mul (e1Special gf) w = c3Mul w (e1Special gf) := by decide +kernel

theorem e1Special_unique : ∀ gf gef : Bool, (gf && gef) = false → (gf || gef) = true →
    ∀ v : Fin 64, e1Sing v → e1Gen gf gef v = true →
      (∀ w : Fin 64, e1Sing w → e1Gen gf gef w = true → c3Mul v w = c3Mul w v) →
      v = e1Special gf ∨ v = c3Mul (e1Special gf) 40 := by decide +kernel

theorem e1_typeB_sing : ∀ v : Fin 64, e1Sing v → e1Gen false false v = true →
    (v = 20 ∨ v = 60) ∨ (v = 28 ∨ v = 52) := by decide

theorem e1_typeB_facts : e1Sing 20 ∧ e1Gen false false 20 = true ∧ c3Mul 20 40 = 60 ∧
    ∀ v w : Fin 64, (v = 28 ∨ v = 52) → (w = 28 ∨ w = 52) → v = w ∨ v = c3Mul w 40 := by decide

theorem pow_conj_mem_of_conj_mem {M : Type*} [Group M] {K : Subgroup M} {g : M}
    (hg : ∀ s ∈ K, g * s * g⁻¹ ∈ K) (j : ℕ) : ∀ s ∈ K, g ^ j * s * (g ^ j)⁻¹ ∈ K := by
  induction j with
  | zero => intro s hs; simpa using hs
  | succ j ih =>
    intro s hs
    have h := hg _ (ih s hs)
    rwa [show g * (g ^ j * s * (g ^ j)⁻¹) * g⁻¹ = g ^ (j + 1) * s * (g ^ (j + 1))⁻¹ by group]
      at h

namespace CaseC3BCD

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}
variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem commute_of_odd_typeC {gf gef : Bool} (hgg : (gf && gef) = false)
    (hor : (gf || gef) = true)
    (hlab : ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true)
    {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) :
    ∀ s ∈ e1RBar Z u m y x, g * s = s * g := by
  obtain ⟨hs₀, hs₀g, hs₀c⟩ := e1Special_spec gf gef hgg hor
  have hginv : g⁻¹ = g ^ (k - 1) := (eq_inv_of_mul_eq_one_left (by
    rw [← pow_succ, Nat.sub_add_cancel hk.pos, hgk])).symm
  have hgR' : ∀ s ∈ e1RBar Z u m y x, g⁻¹ * s * g⁻¹⁻¹ ∈ e1RBar Z u m y x := by
    rw [hginv]
    exact pow_conj_mem_of_conj_mem hgR (k - 1)
  obtain ⟨v₁, hv₁, hv₁g, hv₁e⟩ := hb.exists_conj_sing hgR hlab hs₀ hs₀g
  have hv₁c : ∀ w, e1Sing w → e1Gen gf gef w = true → c3Mul v₁ w = c3Mul w v₁ := by
    intro w hw hwg
    obtain ⟨w', hw', hw'g, hw'e⟩ := hb.exists_conj_sing hgR' hlab hw hwg
    have hww : caseC3Word Z u m y x w = g * caseC3Word Z u m y x w' * g⁻¹ := by
      rw [← hw'e]
      group
    rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul, ← hv₁e, hww,
      show g * caseC3Word Z u m y x (e1Special gf) * g⁻¹ * (g * caseC3Word Z u m y x w' * g⁻¹) =
        g * (caseC3Word Z u m y x (e1Special gf) * caseC3Word Z u m y x w') * g⁻¹ by group,
      show g * caseC3Word Z u m y x w' * g⁻¹ * (g * caseC3Word Z u m y x (e1Special gf) * g⁻¹) =
        g * (caseC3Word Z u m y x w' * caseC3Word Z u m y x (e1Special gf)) * g⁻¹ by group,
      hb.caseC3Word_mul, hb.caseC3Word_mul, hs₀c w' hw' hw'g]
  obtain ⟨hr, hrr, hr1, hrz⟩ := hb.sing_iff.mpr hs₀
  refine hb.commute_of_odd hk hgk hgR hr hrr hr1 hrz ?_
  rcases e1Special_unique gf gef hgg hor v₁ hv₁ hv₁g hv₁c with h | h
  · exact Or.inl (by rw [hv₁e, h])
  · exact Or.inr (by rw [hv₁e, h, hb.caseC3Word_mul])

theorem commute_of_odd_typeB
    (hlab : ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen false false v = true)
    {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) :
    ∀ s ∈ e1RBar Z u m y x, g * s = s * g := by
  obtain ⟨h20, h20g, h2060, hB⟩ := e1_typeB_facts
  have hF40 := hb.conj_forty_of_normalizes hgR
  have hinj : ∀ a b : G ⧸ Z, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  obtain ⟨v₁, hv₁, hv₁g, hv₁e⟩ := hb.exists_conj_sing hgR hlab h20 h20g
  obtain ⟨hr, hrr, hr1, hrz⟩ := hb.sing_iff.mpr h20
  rcases e1_typeB_sing v₁ hv₁ hv₁g with hA | hB₁
  · refine hb.commute_of_odd hk hgk hgR hr hrr hr1 hrz ?_
    rcases hA with h | h
    · exact Or.inl (by rw [hv₁e, h])
    · exact Or.inr (by rw [hv₁e, h, hb.caseC3Word_mul, h2060])
  obtain ⟨v₂, hv₂, hv₂g, hv₂e⟩ := hb.exists_conj_sing hgR hlab hv₁ hv₁g
  have hv₂A : v₂ = 20 ∨ v₂ = 60 := by
    rcases e1_typeB_sing v₂ hv₂ hv₂g with h | h
    · exact h
    exfalso
    rcases hB v₂ v₁ h hB₁ with h' | h'
    · have h'' : caseC3Word Z u m y x v₁ = caseC3Word Z u m y x 20 :=
        hinj _ _ (by rw [hv₂e, h', hv₁e])
      rw [hb.caseC3Word_inj] at h''
      rcases hB₁ with h₃ | h₃ <;> rw [h₃] at h'' <;> exact absurd h'' (by decide)
    · have h'' : caseC3Word Z u m y x v₁ = caseC3Word Z u m y x 60 := by
        refine hinj _ _ ?_
        calc g * caseC3Word Z u m y x v₁ * g⁻¹
            = caseC3Word Z u m y x v₁ * caseC3Word Z u m y x 40 := by
              rw [hv₂e, h', hb.caseC3Word_mul]
          _ = (g * caseC3Word Z u m y x 20 * g⁻¹) * (g * caseC3Word Z u m y x 40 * g⁻¹) := by
              rw [hv₁e, hF40]
          _ = g * caseC3Word Z u m y x 60 * g⁻¹ := by
              rw [← h2060, ← hb.caseC3Word_mul]
              group
      rw [hb.caseC3Word_inj] at h''
      rcases hB₁ with h₃ | h₃ <;> rw [h₃] at h'' <;> exact absurd h'' (by decide)
  have hg2 : ∀ s ∈ e1RBar Z u m y x, g ^ 2 * s = s * g ^ 2 := by
    have hconj2 : g ^ 2 * caseC3Word Z u m y x 20 * (g ^ 2)⁻¹ = caseC3Word Z u m y x v₂ := by
      rw [← hv₂e, ← hv₁e, pow_two]
      group
    refine hb.commute_of_odd hk (by rw [← pow_mul, mul_comm, pow_mul, hgk, one_pow])
      (pow_conj_mem_of_conj_mem hgR 2) hr hrr hr1 hrz ?_
    rcases hv₂A with h | h
    · exact Or.inl (by rw [hconj2, h])
    · exact Or.inr (by rw [hconj2, h, hb.caseC3Word_mul, h2060])
  obtain ⟨j, hj⟩ := hk
  have hgs : g = (g ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = k + 1 by omega, pow_succ, hgk, one_mul]
  intro s hs
  rw [hgs]
  exact ((show Commute (g ^ 2) s from hg2 s hs).pow_left (j + 1)).eq

theorem commute_of_odd_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) :
    ∀ s ∈ e1RBar Z u m y x, g * s = s * g := by
  obtain ⟨gf, gef, hgg, -, -, hlab⟩ := hb.exists_e1Gen_of_not_typeD htype
  cases hor : (gf || gef)
  · obtain ⟨rfl, rfl⟩ : gf = false ∧ gef = false := by
      revert hor
      cases gf <;> cases gef <;> simp
    exact hb.commute_of_odd_typeB hlab hk hgk hgR
  · exact hb.commute_of_odd_typeC hgg hor hlab hk hgk hgR

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
