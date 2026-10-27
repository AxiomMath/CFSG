module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_hcl (h : L41GPh17 t L S x₁ x₂ lam rho) {V₂ : Subgroup G}
    (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hCt : ∀ c ∈ V₂, c * t = t * c → c ∈ l41V1 t x₁ x₂ rho lam)
    {z : G} (hz : z ∈ V₂) {k : G} (hk : k ∈ l41Q1 t x₁ x₂ rho) (hzt : t * z * t⁻¹ = z * k) :
    z ∈ l41V1 t x₁ x₂ rho lam := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htM : t ∈ l41M t x₁ x₂ rho :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hnorm : ∀ q ∈ l41Q1 t x₁ x₂ rho, t * q * t⁻¹ ∈ l41Q1 t x₁ x₂ rho := fun q hq =>
    h.q1facts.normal_Q1.2 t htM q hq
  have hQ1Q : l41Q1 t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho := by
    rw [h.q1facts.Q_eq]
    exact le_sup_left
  have hQV₁ : l41Q t x₁ x₂ rho ≤ l41V1 t x₁ x₂ rho lam := by
    rw [h.q1facts.Q_eq]
    exact sup_le (le_sup_left)
      (le_sup_of_le_right (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))))
  obtain ⟨k', hk'def⟩ : ∃ k', k' = t * k * t⁻¹ := ⟨_, rfl⟩
  have hk'Q₁ : k' ∈ l41Q1 t x₁ x₂ rho := hk'def ▸ hnorm k hk
  have hconj : z⁻¹ * t * z = t * k' := by
    have h1 : t * z = z * k * t := by
      have := congrArg (· * t) hzt
      simpa [mul_assoc, htinv, ht2] using this
    rw [hk'def, htinv]
    calc z⁻¹ * t * z = z⁻¹ * (t * z) := by group
      _ = z⁻¹ * (z * k * t) := by rw [h1]
      _ = k * t := by group
      _ = t * (t * k * t) := by
          calc k * t = (t * t) * k * t := by rw [ht2, one_mul]
            _ = t * (t * k * t) := by group
  have hinv : (t * k') * (t * k') = 1 := by
    rw [← hconj]
    calc z⁻¹ * t * z * (z⁻¹ * t * z) = z⁻¹ * (t * t) * z := by group
      _ = 1 := by rw [ht2]; group
  have hk'inv : k'⁻¹ = t * k' * t := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    calc t * k' * t * k' = (t * k') * (t * k') := by group
      _ = 1 := hinv
  have hcomm : ⁅k', t⁆ ∈ l41Y t x₁ x₂ rho := by
    have e : ⁅k', t⁆ = k' * k' := by
      rw [commutatorElement_def, hk'inv, htinv]
      calc k' * t * (t * k' * t) * t = k' * (t * t) * k' * (t * t) := by group
        _ = k' * k' := by rw [ht2]; group
    rw [e]
    exact h.q1elem k' hk'Q₁
  have hmem : k' ∈ ((ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [← h.qfacts.cent_Qbar_t]
    exact ⟨hQ1Q hk'Q₁, hcomm⟩
  have hk'F : k' ∈ l41F t x₁ x₂ rho :=
    sup_le (m13_W_le_F h.toL41GPh8) ((m13_Y_le_R t x₁ x₂ rho).trans le_sup_left) hmem
  have hk'R : k' ∈ l41R t x₁ x₂ rho := by
    rcases m13_mem_F h.toL41GPh8 hk'F with hR | ⟨r, hr, hkr⟩
    · exact hR
    · exfalso
      apply h.q1facts.t_not_mem
      have htk : t = k' * r⁻¹ := by rw [hkr]; group
      have h' : k' * r⁻¹ ∈ l41Q1 t x₁ x₂ rho :=
        (l41Q1 t x₁ x₂ rho).mul_mem hk'Q₁ ((l41Q1 t x₁ x₂ rho).inv_mem (h.q1facts.R_le hr))
      rwa [← htk] at h'
  have horb : t * k' ∈ conjIn (l41Q t x₁ x₂ rho) t := by
    rw [h.qfacts.orbit_t]
    exact ⟨⟨k', hk'R, rfl⟩, hinv⟩
  obtain ⟨g, hgQ, hg⟩ := horb
  have hc : (z * g) * t = t * (z * g) := by
    have h1 : z⁻¹ * t * z = g * t * g⁻¹ := by rw [hconj, hg]
    calc z * g * t = z * (g * t * g⁻¹) * g := by group
      _ = z * (z⁻¹ * t * z) * g := by rw [h1]
      _ = t * (z * g) := by group
  have hgV₂ : g ∈ V₂ := hV₁ (hQV₁ hgQ)
  have hzg := hCt (z * g) ((V₂).mul_mem hz hgV₂) hc
  have : z = (z * g) * g⁻¹ := by group
  rw [this]
  exact (l41V1 t x₁ x₂ rho lam).mul_mem hzg ((l41V1 t x₁ x₂ rho lam).inv_mem (hQV₁ hgQ))

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
