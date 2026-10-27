module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsCtx

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

namespace Lemma113Claims

namespace Gamma

variable {G : Type} [Group G] [Finite G]

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem mem_normalizer_E (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {q : G} (hq : q ∈ Q) : q ∈ Subgroup.normalizer (E : Set G) := by
  apply mem_normalizer_of_conj_le
  intro y hy
  have h1 : q * y * q⁻¹ * y⁻¹ ∈ E := c.Q0_le_E (c.comm_mem_Q0 hB q hq y (c.hEQ hy))
  have h2 : q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
  rw [h2]
  exact E.mul_mem h1 hy

theorem exists_mul_of_mem_Q (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {w : G} (hwQ : w ∈ Q) : ∃ z ∈ E, ∃ a ∈ A, z * a = w := by
  obtain ⟨b, hbA, hbE⟩ := SetLike.not_le_iff_exists.1 c.hAnE
  have hb3 : b ^ 3 = 1 := c.hAel.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ E.one_mem)
  have hbQ : b ∈ Q := c.hAQ hbA
  have hbN : b ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_E c hB hbQ
  have hzb : Subgroup.zpowers b ≤ Subgroup.normalizer (E : Set G) := Subgroup.zpowers_le.2 hbN
  have hQeq : E ⊔ Subgroup.zpowers b = Q := by
    have hle : E ⊔ Subgroup.zpowers b ≤ Q := sup_le c.hEQ (Subgroup.zpowers_le.2 hbQ)
    have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers b : Subgroup G) = 3 * Nat.card ↥E :=
      l113_card_sup_zpowers E hb3 hb1 hbE hzb
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, c.card_Q hB, c.hEcard]; norm_num)
  have hwmem : w ∈ (E : Set G) * (Subgroup.zpowers b : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left E (Subgroup.zpowers b) hzb]
    change w ∈ (E ⊔ Subgroup.zpowers b : Subgroup G)
    rw [hQeq]
    exact hwQ
  obtain ⟨z, hzE, a, haB, hza⟩ := hwmem
  exact ⟨z, hzE, a, Subgroup.zpowers_le.2 hbA haB, hza⟩

theorem cube_mul_eq_one (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {z a : G} (hzE : z ∈ E) (haA : a ∈ A) (hzA : ∀ x ∈ A, z * x * z⁻¹ ∈ A) :
    (z * a) ^ 3 = 1 := by
  have haQ : a ∈ Q := c.hAQ haA
  have hzQ : z ∈ Q := c.hEQ hzE
  have ha3 : a * a * a = 1 := by rw [← pow_three']; exact c.hAel.2 a haA
  have hz3 : z * z * z = 1 := by rw [← pow_three']; exact c.hEel.2 z hzE
  obtain ⟨d, hd⟩ : ∃ d : G, d = a * z * a⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hdQ0 : d ∈ (Q ⊓ K : Subgroup G) := hd ▸ c.comm_mem_Q0 hB a haQ z hzQ
  have hdE : d ∈ E := c.Q0_le_E hdQ0
  have hd3 : d * d * d = 1 := by rw [← pow_three']; exact c.Q0_elemAbelian.2 d hdQ0
  have hdA : d ∈ A := by
    have h1 : z * a * z⁻¹ * a⁻¹ ∈ A := A.mul_mem (hzA a haA) (A.inv_mem haA)
    have h2 : d = (z * a * z⁻¹ * a⁻¹)⁻¹ := by rw [hd]; group
    rw [h2]
    exact A.inv_mem h1
  have hda : d * a = a * d := Lemma113f.comm_of_isElemAbelian c.hAel hdA haA
  have hdz : d * z = z * d := Lemma113f.comm_of_isElemAbelian c.hEel hdE hzE
  have h1 : a * z * a⁻¹ = d * z := by rw [hd]; group
  have had : a * d * a⁻¹ = d := by rw [← hda]; group
  have h2 : a * a * z * (a * a)⁻¹ = d * d * z := by
    calc a * a * z * (a * a)⁻¹ = a * (a * z * a⁻¹) * a⁻¹ := by group
      _ = a * (d * z) * a⁻¹ := by rw [h1]
      _ = (a * d * a⁻¹) * (a * z * a⁻¹) := by group
      _ = d * d * z := by rw [had, h1]; group
  have h3 : (z * a) ^ 3 =
      z * (a * z * a⁻¹) * (a * a * z * (a * a)⁻¹) * (a * a * a) := by
    rw [pow_three']
    group
  have hcomm : Commute (d * d) z := (show Commute d z from hdz).mul_left (show Commute d z from hdz)
  rw [h3, ha3, h1, h2]
  calc z * (d * z) * (d * d * z) * 1 = z * d * (z * (d * d)) * z := by group
    _ = z * d * (d * d * z) * z := by rw [← hcomm.eq]
    _ = z * (d * d * d) * (z * z) := by group
    _ = z * z * z := by rw [hd3]; group
    _ = 1 := hz3

theorem normalizer_A_cube {G : Type} [Group G] [Finite G] {E A : Subgroup G} {e : G}
    {K Q : Subgroup G} (c : Lemma113Claims.Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {w : G} (hwQ : w ∈ Q) (hwA : ∀ a ∈ A, w * a * w⁻¹ ∈ A) : w ^ 3 = 1 := by
  obtain ⟨z, hzE, a, haA, hza⟩ := exists_mul_of_mem_Q c hB hwQ
  subst hza
  have hzA : ∀ x ∈ A, z * x * z⁻¹ ∈ A := by
    intro x hx
    have h := hwA (a⁻¹ * x * a) (A.mul_mem (A.mul_mem (A.inv_mem haA) hx) haA)
    have e1 : z * a * (a⁻¹ * x * a) * (z * a)⁻¹ = z * x * z⁻¹ := by group
    rwa [e1] at h
  exact cube_mul_eq_one c hB hzE haA hzA

end Gamma

end Lemma113Claims

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
