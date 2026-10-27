module

public import CFSG.CGT.PushingUpLit.A78Sp4.Coord

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open scoped commutatorElement

variable {K : Type*} [Field K] {G : Type*} [Group G] {J : Subgroup G}

theorem z1_elem [CharP K 2] [Finite K] (c : Cls2Coord K J) {S Q : Subgroup G}
    (hJS : J ≤ S) (hJn : ∀ s ∈ S, ∀ x ∈ J, s * x * s⁻¹ ∈ J)
    (hQn : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    {g : G} (hgS : g ∈ S) (hgQ : g ∈ Q) (hact : 4 < (commSet c g).ncard) :
    ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  let A : AddSubgroup (K × K) :=
    { carrier := {z | ∃ q ∈ Q, q ∈ J ∧ c.π q = 0 ∧ c.ζ q = z}
      zero_mem' := ⟨1, Q.one_mem, J.one_mem, c.π_one, c.ζ_one⟩
      add_mem' := by
        rintro _ _ ⟨q₁, h1Q, h1J, h1π, rfl⟩ ⟨q₂, h2Q, h2J, h2π, rfl⟩
        exact ⟨q₁ * q₂, Q.mul_mem h1Q h2Q, J.mul_mem h1J h2J,
          by rw [c.π_mul _ h1J _ h2J, h1π, h2π, add_zero], c.ζ_mul _ h1J h1π _ h2J h2π⟩
      neg_mem' := by
        rintro _ ⟨q, hQ, hJ, hπ, rfl⟩
        exact ⟨q⁻¹, Q.inv_mem hQ, J.inv_mem hJ, by rw [c.π_inv hJ, hπ, neg_zero], c.ζ_inv hJ hπ⟩ }
  have hpolar : ∀ x ∈ commSet c g, ∀ y : K × K, beta x y ∈ A := by
    rintro x ⟨y₀, hy₀, rfl⟩ y
    obtain ⟨w, hwJ, hwπ⟩ := c.π_surj y
    have heJ : ⁅g, y₀⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (hJn g hgS y₀ hy₀) (J.inv_mem hy₀)
    have heQ : ⁅g, y₀⁆ ∈ Q := by
      have h1 := hQn y₀ (hJS hy₀) g⁻¹ (Q.inv_mem hgQ)
      have : ⁅g, y₀⁆ = g * (y₀ * g⁻¹ * y₀⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]; exact Q.mul_mem hgQ h1
    have hweQ : ⁅⁅g, y₀⁆, w⁆ ∈ Q := by
      have h1 := hQn w (hJS hwJ) _ (Q.inv_mem heQ)
      have : ⁅⁅g, y₀⁆, w⁆ = ⁅g, y₀⁆ * (w * (⁅g, y₀⁆)⁻¹ * w⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [this]; exact Q.mul_mem heQ h1
    have hweJ : ⁅⁅g, y₀⁆, w⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem heJ hwJ) (J.inv_mem heJ)) (J.inv_mem hwJ)
    obtain ⟨h1, h2⟩ := c.comm _ heJ w hwJ
    exact ⟨_, hweQ, hweJ, h1, by rw [h2, hwπ]⟩
  have hA : A = ⊤ := by
    rw [eq_top_iff, ← polar_span_eq_top (commSet c g) hact]
    apply (AddSubgroup.closure_le A).2
    rintro z ⟨x, hx, y, rfl⟩
    exact hpolar x hx y
  intro z hzJ hz0
  have hz : c.ζ z ∈ A := by rw [hA]; trivial
  obtain ⟨q, hqQ, hqJ, hqπ, hqζ⟩ := hz
  rw [← c.ζ_inj q hqJ hqπ z hzJ hz0 hqζ]
  exact hqQ

theorem z1_inJ (c : Cls2Coord K J) {S Q : Subgroup G} (hJS : J ≤ S) (hQJ : Q ≤ J)
    (hcent : ∀ s ∈ S, (∀ x ∈ Q, s * x = x * s) → s ∈ Q) :
    ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  intro z hz h0
  exact hcent z (hJS hz) fun x hx => c.ker_central hz h0 (hQJ hx)

theorem z1 [CharP K 2] [Finite K] (c : Cls2Coord K J) {S Q : Subgroup G}
    (hJS : J ≤ S) (hJn : ∀ s ∈ S, ∀ x ∈ J, s * x * s⁻¹ ∈ J)
    (hact : ∀ s ∈ S, s ∉ J → 4 < (commSet c s).ncard)
    (hQS : Q ≤ S) (hQn : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    (hcent : ∀ s ∈ S, (∀ x ∈ Q, s * x = x * s) → s ∈ Q) :
    ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  by_cases hQJ : Q ≤ J
  · exact z1_inJ c hJS hQJ hcent
  · obtain ⟨g, hgQ, hgJ⟩ := Set.not_subset.mp hQJ
    exact z1_elem c hJS hJn hQn (hQS hgQ) hgQ (hact g (hQS hgQ) hgJ)

end CFSG.CGT.PushingUpLit.A78Sp4
