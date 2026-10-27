module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf

open QuaternionGroup

abbrev zQ : QuaternionGroup 2 := QuaternionGroup.a 2

theorem q8_cover : ∀ a b c : QuaternionGroup 2,
    a ≠ 1 → a ≠ zQ → b ≠ 1 → b ≠ zQ → c ≠ 1 → c ≠ zQ →
    a ≠ b → a ≠ b * zQ → a ≠ c → a ≠ c * zQ → b ≠ c → b ≠ c * zQ →
    (a * b * c = 1 ∨ a * b * c = zQ) ∧
    ∀ k : QuaternionGroup 2, k = 1 ∨ k = zQ ∨ k = a ∨ k = a * zQ ∨
      k = b ∨ k = b * zQ ∨ k = c ∨ k = c * zQ := by
  decide +kernel

theorem q8_sq : ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = zQ := by
  decide +kernel

theorem q8_comm : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
    (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = zQ := by decide +kernel

theorem q8_inv_eq : ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = zQ := by decide +kernel

theorem q8_aux1 : ∀ p : QuaternionGroup 2, p * (p * zQ)⁻¹ = zQ := by decide +kernel

theorem q8_aux2 : ∀ p : QuaternionGroup 2, p * zQ * zQ = p := by decide +kernel

theorem q8_cycle_conds (σ : QuaternionGroup 2 → QuaternionGroup 2)
    (hmul : ∀ p q, σ (p * q) = σ p * σ q) (hz : σ zQ = zQ) (h3 : ∀ q, σ (σ (σ q)) = q)
    {a : QuaternionGroup 2} (h1 : σ a * a⁻¹ ≠ 1) (h2 : σ a * a⁻¹ ≠ zQ) :
    a ≠ 1 ∧ a ≠ zQ ∧ σ a ≠ 1 ∧ σ a ≠ zQ ∧ σ (σ a) ≠ 1 ∧ σ (σ a) ≠ zQ ∧
    a ≠ σ a ∧ a ≠ σ a * zQ ∧ a ≠ σ (σ a) ∧ a ≠ σ (σ a) * zQ ∧
    σ a ≠ σ (σ a) ∧ σ a ≠ σ (σ a) * zQ := by
  have hone : σ 1 = 1 := by
    have := hmul 1 1
    simpa using this
  have c1 : a ≠ 1 := by
    intro h; apply h1; rw [h, hone]; simp
  have c2 : a ≠ zQ := by
    intro h; apply h1; rw [h, hz, mul_inv_cancel]
  have c3 : σ a ≠ 1 := by
    intro h; apply c1; rw [← h3 a, h, hone, hone]
  have c4 : σ a ≠ zQ := by
    intro h; apply c2; rw [← h3 a, h, hz, hz]
  have c5 : σ (σ a) ≠ 1 := by
    intro h; apply c1; rw [← h3 a, h, hone]
  have c6 : σ (σ a) ≠ zQ := by
    intro h; apply c2; rw [← h3 a, h, hz]
  have c7 : a ≠ σ a := by
    intro h; apply h1; rw [← h, mul_inv_cancel]
  have c8 : a ≠ σ a * zQ := by
    intro h; apply h2
    have := q8_aux1 (σ a)
    rwa [← h] at this
  have c9 : a ≠ σ (σ a) := by
    intro h
    have := congrArg σ h
    rw [h3 a] at this
    exact c7 this.symm
  have c10 : a ≠ σ (σ a) * zQ := by
    intro h
    have h' : σ a = a * zQ := by
      have := congrArg σ h
      rw [hmul, h3, hz] at this
      exact this
    exact c8 (by rw [h', q8_aux2])
  have c11 : σ a ≠ σ (σ a) := by
    intro h
    have := congrArg σ h
    rw [h3 a] at this
    exact c9 this.symm
  have c12 : σ a ≠ σ (σ a) * zQ := by
    intro h
    have h' : σ (σ a) = a * zQ := by
      have := congrArg σ h
      rw [hmul, h3, hz] at this
      exact this
    exact c10 (by rw [h', q8_aux2])
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩

theorem q8_kill {A : Type*} [CommGroup A] (ψ : QuaternionGroup 2 →* A)
    (σ : QuaternionGroup 2 → QuaternionGroup 2)
    (hmul : ∀ p q, σ (p * q) = σ p * σ q) (hz : σ zQ = zQ) (h3 : ∀ q, σ (σ (σ q)) = q)
    (hψ : ∀ q, ψ (σ q) = ψ q)
    {a : QuaternionGroup 2} (h1 : σ a * a⁻¹ ≠ 1) (h2 : σ a * a⁻¹ ≠ zQ) :
    ∀ k, ψ k = 1 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := q8_cycle_conds σ hmul hz h3 h1 h2
  obtain ⟨hprod, hcov⟩ := q8_cover a (σ a) (σ (σ a)) c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  have key : ∀ u v : QuaternionGroup 2, ψ (u * v * u⁻¹ * v⁻¹) = 1 := fun u v => by
    simp only [map_mul, map_inv]
    rw [mul_comm (ψ u) (ψ v)]
    group
  have hψz : ψ zQ = 1 := by
    rw [← q8_comm]
    exact key _ _
  have hsq : ψ a * ψ a = 1 := by
    rw [← map_mul]
    rcases q8_sq a with h | h
    · rw [h, map_one]
    · rw [h, hψz]
  have hcube : ψ a * ψ a * ψ a = 1 := by
    have : ψ (a * σ a * σ (σ a)) = 1 := by
      rcases hprod with h | h
      · rw [h, map_one]
      · rw [h, hψz]
    simpa only [map_mul, hψ] using this
  have hψa : ψ a = 1 := by
    rw [hsq, one_mul] at hcube
    exact hcube
  intro k
  rcases hcov k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [map_mul, hψ, hψa, hψz]

theorem le_commutator_of_threeCycle {G : Type*} [Group G] {H R : Subgroup G} {t x : G}
    (hRH : R ≤ H) (hxH : x ∈ H) (e : ↥R ≃* QuaternionGroup 2)
    (het : ((e.symm zQ : ↥R) : G) = t)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hx3 : x ^ 3 = 1) (hxt : x * t * x⁻¹ = t)
    (hact : ∃ r ∈ R, x * r * x⁻¹ * r⁻¹ ≠ 1 ∧ x * r * x⁻¹ * r⁻¹ ≠ t) :
    R ≤ ⁅H, H⁆ := by
  classical
  let ab : ↥H →* Abelianization ↥H := Abelianization.of
  let incl : ↥R →* ↥H := Subgroup.inclusion hRH
  let ψ : QuaternionGroup 2 →* Abelianization ↥H := (ab.comp incl).comp e.symm.toMonoidHom
  let σ : QuaternionGroup 2 → QuaternionGroup 2 :=
    fun q => e ⟨x * ((e.symm q : ↥R) : G) * x⁻¹, hxR _ (e.symm q).2⟩
  have hσ : ∀ q, ((e.symm (σ q) : ↥R) : G) = x * ((e.symm q : ↥R) : G) * x⁻¹ := by
    intro q
    simp only [σ, MulEquiv.symm_apply_apply]
  have hσmul : ∀ p q, σ (p * q) = σ p * σ q := by
    intro p q
    apply e.symm.injective
    apply Subtype.ext
    rw [hσ, map_mul, Subgroup.coe_mul, map_mul, Subgroup.coe_mul, hσ, hσ]
    group
  have hσz : σ zQ = zQ := by
    apply e.symm.injective
    apply Subtype.ext
    rw [hσ, het, hxt]
  have hσ3 : ∀ q, σ (σ (σ q)) = q := by
    intro q
    apply e.symm.injective
    apply Subtype.ext
    rw [hσ, hσ, hσ]
    have h111 : x * x * x = 1 := by rw [← pow_three']; exact hx3
    calc x * (x * (x * ((e.symm q : ↥R) : G) * x⁻¹) * x⁻¹) * x⁻¹
        = (x * x * x) * ((e.symm q : ↥R) : G) * (x * x * x)⁻¹ := by group
      _ = ((e.symm q : ↥R) : G) := by rw [h111]; group
  have hψσ : ∀ q, ψ (σ q) = ψ q := by
    intro q
    have h1 : ψ (σ q) = ab ⟨x * ((e.symm q : ↥R) : G) * x⁻¹, hRH (hxR _ (e.symm q).2)⟩ := by
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ab, incl]
      congr 1
      apply Subtype.ext
      exact hσ q
    have h2 : (⟨x * ((e.symm q : ↥R) : G) * x⁻¹, hRH (hxR _ (e.symm q).2)⟩ : ↥H) =
        ⟨x, hxH⟩ * ⟨((e.symm q : ↥R) : G), hRH (e.symm q).2⟩ * ⟨x, hxH⟩⁻¹ := rfl
    have h3 : ψ q = ab ⟨((e.symm q : ↥R) : G), hRH (e.symm q).2⟩ := rfl
    rw [h1, h2, h3, map_mul, map_mul, map_inv, mul_comm (ab ⟨x, hxH⟩), mul_assoc,
      mul_inv_cancel, mul_one]
  obtain ⟨r, hr, hr1, hrt⟩ := hact
  have hrσ : σ (e ⟨r, hr⟩) * (e ⟨r, hr⟩)⁻¹ ≠ 1 ∧ σ (e ⟨r, hr⟩) * (e ⟨r, hr⟩)⁻¹ ≠ zQ := by
    have hk : ((e.symm (σ (e ⟨r, hr⟩) * (e ⟨r, hr⟩)⁻¹) : ↥R) : G) = x * r * x⁻¹ * r⁻¹ := by
      rw [map_mul, Subgroup.coe_mul, map_inv, hσ]
      simp
    constructor
    · intro h
      apply hr1
      rw [← hk, h]
      simp
    · intro h
      apply hrt
      rw [← hk, h, het]
  have hkill := q8_kill ψ σ hσmul hσz hσ3 hψσ hrσ.1 hrσ.2
  intro k hk
  have hk1 : ψ (e ⟨k, hk⟩) = 1 := hkill _
  have hk2 : ab ⟨k, hRH hk⟩ = 1 := by
    have : ψ (e ⟨k, hk⟩) = ab ⟨k, hRH hk⟩ := by
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, ab,
        incl]
      rfl
    rw [← this]
    exact hk1
  have hker : (⟨k, hRH hk⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of]
    exact hk2
  rw [← Subgroup.map_subtype_commutator H]
  exact ⟨_, hker, rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf
