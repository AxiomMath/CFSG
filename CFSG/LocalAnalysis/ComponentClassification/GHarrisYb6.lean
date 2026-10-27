module

public import Certificates.Certificate22606
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb1

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.pow_eight : ∀ s : SE, s ^ 8 = 1 := by decide +kernel

theorem SCert.SE.t_predE_predF : predE (invRep 1) ∧ predF (invRep 1) := by decide

theorem SCert.SE.I1E : ∀ e₁ e₂ : SE, predE e₁ → predE e₂ →
    e₁ * invRep 1 = invRep 1 * e₁ → e₂ * invRep 1 = invRep 1 * e₂ → ¬ predF e₁ → ¬ predF e₂ →
      predF (e₁⁻¹ * e₂) :=
  Certificates.certificate22606.1

theorem SCert.SE.I2E : ∀ e₁ e₂ : SE, predE e₁ → predE e₂ →
    e₁ * invRep 1 ≠ invRep 1 * e₁ → e₂ * invRep 1 ≠ invRep 1 * e₂ →
      e₁⁻¹ * e₂ * invRep 1 = invRep 1 * (e₁⁻¹ * e₂) :=
  Certificates.certificate22606.2.1

theorem SCert.SE.I1F : ∀ e₁ e₂ : SE, predF e₁ → predF e₂ →
    e₁ * invRep 1 = invRep 1 * e₁ → e₂ * invRep 1 = invRep 1 * e₂ → ¬ predE e₁ → ¬ predE e₂ →
      predE (e₁⁻¹ * e₂) :=
  Certificates.certificate22606.2.2.1

theorem SCert.SE.I2F : ∀ e₁ e₂ : SE, predF e₁ → predF e₂ →
    e₁ * invRep 1 ≠ invRep 1 * e₁ → e₂ * invRep 1 ≠ invRep 1 * e₂ →
      e₁⁻¹ * e₂ * invRep 1 = invRep 1 * (e₁⁻¹ * e₂) :=
  Certificates.certificate22606.2.2.2

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem eq_of_conj_mul_fixed {p e u : Y} (h1 : p * e * p⁻¹ = e * u) (h2 : p * u * p⁻¹ = u)
    (hodd : Odd (orderOf p)) (hu : u ^ 8 = 1) : p * e * p⁻¹ = e := by
  have hpu : ∀ k : ℕ, p ^ k * u * (p ^ k)⁻¹ = u := by
    intro k
    induction k with
    | zero => simp
    | succ j ihj =>
      calc p ^ (j + 1) * u * (p ^ (j + 1))⁻¹ = p ^ j * (p * u * p⁻¹) * (p ^ j)⁻¹ := by
            rw [pow_succ]; group
        _ = u := by rw [h2, ihj]
  have hk : ∀ k : ℕ, p ^ k * e * (p ^ k)⁻¹ = e * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc p ^ (k + 1) * e * (p ^ (k + 1))⁻¹ = p ^ k * (p * e * p⁻¹) * (p ^ k)⁻¹ := by
            rw [pow_succ]; group
        _ = p ^ k * e * (p ^ k)⁻¹ * (p ^ k * u * (p ^ k)⁻¹) := by rw [h1]; group
        _ = e * u ^ k * u := by rw [ih, hpu]
        _ = e * u ^ (k + 1) := by rw [pow_succ, mul_assoc]
  have hm := hk (orderOf p)
  rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at hm
  have hum : u ^ orderOf p = 1 := by
    have := congrArg (fun y => e⁻¹ * y) hm
    simpa using this.symm
  have hu1 : u = 1 := by
    have hd : orderOf u ∣ Nat.gcd (orderOf p) 8 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hum) (orderOf_dvd_of_pow_eq_one hu)
    have hg : Nat.gcd (orderOf p) 8 = 1 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 ((Nat.coprime_two_right).mpr hodd)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  rw [h1, hu1, mul_one]

namespace GHSylow

variable (D : GHSylow Y)

omit [Finite Y] in
theorem pow_eight_of_mem_S {s : Y} (hs : s ∈ (D.S : Subgroup Y)) : s ^ 8 = 1 := by
  obtain ⟨s₀, rfl⟩ := D.exists_toG hs
  rw [← map_pow, SE.pow_eight, map_one]

omit [Finite Y] in
theorem centralizes_E_of_odd {p : Y} (hp : p ∈ D.Y1)
    (hodd : Odd (orderOf p))
    (hV : ∀ v ∈ D.E, v ∈ D.F → (p * v * p⁻¹)⁻¹ * v = 1 ∨ (p * v * p⁻¹)⁻¹ * v = D.l ∨
      (p * v * p⁻¹)⁻¹ * v = D.z ∨ (p * v * p⁻¹)⁻¹ * v = D.l * D.z)
    (hE : ∀ e ∈ D.E, p * e * p⁻¹ ∈ D.E) : ∀ e ∈ D.E, p * e * p⁻¹ = e := by
  have hpl : p * D.l = D.l * p := mem_centralizer_singleton_iff.mp hp
  have hpz : p * D.z = D.z * p := by
    rw [← D.l_mul_l, ← mul_assoc, hpl, mul_assoc, hpl, mul_assoc]
  have hV1 : ∀ v ∈ D.E, v ∈ D.F → p * v * p⁻¹ = v := by
    intro v hvE hvF
    obtain ⟨c, hc, hcv⟩ : ∃ c : Y, (c = 1 ∨ c = D.l ∨ c = D.z ∨ c = D.l * D.z) ∧
        (p * v * p⁻¹)⁻¹ * v = c := ⟨_, hV v hvE hvF, rfl⟩
    have h1 : p * v * p⁻¹ = v * c⁻¹ := by rw [← hcv]; group
    have hcS : c⁻¹ ∈ (D.S : Subgroup Y) := by
      refine inv_mem ?_
      rcases hc with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact D.toG_mem _
      · exact D.z_mem_S
      · exact mul_mem (D.toG_mem _) D.z_mem_S
    have hpc : p * c = c * p := by
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · exact hpl
      · exact hpz
      · rw [← mul_assoc, hpl, mul_assoc, hpz, mul_assoc]
    have h2 : p * c⁻¹ * p⁻¹ = c⁻¹ := by
      rw [((Commute.inv_right (show Commute p c from hpc))).eq, mul_inv_cancel_right]
    exact eq_of_conj_mul_fixed h1 h2 hodd (D.pow_eight_of_mem_S hcS)
  have ht : p * D.t * p⁻¹ = D.t :=
    hV1 _ ((D.toG_mem_E_iff).mpr SE.t_predE_predF.1) ((D.toG_mem_F_iff).mpr SE.t_predE_predF.2)
  have hEmem : ∀ e ∈ D.E, ∃ e₀ : SE, D.toG e₀ = e ∧ SE.predE e₀ := by
    rintro _ ⟨e₀, he₀, rfl⟩; exact ⟨e₀, rfl, he₀⟩
  have hct : ∀ e₀ : SE, D.toG e₀ * D.t = D.t * D.toG e₀ ↔ e₀ * SE.invRep 1 = SE.invRep 1 * e₀ :=
    fun e₀ => ⟨fun h => D.toG_injective (by rw [map_mul, map_mul]; exact h),
      fun h => by rw [← map_mul, ← map_mul, h]⟩
  have hconj_t : ∀ e : Y, (p * e * p⁻¹) * D.t = D.t * (p * e * p⁻¹) ↔ e * D.t = D.t * e := by
    intro e
    constructor
    · intro h
      calc e * D.t = p⁻¹ * ((p * e * p⁻¹) * (p * D.t * p⁻¹)) * p := by group
        _ = p⁻¹ * (D.t * (p * e * p⁻¹)) * p := by rw [ht, h]
        _ = p⁻¹ * ((p * D.t * p⁻¹) * (p * e * p⁻¹)) * p := by rw [ht]
        _ = D.t * e := by group
    · intro h
      calc p * e * p⁻¹ * D.t = p * e * p⁻¹ * (p * D.t * p⁻¹) := by rw [ht]
        _ = p * (e * D.t) * p⁻¹ := by group
        _ = p * (D.t * e) * p⁻¹ := by rw [h]
        _ = (p * D.t * p⁻¹) * (p * e * p⁻¹) := by group
        _ = D.t * (p * e * p⁻¹) := by rw [ht]
  have hV1' : ∀ v ∈ D.E, v ∈ D.F → p⁻¹ * v * p = v := by
    intro v hvE hvF
    have := hV1 v hvE hvF
    calc p⁻¹ * v * p = p⁻¹ * (p * v * p⁻¹) * p := by rw [this]
      _ = v := by group
  have hCE : ∀ e ∈ D.E, e * D.t = D.t * e → p * e * p⁻¹ = e := by
    intro e he het
    by_cases heF : e ∈ D.F
    · exact hV1 e he heF
    obtain ⟨e₀, rfl, he₀⟩ := hEmem e he
    obtain ⟨e₁, he₁e, he₁⟩ := hEmem _ (hE _ he)
    have he₁F : ¬ SE.predF e₁ := by
      intro h
      apply heF
      have hmem : p * D.toG e₀ * p⁻¹ ∈ D.F := by rw [← he₁e]; exact (D.toG_mem_F_iff).mpr h
      have := hV1' _ (hE _ he) hmem
      rw [show D.toG e₀ = p⁻¹ * (p * D.toG e₀ * p⁻¹) * p by group, this]
      exact hmem
    have hu := SE.I1E e₀ e₁ he₀ he₁ ((hct e₀).mp het) ((hct e₁).mp (by
      rw [he₁e]; exact (hconj_t _).mpr het)) (fun h => heF ((D.toG_mem_F_iff).mpr h)) he₁F
    have huE : SE.predE (e₀⁻¹ * e₁) := SE.Esub.mul_mem (SE.Esub.inv_mem he₀) he₁
    refine eq_of_conj_mul_fixed (u := D.toG (e₀⁻¹ * e₁)) ?_ ?_ hodd
      (D.pow_eight_of_mem_S (D.toG_mem _))
    · rw [map_mul, map_inv, he₁e]; group
    · exact hV1 _ ((D.toG_mem_E_iff).mpr huE) ((D.toG_mem_F_iff).mpr hu)
  intro e he
  by_cases het : e * D.t = D.t * e
  · exact hCE e he het
  obtain ⟨e₀, rfl, he₀⟩ := hEmem e he
  obtain ⟨e₁, he₁e, he₁⟩ := hEmem _ (hE _ he)
  have hu := SE.I2E e₀ e₁ he₀ he₁ (fun h => het ((hct e₀).mpr h)) (fun h => het (by
    have h' := (hct e₁).mpr h
    rw [he₁e] at h'
    exact (hconj_t _).mp h'))
  have huE : SE.predE (e₀⁻¹ * e₁) := SE.Esub.mul_mem (SE.Esub.inv_mem he₀) he₁
  refine eq_of_conj_mul_fixed (u := D.toG (e₀⁻¹ * e₁)) ?_ ?_ hodd
    (D.pow_eight_of_mem_S (D.toG_mem _))
  · rw [map_mul, map_inv, he₁e]; group
  · exact hCE _ ((D.toG_mem_E_iff).mpr huE) ((hct _).mpr hu)

omit [Finite Y] in
theorem centralizes_F_of_odd {p : Y} (hp : p ∈ D.Y1)
    (hodd : Odd (orderOf p))
    (hV : ∀ v ∈ D.E, v ∈ D.F → (p * v * p⁻¹)⁻¹ * v = 1 ∨ (p * v * p⁻¹)⁻¹ * v = D.l ∨
      (p * v * p⁻¹)⁻¹ * v = D.z ∨ (p * v * p⁻¹)⁻¹ * v = D.l * D.z)
    (hE : ∀ e ∈ D.F, p * e * p⁻¹ ∈ D.F) : ∀ e ∈ D.F, p * e * p⁻¹ = e := by
  have hpl : p * D.l = D.l * p := mem_centralizer_singleton_iff.mp hp
  have hpz : p * D.z = D.z * p := by
    rw [← D.l_mul_l, ← mul_assoc, hpl, mul_assoc, hpl, mul_assoc]
  have hV1 : ∀ v ∈ D.E, v ∈ D.F → p * v * p⁻¹ = v := by
    intro v hvE hvF
    obtain ⟨c, hc, hcv⟩ : ∃ c : Y, (c = 1 ∨ c = D.l ∨ c = D.z ∨ c = D.l * D.z) ∧
        (p * v * p⁻¹)⁻¹ * v = c := ⟨_, hV v hvE hvF, rfl⟩
    have h1 : p * v * p⁻¹ = v * c⁻¹ := by rw [← hcv]; group
    have hcS : c⁻¹ ∈ (D.S : Subgroup Y) := by
      refine inv_mem ?_
      rcases hc with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact D.toG_mem _
      · exact D.z_mem_S
      · exact mul_mem (D.toG_mem _) D.z_mem_S
    have hpc : p * c = c * p := by
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · exact hpl
      · exact hpz
      · rw [← mul_assoc, hpl, mul_assoc, hpz, mul_assoc]
    have h2 : p * c⁻¹ * p⁻¹ = c⁻¹ := by
      rw [((Commute.inv_right (show Commute p c from hpc))).eq, mul_inv_cancel_right]
    exact eq_of_conj_mul_fixed h1 h2 hodd (D.pow_eight_of_mem_S hcS)
  have ht : p * D.t * p⁻¹ = D.t :=
    hV1 _ ((D.toG_mem_E_iff).mpr SE.t_predE_predF.1) ((D.toG_mem_F_iff).mpr SE.t_predE_predF.2)
  have hEmem : ∀ e ∈ D.F, ∃ e₀ : SE, D.toG e₀ = e ∧ SE.predF e₀ := by
    rintro _ ⟨e₀, he₀, rfl⟩; exact ⟨e₀, rfl, he₀⟩
  have hct : ∀ e₀ : SE, D.toG e₀ * D.t = D.t * D.toG e₀ ↔ e₀ * SE.invRep 1 = SE.invRep 1 * e₀ :=
    fun e₀ => ⟨fun h => D.toG_injective (by rw [map_mul, map_mul]; exact h),
      fun h => by rw [← map_mul, ← map_mul, h]⟩
  have hconj_t : ∀ e : Y, (p * e * p⁻¹) * D.t = D.t * (p * e * p⁻¹) ↔ e * D.t = D.t * e := by
    intro e
    constructor
    · intro h
      calc e * D.t = p⁻¹ * ((p * e * p⁻¹) * (p * D.t * p⁻¹)) * p := by group
        _ = p⁻¹ * (D.t * (p * e * p⁻¹)) * p := by rw [ht, h]
        _ = p⁻¹ * ((p * D.t * p⁻¹) * (p * e * p⁻¹)) * p := by rw [ht]
        _ = D.t * e := by group
    · intro h
      calc p * e * p⁻¹ * D.t = p * e * p⁻¹ * (p * D.t * p⁻¹) := by rw [ht]
        _ = p * (e * D.t) * p⁻¹ := by group
        _ = p * (D.t * e) * p⁻¹ := by rw [h]
        _ = (p * D.t * p⁻¹) * (p * e * p⁻¹) := by group
        _ = D.t * (p * e * p⁻¹) := by rw [ht]
  have hV1' : ∀ v ∈ D.E, v ∈ D.F → p⁻¹ * v * p = v := by
    intro v hvE hvF
    have := hV1 v hvE hvF
    calc p⁻¹ * v * p = p⁻¹ * (p * v * p⁻¹) * p := by rw [this]
      _ = v := by group
  have hCE : ∀ e ∈ D.F, e * D.t = D.t * e → p * e * p⁻¹ = e := by
    intro e he het
    by_cases heF : e ∈ D.E
    · exact hV1 e heF he
    obtain ⟨e₀, rfl, he₀⟩ := hEmem e he
    obtain ⟨e₁, he₁e, he₁⟩ := hEmem _ (hE _ he)
    have he₁F : ¬ SE.predE e₁ := by
      intro h
      apply heF
      have hmem : p * D.toG e₀ * p⁻¹ ∈ D.E := by rw [← he₁e]; exact (D.toG_mem_E_iff).mpr h
      have := hV1' _ hmem (hE _ he)
      rw [show D.toG e₀ = p⁻¹ * (p * D.toG e₀ * p⁻¹) * p by group, this]
      exact hmem
    have hu := SE.I1F e₀ e₁ he₀ he₁ ((hct e₀).mp het) ((hct e₁).mp (by
      rw [he₁e]; exact (hconj_t _).mpr het)) (fun h => heF ((D.toG_mem_E_iff).mpr h)) he₁F
    have huE : SE.predF (e₀⁻¹ * e₁) := SE.Fsub.mul_mem (SE.Fsub.inv_mem he₀) he₁
    refine eq_of_conj_mul_fixed (u := D.toG (e₀⁻¹ * e₁)) ?_ ?_ hodd
      (D.pow_eight_of_mem_S (D.toG_mem _))
    · rw [map_mul, map_inv, he₁e]; group
    · exact hV1 _ ((D.toG_mem_E_iff).mpr hu) ((D.toG_mem_F_iff).mpr huE)
  intro e he
  by_cases het : e * D.t = D.t * e
  · exact hCE e he het
  obtain ⟨e₀, rfl, he₀⟩ := hEmem e he
  obtain ⟨e₁, he₁e, he₁⟩ := hEmem _ (hE _ he)
  have hu := SE.I2F e₀ e₁ he₀ he₁ (fun h => het ((hct e₀).mpr h)) (fun h => het (by
    have h' := (hct e₁).mpr h
    rw [he₁e] at h'
    exact (hconj_t _).mp h'))
  have huE : SE.predF (e₀⁻¹ * e₁) := SE.Fsub.mul_mem (SE.Fsub.inv_mem he₀) he₁
  refine eq_of_conj_mul_fixed (u := D.toG (e₀⁻¹ * e₁)) ?_ ?_ hodd
    (D.pow_eight_of_mem_S (D.toG_mem _))
  · rw [map_mul, map_inv, he₁e]; group
  · exact hCE _ ((D.toG_mem_F_iff).mpr huE) ((hct _).mpr hu)

end GHSylow

end CFSG.ComponentClassification.GHarris
