module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreChar

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

@[expose] def Fusion.inv (φ : Δ.Fusion) : Δ.Fusion where
  T := φ.T
  le := φ.le
  x := φ.x⁻¹
  mem := inv_mem φ.mem
  not_mem := fun h => φ.not_mem (by simpa using inv_mem h)
  conj_mem := fun s hs => by simpa using φ.conj_inv_mem hs
  sq_mem := by rw [inv_pow]; exact inv_mem φ.sq_mem

@[simp] theorem Fusion.inv_x (φ : Δ.Fusion) : φ.inv.x = φ.x⁻¹ := rfl

variable {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

theorem TwoB_commute (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {d d' : X}
    (hd : d ∈ Δ.D) (hd' : d' ∈ Δ.D) : d * (φ.x * d' * φ.x⁻¹) = (φ.x * d' * φ.x⁻¹) * d := by
  have hd'S : φ.x * d' * φ.x⁻¹ ∈ Δ.S := φ.conj_mem d' (Δ.D_le hd')
  set c := d * (φ.x * d' * φ.x⁻¹) * d⁻¹ * (φ.x * d' * φ.x⁻¹)⁻¹
  have hcD : c ∈ Δ.D := by
    have : c = d * ((φ.x * d' * φ.x⁻¹) * d⁻¹ * (φ.x * d' * φ.x⁻¹)⁻¹) := by simp only [c]; group
    rw [this]
    exact mul_mem hd (Δ.conj_mem_D _ hd'S _ (inv_mem hd))
  have hcD' : φ.x⁻¹ * c * φ.x ∈ Δ.D := by
    have : φ.x⁻¹ * c * φ.x = (φ.x⁻¹ * d * φ.x) * d' * (φ.x⁻¹ * d * φ.x)⁻¹ * d'⁻¹ := by
      simp only [c]; group
    rw [this]
    exact mul_mem (Δ.conj_mem_D _ (φ.conj_inv_mem (Δ.D_le hd)) _ hd') (inv_mem hd')
  have h := hD1 c hcD hcD'
  calc d * (φ.x * d' * φ.x⁻¹) = c * ((φ.x * d' * φ.x⁻¹) * d) := by simp only [c]; group
    _ = (φ.x * d' * φ.x⁻¹) * d := by rw [h, one_mul]

theorem TwoB_inv (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) :
    ∀ u ∈ Δ.D, φ.inv.x⁻¹ * u * φ.inv.x ∈ Δ.D → u = 1 := by
  intro u hu hu'
  simp only [Fusion.inv_x, inv_inv] at hu'
  have h := hD1 _ hu' (by simpa [mul_assoc] using hu)
  calc u = φ.x⁻¹ * (φ.x * u * φ.x⁻¹) * φ.x := by group
    _ = 1 := by rw [h]; group

include h2 in
theorem TwoB_conj_dz (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) :
    φ.x * Δ.dz * φ.x⁻¹ = Δ.t := by
  have h8 := h2.2.2.2.2.1
  have hρS : φ.x * Δ.da * φ.x⁻¹ ∈ Δ.S := φ.conj_mem _ (Δ.D_le Δ.da_mem)
  have hρD : ∀ d ∈ Δ.D, φ.x * Δ.da * φ.x⁻¹ * d = d * (φ.x * Δ.da * φ.x⁻¹) := fun d hd =>
    (TwoB_commute φ hD1 hd Δ.da_mem).symm
  have hsq := Δ.sq_mem_Q_of_caseTwo h2 hρS hρD
  have he : (φ.x * Δ.da * φ.x⁻¹) ^ 2 = φ.x * Δ.dz * φ.x⁻¹ := by
    rw [← Δ.da_sq h8, pow_two, pow_two]
    group
  rw [he] at hsq
  refine Δ.eq_t_of_mem_Q hsq ?_ ?_
  · rw [pow_two, show φ.x * Δ.dz * φ.x⁻¹ * (φ.x * Δ.dz * φ.x⁻¹) = φ.x * (Δ.dz * Δ.dz) * φ.x⁻¹ by
      group, ← pow_two, Δ.dz_sq]
    group
  · intro h
    apply Δ.dz_ne_one
    calc Δ.dz = φ.x⁻¹ * (φ.x * Δ.dz * φ.x⁻¹) * φ.x := by group
      _ = 1 := by rw [h]; group

include h2 in
theorem TwoB_conj_t (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) :
    φ.x * Δ.t * φ.x⁻¹ = Δ.dz := by
  have h := TwoB_conj_dz h2 φ.inv (TwoB_inv φ hD1)
  simp only [Fusion.inv_x, inv_inv] at h
  rw [← h]
  group

omit [Finite X] in
theorem TwoB_unique (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {a a' b b' : X}
    (ha : a ∈ Δ.D) (ha' : a' ∈ Δ.D) (hb : b ∈ Δ.D) (hb' : b' ∈ Δ.D)
    (h : a * (φ.x * b * φ.x⁻¹) = a' * (φ.x * b' * φ.x⁻¹)) : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = φ.x * (b' * b⁻¹) * φ.x⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * (φ.x * b * φ.x⁻¹)) * (φ.x * b * φ.x⁻¹)⁻¹ := by group
      _ = a'⁻¹ * (a' * (φ.x * b' * φ.x⁻¹)) * (φ.x * b * φ.x⁻¹)⁻¹ := by rw [h]
      _ = φ.x * (b' * b⁻¹) * φ.x⁻¹ := by group
  have hmem : φ.x⁻¹ * (a'⁻¹ * a) * φ.x ∈ Δ.D := by
    rw [h1]
    simpa [mul_assoc] using mul_mem hb' (inv_mem hb)
  have h2' := hD1 _ (mul_mem (inv_mem ha') ha) hmem
  refine ⟨(inv_mul_eq_one.mp h2').symm, ?_⟩
  rw [h2'] at h1
  have : b' * b⁻¹ = 1 := by
    calc b' * b⁻¹ = φ.x⁻¹ * (φ.x * (b' * b⁻¹) * φ.x⁻¹) * φ.x := by group
      _ = 1 := by rw [← h1]; group
  exact (mul_inv_eq_one.mp this).symm

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
