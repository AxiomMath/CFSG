module

public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

section Model

variable {M : Type*} [Group M]

theorem hrep_of_cover (N : Subgroup M) {δ : M} {p : ℕ} (reps : List M)
    (hcover : ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hreps : ∀ r ∈ reps, ∃ g' ∈ N, orderOf (r * (g' * r * g'⁻¹)) = p) :
    ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ g' ∈ N, orderOf (u * (g' * u * g'⁻¹)) = p := by
  intro u hu hord
  obtain ⟨r, hr, c, hc, rfl⟩ := hcover u hu hord
  obtain ⟨g', hg', hp⟩ := hreps r hr
  refine ⟨c * g' * c⁻¹, N.mul_mem (N.mul_mem hc hg') (N.inv_mem hc), ?_⟩
  have : c * r * c⁻¹ * (c * g' * c⁻¹ * (c * r * c⁻¹) * (c * g' * c⁻¹)⁻¹) =
      c * (r * (g' * r * g'⁻¹)) * c⁻¹ := by group
  rw [this]
  have h2 := MulEquiv.orderOf_eq (MulAut.conj c) (r * (g' * r * g'⁻¹))
  simp only [MulAut.conj_apply] at h2
  rw [h2, hp]

theorem outer_dihedral_of_delta (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) {p : ℕ}
    (hrep : ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ g' ∈ N, orderOf (u * (g' * u * g'⁻¹)) = p) :
    ∀ α : MulAut N, α * α = 1 → α ∉ inner N → ∃ β : MulAut N, orderOf (α * (β * α * β⁻¹)) = p := by
  intro α hα2 hα
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ with hu
  have huN : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, ?_⟩
    ext h
    rw [MonoidHom.map_one, MulAut.one_apply, hαg]
    simp [h1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨g', hg', hp⟩ := hrep u huN hord
  refine ⟨MulAut.conj (⟨g', hg'⟩ : N), ?_⟩
  have hzN : u * (g' * u * g'⁻¹) ∈ N := by
    have : u * (g' * u * g'⁻¹) = g * (δ * (g' * g) * δ⁻¹) * (δ * δ) * g'⁻¹ := by
      simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem (N.mul_mem hg (hδ _ (N.mul_mem hg' hg))) hδ2) (N.inv_mem hg')
  have hconj : α * (MulAut.conj (⟨g', hg'⟩ : N) * α * (MulAut.conj (⟨g', hg'⟩ : N))⁻¹) =
      MulAut.conj (⟨u * (g' * u * g'⁻¹), hzN⟩ : N) := by
    ext h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    simp only [hαg, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hinj := conj_injective_of_center N hcenter
  rw [hconj, orderOf_injective (MulAut.conj : N →* MulAut N) hinj]
  have h3 := Subgroup.orderOf_coe (⟨u * (g' * u * g'⁻¹), hzN⟩ : N)
  rw [← h3]
  exact hp

end Model

end CFSG.QuasithinUnique.Setup.X1
