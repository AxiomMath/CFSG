module

public import CFSG.CGT.Foote81L6.Normalizer.DihedralEight
public import CFSG.Quasithin.Background.B1Transvection

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

structure TvHyp {V X : Type*} [CommGroup V] [Group X] (ρ : X →* MulAut V) (D : Sylow 2 X)
    (d₀ d₁ : X) : Prop where
  injective : Function.Injective ρ
  sq_eq_one : ∀ v : V, v * v = 1
  card_eq : Nat.card V = 2 ^ 6
  dihedral : Nonempty ((D : Subgroup X) ≃* DihedralGroup 4)
  mem₀ : d₀ ∈ (D : Subgroup X)
  mem₁ : d₁ ∈ (D : Subgroup X)
  ne : d₀ ≠ d₁
  transvection : IsTransvection (ρ d₀)
  fusion : ∀ y ∈ (D : Subgroup X), IsConj d₀ y ↔ y = d₀ ∨ y = d₁

structure IsSymDirect {X : Type*} [Group X] (d₀ d₁ : X) {n : ℕ} [NeZero n]
    (φ : X →* Equiv.Perm (Fin n)) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = pPrimeCore 2 X
  map₀ : φ d₀ = Equiv.swap 0 1
  map₁ : φ d₁ = Equiv.swap 2 3
  mem₁ : d₁ ∈ Subgroup.normalClosure ({d₀} : Set X)
  inf_eq : Subgroup.normalClosure ({d₀} : Set X) ⊓ pPrimeCore 2 X = ⊥
  sup_eq : Subgroup.normalClosure ({d₀} : Set X) ⊔ pPrimeCore 2 X = ⊤
  commute : ∀ a ∈ Subgroup.normalClosure ({d₀} : Set X), ∀ o ∈ pPrimeCore 2 X, a * o = o * a

namespace TvHyp

variable {V X : Type*} [CommGroup V] [Group X] {ρ : X →* MulAut V} {D : Sylow 2 X} {d₀ d₁ : X}

theorem sq₀ (h : TvHyp ρ D d₀ d₁) : d₀ * d₀ = 1 := by
  obtain ⟨ht1, w, htw⟩ := h.transvection
  have hV : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact h.sq_eq_one v
  apply h.injective
  rw [map_mul, B1.tv_sq hV htw ht1, map_one]

theorem ne_one₀ (h : TvHyp ρ D d₀ d₁) : d₀ ≠ 1 := fun h1 =>
  h.transvection.1 (by rw [h1, map_one])

theorem isConj₁ (h : TvHyp ρ D d₀ d₁) : IsConj d₀ d₁ :=
  (h.fusion d₁ h.mem₁).mpr (Or.inr rfl)

theorem sq₁ (h : TvHyp ρ D d₀ d₁) : d₁ * d₁ = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h.isConj₁
  calc c * d₀ * c⁻¹ * (c * d₀ * c⁻¹) = c * (d₀ * d₀) * c⁻¹ := by group
    _ = 1 := by rw [h.sq₀, mul_one, mul_inv_cancel]

theorem ne_one₁ (h : TvHyp ρ D d₀ d₁) : d₁ ≠ 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h.isConj₁
  intro h1
  apply h.ne_one₀
  calc d₀ = c⁻¹ * (c * d₀ * c⁻¹) * c := by group
    _ = 1 := by rw [h1]; group

theorem conj_eq (h : TvHyp ρ D d₀ d₁) {g : X} (hg : g * d₀ * g⁻¹ ∈ (D : Subgroup X)) :
    g * d₀ * g⁻¹ = d₀ ∨ g * d₀ * g⁻¹ = d₁ :=
  (h.fusion _ hg).mp (isConj_iff.mpr ⟨g, rfl⟩)

theorem conj_eq₁ (h : TvHyp ρ D d₀ d₁) {g : X} (hg : g * d₁ * g⁻¹ ∈ (D : Subgroup X)) :
    g * d₁ * g⁻¹ = d₀ ∨ g * d₁ * g⁻¹ = d₁ :=
  (h.fusion _ hg).mp (h.isConj₁.trans (isConj_iff.mpr ⟨g, rfl⟩))

theorem dihedral_facts (h : TvHyp ρ D d₀ d₁) :
    d₀ * d₁ = d₁ * d₀ ∧ (∀ c ∈ (D : Subgroup X), c * (d₀ * d₁) = d₀ * d₁ * c) ∧
      d₀ * d₁ ≠ 1 ∧ d₀ * d₁ ≠ d₀ ∧ d₀ * d₁ ≠ d₁ ∧
      (∃ c ∈ (D : Subgroup X), c * d₀ * c⁻¹ = d₁) ∧
      (∀ c ∈ (D : Subgroup X), c * d₀ = d₀ * c → c * d₁ = d₁ * c →
        c = 1 ∨ c = d₀ ∨ c = d₁ ∨ c = d₀ * d₁) ∧
      ∃ Q : Subgroup X, Q ≤ D ∧ Q.relIndex D = 2 ∧ d₀ ∉ Q ∧ d₁ ∉ Q := by
  obtain ⟨ψ⟩ := h.dihedral
  exact dihedralEight_fusion ψ h.mem₀ h.mem₁ h.ne h.sq₀ h.ne_one₀ h.sq₁ h.ne_one₁
    (fun c hc => h.conj_eq ((D : Subgroup X).mul_mem
      ((D : Subgroup X).mul_mem hc h.mem₀) ((D : Subgroup X).inv_mem hc)))
    (fun c hc => h.conj_eq₁ ((D : Subgroup X).mul_mem
      ((D : Subgroup X).mul_mem hc h.mem₁) ((D : Subgroup X).inv_mem hc)))

end TvHyp

end CFSG.CGT.Foote81L6.Normalizer
