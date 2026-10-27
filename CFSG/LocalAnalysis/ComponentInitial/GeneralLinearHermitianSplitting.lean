module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix MatrixExtension

theorem four_element_general_linear_hermitian_extension_splitting {K : Type*} [Field K]
    (hK : Nat.card K = 4) {r : ℕ} (hr : 2 ≤ r)
    {M : Type*} [AddCommGroup M] (_hfin : Finite M) (_hM : ∀ m : M, ∃ n : ℕ, 2 ^ n • m = 0)
    [DistribMulAction (GL (Fin r) K) M] (π : M →+ Matrix (Fin r) (Fin r) K)
    (hπV : ∀ m, hconj (π m) = π m)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B)
    (hπact : ∀ (g : GL (Fin r) K) (m : M), π (g • m) = (g : Matrix (Fin r) (Fin r) K) *
      π m * hconj (g : Matrix (Fin r) (Fin r) K))
    (hC2 : ∀ c ∈ π.ker, 2 • c = 0) (hC : ∀ g : GL (Fin r) K, ∀ c ∈ π.ker, g • c = c) :
    (∀ m : M, 2 • m = 0) ∧ ∃ M₀ : AddSubgroup M, (∀ g : GL (Fin r) K, ∀ x ∈ M₀, g • x ∈ M₀) ∧
      π.ker ⊓ M₀ = ⊥ ∧ π.ker ⊔ M₀ = ⊤ ∧ (∀ x ∈ M₀, π x = 0 → x = 0) ∧
      ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ x ∈ M₀, π x = B := by
  classical
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  have hdet : ∀ g : (⊤ : Subgroup (GL (Fin r) K)), ∃ (t : (⊤ : Subgroup (GL (Fin r) K)))
      (e : Fin r → Kˣ), (t : GL (Fin r) K) = hTorusGL e ∧
        GeneralLinearGroup.det (t : GL (Fin r) K) = GeneralLinearGroup.det (g : GL (Fin r) K) := by
    intro g
    let i₀ : Fin r := ⟨0, by omega⟩
    refine ⟨⟨hTorusGL (Pi.mulSingle i₀ (GeneralLinearGroup.det (g : GL (Fin r) K))),
      Subgroup.mem_top _⟩, _, rfl, Units.ext ?_⟩
    rw [GeneralLinearGroup.val_det_apply, hTorusGL_det, ← Units.coe_prod,
      Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
  have hsep : ∀ a b i j : Fin r, a ≠ b → i ≠ j → ¬(i = a ∧ j = b) → ¬(i = b ∧ j = a) →
      ∃ (h : (⊤ : Subgroup (GL (Fin r) K))) (e : Fin r → Kˣ),
        (h : GL (Fin r) K) = hTorusGL e ∧ e a = e b ∧ e i ≠ e j := by
    intro a b i j _ hij h₁ h₂
    obtain ⟨e, he₁, he₂⟩ := exists_sep_units hω0 hω1 hij h₁ h₂
    exact ⟨⟨hTorusGL e, Subgroup.mem_top _⟩, e, rfl, he₁, he₂⟩
  obtain ⟨h2, M₀, hinv, hrest⟩ := herm_splitting_of_sep hK hr (Γ := ⊤)
    (fun g _ => Subgroup.mem_top g) hdet hsep π hπV hsurj (fun g m => hπact g m) hC2
    (fun g c hc => hC g c hc)
  exact ⟨h2, M₀, fun g x hx => hinv ⟨g, Subgroup.mem_top g⟩ x hx, hrest⟩

end CFSG.LocalAnalysis.ComponentInitial
