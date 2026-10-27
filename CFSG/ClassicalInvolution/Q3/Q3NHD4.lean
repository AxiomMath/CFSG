module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3W.EX CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Spin

theorem d4_cross_pair_mul_central (hF : D4Facts3)
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR₁ : R₁ ∈ fundD4 𝔽₃)
    (hR₂ : R₂ ∈ fundD4 𝔽₃) {c₁ c₂ : spinGroup (quadPlus 4 𝔽₃)} (hc₁ : c₁ ∈ R₁)
    (hc₂ : c₂ ∈ R₂) (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂)
    (hx : ∀ r ∈ R₁, c₂ * r = r * c₂) (h₁ : c₁ ≠ 1) (h₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hker := ker_spinAction_le_center (quadPlus 4 𝔽₃)
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hmemF : ∀ (x : spinGroup (quadPlus 4 𝔽₃)) (k : Fin 4),
      rankOneRoot (plusDatum 4 𝔽₃ hn3) x (Pi.single k 1) ∈ fundD4 𝔽₃ := fun x k =>
    ⟨x, Pi.single k 1, Or.inl (hF.long k), rfl⟩
  have hθ₁ : spinAction (quadPlus 4 𝔽₃) c₁ ≠ 1 := fun h => h₁ (hF.inj hR₁ hc₁ h)
  have hθ₂ : spinAction (quadPlus 4 𝔽₃) c₂ ≠ 1 := fun h => h₂ (hF.inj hR₂ hc₂ h)
  obtain ⟨fr₁, hfr₁⟩ := hF.exists_frame hR₁
  obtain ⟨fr₂, hfr₂⟩ := hF.exists_frame hR₂
  have hi₁ : spinAction (quadPlus 4 𝔽₃) c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction (quadPlus 4 𝔽₃) c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  by_cases hEq : fr₂.La (-1) = fr₁.La (-1)
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, hi₁, hi₂, hEq]
    exact fr₁.La_neg_one_mul_self
  · have hc' : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
      rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hx c₁ hc₁]
    have hcent : ∀ A : SL(2, 𝔽₃), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
      intro A
      obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction (quadPlus 4 𝔽₃)) := hfr₁ ▸ ⟨A, rfl⟩
      rw [← hi₂, ← hrA, ← map_mul, ← map_mul, hx r hr]
    have horth := (Frame.orth_or_eq h2 hc' hcent).resolve_right hEq
    have hneg := La_neg_one_mul_of_orth h2 hdim horth
    have hθ12 : spinAction (quadPlus 4 𝔽₃) (c₁ * c₂) = LinearEquiv.neg 𝔽₃ := by
      rw [map_mul, hi₁, hi₂, hneg]
    have hcent' : ∀ R ∈ fundD4 𝔽₃, ∀ y ∈ R, y * (c₁ * c₂) = (c₁ * c₂) * y := by
      intro R hR y hy
      exact ModelFacts.commute_of_map_commute_of_gen3 (spinAction (quadPlus 4 𝔽₃)) hker
        hF.central.k3 (hF.central.gen R hR) (b := c₁ * c₂) (by
          intro a _
          rw [hθ12]
          ext v
          simp) y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (⨆ k : Fin 4, rankOneRoot (plusDatum 4 𝔽₃ hn3) 1 (Pi.single k 1)) := by
      rw [hF.gen 1]
      trivial
    have : (⨆ k : Fin 4, rankOneRoot (plusDatum 4 𝔽₃ hn3) 1 (Pi.single k 1)) ≤
        Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 𝔽₃))) :=
      iSup_le fun k y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcent' _ (hmemF 1 k) y hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)

theorem d4_center_three (x : spinGroup (quadPlus 4 𝔽₃))
    (hx : x ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃))) (h3 : x ^ 3 = 1) : x = 1 := by
  have hcard : Nat.card 𝔽₃ = 2 ^ 1 + 1 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have h4 : x ^ (2 ^ (1 + 1)) = 1 := centerExp_spinPlus (by norm_num) hcard x hx
  have : x = x ^ 4 * (x ^ 3)⁻¹ := by group
  rw [this]
  norm_num at h4
  rw [h4, h3]
  simp

end Spin

section Quotient

theorem d4_cross_pair_central_quotient {X : Type} [Group X]
    (ψ : spinGroup (quadPlus 4 𝔽₃) →* X) (hker : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR₁ : R₁ ∈ fundD4 𝔽₃)
    (hR₂ : R₂ ∈ fundD4 𝔽₃) {ζ₁ ζ₂ : X} (h₁ : ζ₁ ∈ R₁.map ψ) (h₂ : ζ₂ ∈ R₂.map ψ)
    (n₁ : ζ₁ ≠ 1) (n₂ : ζ₂ ≠ 1) (z₁ : ∀ y ∈ R₁.map ψ, ζ₁ * y = y * ζ₁)
    (z₂ : ∀ y ∈ R₂.map ψ, ζ₂ * y = y * ζ₂) (x : ∀ y ∈ R₁.map ψ, ζ₂ * y = y * ζ₂) :
    ∀ y ∈ ψ.range, ζ₁ * ζ₂ * y = y * (ζ₁ * ζ₂) := by
  have hF : D4Facts3 := D4Facts3.of_gf3
  have hk3 : ∀ w ∈ ψ.ker, w ^ 3 = 1 → w = 1 := fun w hw h3 => d4_center_three w (hker hw) h3
  obtain ⟨r₁, hr₁, rfl⟩ := h₁
  obtain ⟨r₂, hr₂, rfl⟩ := h₂
  have c₁ : ∀ a ∈ R₁, r₁ * a = a * r₁ := fun a ha =>
    (ModelFacts.commute_of_map_commute_of_gen3 ψ hker hk3 (hF.central.gen R₁ hR₁) (b := r₁)
      (fun a' ha' => (z₁ (ψ a') ⟨a', ha', rfl⟩).symm) a ha).symm
  have c₂ : ∀ a ∈ R₂, r₂ * a = a * r₂ := fun a ha =>
    (ModelFacts.commute_of_map_commute_of_gen3 ψ hker hk3 (hF.central.gen R₂ hR₂) (b := r₂)
      (fun a' ha' => (z₂ (ψ a') ⟨a', ha', rfl⟩).symm) a ha).symm
  have cx : ∀ a ∈ R₁, r₂ * a = a * r₂ := fun a ha =>
    (ModelFacts.commute_of_map_commute_of_gen3 ψ hker hk3 (hF.central.gen R₁ hR₁) (b := r₂)
      (fun a' ha' => (x (ψ a') ⟨a', ha', rfl⟩).symm) a ha).symm
  have h1 : r₁ ≠ 1 := fun h => n₁ (by rw [h, map_one])
  have h2 : r₂ ≠ 1 := fun h => n₂ (by rw [h, map_one])
  have hc := d4_cross_pair_mul_central hF hR₁ hR₂ hr₁ hr₂ c₁ c₂ cx h1 h2
  rintro _ ⟨g, rfl⟩
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact (Subgroup.mem_center_iff.mp hc g).symm

theorem d4_cross_pair_central_model {X : Type} [Group X]
    (ψ : (CompData.model .POmegaPlus 4).G →* X) (hker : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup (CompData.model .POmegaPlus 4).G}
    (hR₁ : R₁ ∈ (CompData.model .POmegaPlus 4).fund)
    (hR₂ : R₂ ∈ (CompData.model .POmegaPlus 4).fund) {ζ₁ ζ₂ : X} (h₁ : ζ₁ ∈ R₁.map ψ)
    (h₂ : ζ₂ ∈ R₂.map ψ) (n₁ : ζ₁ ≠ 1) (n₂ : ζ₂ ≠ 1) (z₁ : ∀ y ∈ R₁.map ψ, ζ₁ * y = y * ζ₁)
    (z₂ : ∀ y ∈ R₂.map ψ, ζ₂ * y = y * ζ₂) (x : ∀ y ∈ R₁.map ψ, ζ₂ * y = y * ζ₂) :
    ∀ y ∈ ψ.range, ζ₁ * ζ₂ * y = y * (ζ₁ * ζ₂) :=
  d4_cross_pair_central_quotient ψ hker hR₁ hR₂ h₁ h₂ n₁ n₂ z₁ z₂ x

theorem d4_cross_pair_central_of_comp {X : Type} [Group X] {c : CompData}
    (hc : c = CompData.model .POmegaPlus 4) (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup c.G} (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund) {ζ₁ ζ₂ : X}
    (h₁ : ζ₁ ∈ R₁.map ψ) (h₂ : ζ₂ ∈ R₂.map ψ) (n₁ : ζ₁ ≠ 1) (n₂ : ζ₂ ≠ 1)
    (z₁ : ∀ y ∈ R₁.map ψ, ζ₁ * y = y * ζ₁) (z₂ : ∀ y ∈ R₂.map ψ, ζ₂ * y = y * ζ₂)
    (x : ∀ y ∈ R₁.map ψ, ζ₂ * y = y * ζ₂) :
    ∀ y ∈ ψ.range, ζ₁ * ζ₂ * y = y * (ζ₁ * ζ₂) := by
  subst hc
  exact d4_cross_pair_central_model ψ hker hR₁ hR₂ h₁ h₂ n₁ n₂ z₁ z₂ x

end Quotient

end CFSG.ClassicalInvolution.Q3.Q3NH
