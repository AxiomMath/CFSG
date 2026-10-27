module

public import CFSG.ClassicalInvolution.Q3.Q3TLKD4Sq
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4Fix
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition
public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


theorem sqTrichotomy3_plus4_aux :
    SqTrichotomyOn .POmegaPlus ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have cq := Q3TY.centralQuot3_plus (m := 4) le_rfl
  have hZ3 := center_plus4_no_three
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  intro X _ θ hθs hθk R R' R₂ hR hR' hR₂ hne x x' x₂ hx hx2 hx1 hx' hx'2 hx'1 hxx' hx₂ hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  have hcK : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q₄) :=
    hθk (by rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', mul_inv_cancel])
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have h1 := Subgroup.mem_center_iff.mp hcK x
    have h2 : x * (x * x'⁻¹) = x'⁻¹ := by rw [← mul_assoc, hx2, one_mul]
    have h3 : x * x'⁻¹ * x = x'⁻¹ := by rw [← h1, h2]
    calc (x * x'⁻¹) * (x * x'⁻¹) = (x * x'⁻¹ * x) * x'⁻¹ := by group
      _ = x'⁻¹ * x'⁻¹ := by rw [h3]
      _ = 1 := by rw [hx'inv, hx'2]
  obtain ⟨σ, hσ, hθ⟩ := ModelFacts.TG3.exists_aut_ordinary3 hadm hcK hc2
  have hord : spinAction Q₄ (σ x) = spinAction Q₄ (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  set θ' : spinGroup Q₄ →* X := θ.comp σ.symm.toMonoidHom with hθ'
  have hθ's : Function.Surjective θ' := hθs.comp σ.symm.surjective
  have hθ'k : θ'.ker ≤ Subgroup.center (spinGroup Q₄) := by
    intro s hs
    have h1 : σ.symm s ∈ θ.ker := by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact hs
    have h2 := hθk h1
    have : s = σ (σ.symm s) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    have := h2 (σ.symm y)
    simpa using congrArg σ this
  have hθ'σ : ∀ s, θ' (σ s) = θ s := fun s => by simp [hθ']
  have hθ'σ' : ∀ s, θ' (σ.toMonoidHom s) = θ s := fun s => by simp [hθ']
  have hlift := liftSimFr3_plus4 θ' hθ'k
  have hRp := cq.pow3 _ (hσ R hR)
  have hR'p := cq.pow3 _ (hσ R' hR')
  have hR₂p := cq.pow3 _ (hσ R₂ hR₂)
  have hRc := cq.map_mem _ (hσ R hR)
  have hR'c := cq.map_mem _ (hσ R' hR')
  have hR₂c := cq.map_mem _ (hσ R₂ hR₂)
  have hRi := cq.inj _ (hσ R hR)
  have hR'i := cq.inj _ (hσ R' hR')
  have hR₂i := cq.inj _ (hσ R₂ hR₂)
  have hne' : R.map σ.toMonoidHom ≠ R'.map σ.toMonoidHom := by
    intro h
    apply hne
    have := congrArg (fun S : Subgroup (spinGroup Q₄) => S.map σ.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using this
  have hres := spin_sq_trichotomy_ord3 (θ := θ') (X := X) odd_gf3 card_gf3
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) hZ3 hdim hθ's hθ'k hlift hRp hR'p hRc hR'c hRi hR'i hne'
    (Subgroup.mem_map_of_mem _ hx) (by rw [← map_mul, hx2, map_one]) (fun h => hx1
      (σ.injective (by simpa using h)))
    (Subgroup.mem_map_of_mem _ hx') (by rw [← map_mul, hx'2, map_one]) (fun h => hx'1
      (σ.injective (by simpa using h))) hord hR₂p hR₂c hR₂i
    (Subgroup.mem_map_of_mem _ hx₂) (by rw [← map_mul, hx₂2, map_one]) (fun h => hx₂1
      (σ.injective (by simpa using h))) α hα4
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR r hr)
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR' r hr)
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR₂ r hr)
  rcases hres with h | h | ⟨g', hg1, r₁', hr₁', hg2⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    rw [h, hθ'σ']
  · refine Or.inr (Or.inr ⟨σ.symm g', ?_, ?_⟩)
    · intro r hr
      have e1 : ∀ r₀ : spinGroup Q₄,
          θ' (g' * σ r₀ * g'⁻¹) = θ (σ.symm g' * r₀ * (σ.symm g')⁻¹) := fun r₀ => by
        simp [hθ']
      have := hg1 (σ r) ⟨r, hr, rfl⟩
      rw [hθ'σ', e1] at this
      exact this
    · obtain ⟨r₁, hr₁, rfl⟩ := hr₁'
      refine ⟨r₁, hr₁, ?_⟩
      have e1 : ∀ r₀ : spinGroup Q₄,
          θ' (g' * σ.toMonoidHom r₀ * g'⁻¹) = θ (σ.symm g' * r₀ * (σ.symm g')⁻¹) := fun r₀ => by
        simp [hθ']
      rw [e1] at hg2
      exact hg2

theorem sqTrichotomy3_plus4 :
    SqTrichotomyOn .POmegaPlus (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three) := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
      SqTrichotomyOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact sqTrichotomy3_plus4_aux
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))

end CFSG.ClassicalInvolution.Q3.Q3TLK
