module

public import CFSG.ClassicalInvolution.Asc77.AscE189Comp
public import CFSG.ClassicalInvolution.Uniform.U8Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3 commute_of_map_commute_of_gen3)
open CFSG.ClassicalInvolution.Uniform (eq_of_map_eq_of_gen3)
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]


theorem e189_component_three (e : ℕ) (t : StatedLieTag) (n : ℕ) (hmodel : E189ModelAt p e t n)
    [Finite (ModelGrp p e t n)] {Λ : Set (Subgroup Y)} (hΛ : ConjInvariant Λ)
    (ψ : ModelGrp p e t n →* Y) (hker : ψ.ker ≤ Subgroup.center (ModelGrp p e t n))
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1)
    {F₁ : Subgroup (ModelGrp p e t n)} (hF₁ : F₁ ∈ modelFund p e t n)
    (hinj : ∀ x ∈ F₁, ψ x = 1 → x = 1) (hgen : Gen3 F₁) (hK : F₁.map ψ ∈ Λ)
    {z₁ : ModelGrp p e t n} (hz₁ : IsUniqueInvolution F₁ z₁) (q : ModelGrp p e t n)
    (hzt : ψ z₁ * ψ (q * z₁ * q⁻¹) = ψ (q * z₁ * q⁻¹) * ψ z₁)
    (hat : ψ z₁ * ψ (q * z₁ * q⁻¹) ≠ 1)
    (hne : conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ) ≠ F₁.map ψ)
    (hcomm : Commutes (F₁.map ψ) (conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ)))
    (hnbΛ : ∀ L ∈ Λ, ((L = F₁.map ψ ∨ Commutes L (F₁.map ψ)) ↔
      (L = conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ) ∨
        Commutes L (conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ))))) :
    (∃ K'' ∈ twinSet Λ (F₁.map ψ), K'' ≠ F₁.map ψ ∧ ∃ R₁ R₂ : Subgroup Y,
        IsSylow2In R₁ (F₁.map ψ) ∧ IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y,
        u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = ψ z₁ * ψ (q * z₁ * q⁻¹)) ∨
    (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x (F₁.map ψ)), M' ≠ conjSub x (F₁.map ψ) ∧
        ∀ w ∈ conjSub x (F₁.map ψ) ⊔ M', w * (ψ z₁ * ψ (q * z₁ * q⁻¹)) =
          (ψ z₁ * ψ (q * z₁ * q⁻¹)) * w) := by
  set t₁ := q * z₁ * q⁻¹ with ht₁
  have hgenS : ∀ y : ModelGrp p e t n, Gen3 (conjSub y F₁) := fun y =>
    hgen.map (MulAut.conj y).toMonoidHom
  have h1 : ⁅z₁, t₁⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hzt
  have h2 : z₁ * t₁ ∉ ψ.ker := fun h => hat (by rw [← map_mul]; exact h)
  have h3 : conjSub t₁ F₁ ≠ F₁ := by
    intro heq
    apply hne
    rw [← map_conjSub_eq, heq]
  have h4 : Commutes F₁ (conjSub t₁ F₁) := by
    intro a ha b hb
    refine commute_of_map_commute_of_gen3 ψ hker hk3 hgen (b := b) (fun a' ha' => ?_) a ha
    have hb' : ψ b ∈ conjSub (ψ t₁) (F₁.map ψ) := by
      rw [← map_conjSub_eq]
      exact Subgroup.mem_map_of_mem ψ hb
    exact hcomm (ψ a') (Subgroup.mem_map_of_mem ψ ha') (ψ b) hb'
  have hzK : IsUniqueInvolution (F₁.map ψ) (ψ z₁) := isUniqueInvolution_map_of_injOn ψ hinj hz₁
  have h5 : ∀ S : Subgroup (ModelGrp p e t n), (∃ y, S = conjSub y F₁) →
      ((S = F₁ ∨ Commutes S F₁) ↔ (S = conjSub t₁ F₁ ∨ Commutes S (conjSub t₁ F₁))) := by
    rintro S ⟨y, rfl⟩
    have hSΛ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hF₂map : (conjSub t₁ F₁).map ψ = conjSub (ψ t₁) (F₁.map ψ) := map_conjSub_eq ψ t₁ F₁
    have e1 : conjSub y F₁ = F₁ ↔ (conjSub y F₁).map ψ = F₁.map ψ :=
      ⟨fun h => by rw [h], fun h => eq_of_map_eq_of_gen3 ψ hker hk3 (hgenS y) hgen h⟩
    have e2 : conjSub y F₁ = conjSub t₁ F₁ ↔
        (conjSub y F₁).map ψ = conjSub (ψ t₁) (F₁.map ψ) :=
      ⟨fun h => by rw [h, hF₂map], fun h =>
        eq_of_map_eq_of_gen3 ψ hker hk3 (hgenS y) (hgenS t₁) (h.trans hF₂map.symm)⟩
    have e3 : Commutes (conjSub y F₁) F₁ ↔ Commutes ((conjSub y F₁).map ψ) (F₁.map ψ) :=
      ⟨fun h => by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, h a ha b hb],
        fun h a ha b hb =>
          commute_of_map_commute_of_gen3 ψ hker hk3 (hgenS y) (b := b) (fun a' ha' =>
            h (ψ a') (Subgroup.mem_map_of_mem ψ ha') (ψ b) (Subgroup.mem_map_of_mem ψ hb)) a ha⟩
    have e4 : Commutes (conjSub y F₁) (conjSub t₁ F₁) ↔
        Commutes ((conjSub y F₁).map ψ) (conjSub (ψ t₁) (F₁.map ψ)) :=
      ⟨fun h => by
        rw [← hF₂map]
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, h a ha b hb],
        fun h a ha b hb =>
          commute_of_map_commute_of_gen3 ψ hker hk3 (hgenS y) (b := b) (fun a' ha' =>
            h (ψ a') (Subgroup.mem_map_of_mem ψ ha') (ψ b)
              (by rw [← hF₂map]; exact Subgroup.mem_map_of_mem ψ hb)) a ha⟩
    rw [e1, e2, e3, e4]
    exact hnbΛ _ hSΛ
  rcases hmodel ψ.ker hker F₁ hF₁ z₁ hz₁ q h1 h2 h3 h4 h5 with
    ⟨F₃, -, hF₃ne, hF₁F₃, ⟨y, hy⟩, z₃, hz₃, hz₁z₃, R₁, R₃, hR₁, hR₃, u, x, hu, huN, hu2, hux⟩ |
    ⟨x, M₂, -, hM₂ne, -, ⟨y, hy⟩, z₂, hz₂, hxz, hw⟩
  · left
    subst hy
    have hinj₃ := injOn_conjSub ψ hinj y
    have hΛ₃ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hz₃' : ψ z₃ = ψ z₁ := by
      have : ψ (z₁⁻¹ * z₃) = 1 := hz₁z₃
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    refine ⟨(conjSub y F₁).map ψ, ⟨hΛ₃, ψ z₁, hzK, ?_⟩, ?_, R₁.map ψ, R₃.map ψ,
      isSylow2In_map_of_injOn ψ hinj hR₁, isSylow2In_map_of_injOn ψ hinj₃ hR₃, ?_, ψ u, ψ x, ?_,
      ?_, ?_, ?_⟩
    · rw [← hz₃']
      exact isUniqueInvolution_map_of_injOn ψ hinj₃ hz₃
    · intro h
      exact hF₃ne (eq_of_map_eq_of_gen3 ψ hker hk3 (hgenS y) hgen h)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hF₁F₃ a (hR₁.1 ha) b (hR₃.1 hb)]
    · rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem ψ hu
    · exact fun h => huN h
    · rw [← map_mul]
      exact (MonoidHom.mem_ker.mp hu2)
    · have h5 : ψ ((x * u * x⁻¹)⁻¹ * (z₁ * t₁)) = 1 := hux
      rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h5
      rw [← map_mul]
      simpa [map_mul, map_inv] using h5
  · right
    subst hy
    have hinj₂ := injOn_conjSub ψ hinj y
    have hΛ₂ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hxK : IsUniqueInvolution (conjSub (ψ x) (F₁.map ψ)) (ψ x * ψ z₁ * (ψ x)⁻¹) := hzK.conj _
    have hz₂' : ψ z₂ = ψ x * ψ z₁ * (ψ x)⁻¹ := by
      have : ψ ((x * z₁ * x⁻¹)⁻¹ * z₂) = 1 := hxz
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      simpa [map_mul, map_inv] using this.symm
    refine ⟨ψ x, (conjSub y F₁).map ψ, ⟨hΛ₂, ψ x * ψ z₁ * (ψ x)⁻¹, hxK, ?_⟩, ?_, ?_⟩
    · rw [← hz₂']
      exact isUniqueInvolution_map_of_injOn ψ hinj₂ hz₂
    · rw [← map_conjSub_eq]
      intro h
      exact hM₂ne (eq_of_map_eq_of_gen3 ψ hker hk3 (hgenS y) (hgenS x) h)
    · intro w hw
      rw [← map_conjSub_eq, ← Subgroup.map_sup] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      have h5 := MonoidHom.mem_ker.mp (hw w₀ hw₀)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_mul] at h5
      exact h5

end CFSG.ClassicalInvolution.Q3.Q3T7E9
