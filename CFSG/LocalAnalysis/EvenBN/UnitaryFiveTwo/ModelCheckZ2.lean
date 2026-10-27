module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckW
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada

@[expose] def Z₂sub : Subgroup SU52 := X₃sub ⊔ ZX₄sub

theorem X₂sub_le_Ssub : X₂sub ≤ Ssub := le_sup_right.trans (le_sup_left.trans le_sup_left)

theorem X₃sub_le_Ssub : X₃sub ≤ Ssub := le_sup_right.trans le_sup_left

theorem X₃sub_comm_ZX₄sub {a c : SU52} (ha : a ∈ X₃sub) (hc : c ∈ ZX₄sub) : a * c = c * a :=
  ZX₄sub_comm hc (X₃sub_le_Ssub ha)

theorem exists_of_mem_Z₂sub {g : SU52} (hg : g ∈ Z₂sub) :
    ∃ γ β : F4, ValidPair 0 β ∧ mat g = x₃Mat γ * x₄Mat 0 β := by
  obtain ⟨a, ha, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha c hc => X₃sub_comm_ZX₄sub ha hc) hg
  obtain ⟨γ, hγ⟩ := mem_X₃sub.1 ha
  obtain ⟨α, β, hα, hβ⟩ := mem_x₄Sub.1 hc
  subst hα
  exact ⟨γ, β, x₄_coord_rel hβ, by rw [mat_mul, hγ, hβ]⟩

theorem Z₂sub_le_Fsub : Z₂sub ≤ Fsub := sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem Z₂sub_le_A₁sub : Z₂sub ≤ A₁sub :=
  sup_le X₃sub_le_A₁sub (ZX₄sub_le_X₄sub.trans X₄sub_le_A₁sub')

theorem Fsub_inf_A₁sub : Fsub ⊓ A₁sub = Z₂sub := by
  refine le_antisymm (fun g hg => ?_) (le_inf Z₂sub_le_Fsub Z₂sub_le_A₁sub)
  obtain ⟨hgF, hgA⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨⟨b₁, γ, b₄⟩, -, h₄, hm⟩ := exists_fMat_of_mem_Fsub hgF
  have hb₁ : b₁ = 0 := by
    have := (mem_A₁sub.1 hgA).2.2
    rw [hm, fMat_eq] at this
    simpa using this
  subst hb₁
  have h₄' : (0 : F4) * bar 0 = b₄ + bar b₄ := h₄
  have e : g = x₃SU γ * x₄SU 0 b₄ h₄' := ext_mat (by
    rw [hm, mat_mul, mat_x₃SU, mat_x₄SU, fMat_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five])
  rw [e]
  exact mul_mem (mem_sup_left (x₃SU_mem γ)) (mem_sup_right (mem_x₄Sub.2 ⟨0, b₄, rfl, rfl⟩))

theorem X₃sub_inf_ZX₄sub : X₃sub ⊓ ZX₄sub = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨γ, hγ⟩ := mem_X₃sub.1 (Subgroup.mem_inf.1 hg).1
  obtain ⟨α, β, hα, hβ⟩ := mem_x₄Sub.1 (Subgroup.mem_inf.1 hg).2
  subst hα
  have h30 : γ = 0 := by
    have := congrFun (congrFun (hγ.symm.trans hβ) 3) 0
    simpa [x₃Mat, x₄Mat] using this
  rw [mem_bot]
  exact ext_mat (by rw [hγ, h30, x₃Mat_zero, mat_one])

theorem card_Z₂sub : Nat.card Z₂sub = 8 := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X₃sub ZX₄sub
    fun _ ha _ hc => X₃sub_comm_ZX₄sub ha hc).1
  rw [X₃sub_inf_ZX₄sub, card_bot, mul_one, card_X₃sub, card_ZX₄sub] at hc
  exact hc

theorem x₃Mat_x₂Mat_check : ∀ γ c : F4, ∃ β : F4,
    x₃Mat γ * x₂Mat c * x₃Mat γ * x₂Mat c = x₄Mat 0 β := by
  decide +kernel

theorem Z₂sub_comm_x₂ {g : SU52} (hg : g ∈ Z₂sub) (c : F4) :
    g * x₂SU c * g⁻¹ * (x₂SU c)⁻¹ ∈ ZX₄sub := by
  obtain ⟨a, ha, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha c hc => X₃sub_comm_ZX₄sub ha hc) hg
  have hzx : x₂SU c * z = z * x₂SU c := ZX₄sub_comm hz (X₂sub_le_Ssub (x₂SU_mem c))
  rw [show a * z * x₂SU c * (a * z)⁻¹ = a * (z * x₂SU c * z⁻¹) * a⁻¹ by group, ← hzx,
    mul_inv_cancel_right]
  obtain ⟨γ, hγ⟩ := mem_X₃sub.1 ha
  obtain ⟨β, hβ⟩ := x₃Mat_x₂Mat_check γ c
  refine mem_x₄Sub.2 ⟨0, β, rfl, ?_⟩
  rw [mat_mul, mat_mul, mat_mul, mat_inv_of_x₃ hγ, mat_inv_of_x₂ (mat_x₂SU c), hγ, mat_x₂SU, hβ]

@[expose] def trF4 (γ : F4) : F4 := γ + bar γ

theorem trF4_valid : ∀ γ : F4, (0 : F4) * bar 0 = trF4 γ + bar (trF4 γ) := by
  unfold trF4
  decide

theorem z₂_check : ∀ γ β : F4, ValidPair 0 β →
    x₃Mat γ * x₄Mat 0 β =
      x₁Mat 0 (trF4 (bar F4.ω * γ)) * (x₂Mat 1 * x₁Mat 0 (trF4 (bar F4.ω * γ)) * x₂Mat 1) *
        (x₁Mat 0 (trF4 γ) * x₃Mat (β + trF4 (bar F4.ω * γ) + trF4 γ) *
          (x₂Mat F4.ω * (x₁Mat 0 (trF4 γ) * x₃Mat (β + trF4 (bar F4.ω * γ) + trF4 γ)) *
            x₂Mat F4.ω)) := by
  unfold ValidPair trF4
  decide +kernel

theorem exists_Fsub_of_mem_Z₂sub {g : SU52} (hg : g ∈ Z₂sub) :
    ∃ f₁ ∈ Fsub, ∃ f₂ ∈ Fsub, g = f₁ * (x₂SU 1 * f₁ * (x₂SU 1)⁻¹) *
      (f₂ * (x₂SU F4.ω * f₂ * (x₂SU F4.ω)⁻¹)) := by
  obtain ⟨γ, β, hβ, hm⟩ := exists_of_mem_Z₂sub hg
  have hZ₁ : ∀ (b : F4) (h : (0 : F4) * bar 0 = b + bar b), x₁SU 0 b h ∈ Fsub := fun b h =>
    mem_sup_left (mem_sup_left (mem_x₁Sub.2 ⟨0, b, rfl, rfl⟩))
  have hX₃ : ∀ q : F4, x₃SU q ∈ Fsub := fun q => mem_sup_left (mem_sup_right (x₃SU_mem q))
  refine ⟨x₁SU 0 _ (trF4_valid (bar F4.ω * γ)), hZ₁ _ _,
    x₁SU 0 _ (trF4_valid γ) * x₃SU (β + trF4 (bar F4.ω * γ) + trF4 γ),
    mul_mem (hZ₁ _ _) (hX₃ _), ext_mat ?_⟩
  simp only [mat_mul, mat_inv_of_x₂ (mat_x₂SU _), mat_x₂SU, mat_x₁SU, mat_x₃SU]
  rw [hm]
  exact z₂_check γ β hβ

theorem mem_closure_orbV (c : Fin 3 → F4) : c ∈ AddSubmonoid.closure (Set.range orbV) := by
  have hv : ∀ k, orbV k ∈ AddSubmonoid.closure (Set.range orbV) := fun k =>
    AddSubmonoid.subset_closure ⟨k, rfl⟩
  have hb : ∀ i : Fin 3, Pi.single i (1 : F4) ∈ AddSubmonoid.closure (Set.range orbV) ∧
      Pi.single i F4.ω ∈ AddSubmonoid.closure (Set.range orbV) := by
    intro i
    fin_cases i
    · exact ⟨by convert hv 3 using 1; decide, by convert hv 11 using 1; decide⟩
    · exact ⟨by convert add_mem (add_mem (hv 5) (hv 3)) (hv 1) using 1; decide,
        by convert add_mem (add_mem (hv 7) (hv 3)) (hv 1) using 1; decide⟩
    · exact ⟨by convert hv 0 using 1; decide, by convert hv 1 using 1; decide⟩
  have key : ∀ (i : Fin 3) (a : F4), Pi.single i a ∈ AddSubmonoid.closure (Set.range orbV) := by
    intro i a
    rcases F4_cases a with rfl | rfl | rfl | rfl
    · rw [Pi.single_zero]
      exact zero_mem _
    · exact (hb i).1
    · exact (hb i).2
    · rw [Pi.single_add]
      exact add_mem (hb i).2 (hb i).1
  rw [← Finset.univ_sum_single c]
  exact sum_mem fun i _ => key i (c i)

theorem valid_mul_omega : ∀ a : F4, a * bar a = a * bar a * F4.ω + bar (a * bar a * F4.ω) := by
  decide

@[expose] def nfA₁ (c : Fin 3 → F4) : SU52 :=
  x₂SU (c 0) * x₃SU (c 2) * x₄SU (c 1) (c 1 * bar (c 1) * F4.ω) (valid_mul_omega (c 1))

theorem nfA₁_mem (c : Fin 3 → F4) : nfA₁ c ∈ A₁sub :=
  mul_mem (mul_mem (X₂sub_le_A₁sub (x₂SU_mem _)) (X₃sub_le_A₁sub (x₃SU_mem _)))
    (X₄sub_le_A₁sub' (x₄SU_mem _ _ _))

theorem cvec_nfA₁ (c : Fin 3 → F4) : cvec (mat (nfA₁ c)) = c := by
  rw [nfA₁, mat_mul, mat_mul, mat_x₂SU, mat_x₃SU, mat_x₄SU, cvec_nf]
  funext i
  fin_cases i <;> rfl

theorem exists_cvec_eq_of_orb {T : Set SU52} (hT : T ⊆ A₁sub) (h1 : 1 ∈ T)
    (hmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T) (horb : ∀ k, orbSU k * b₀SU * (orbSU k)⁻¹ ∈ T)
    (c : Fin 3 → F4) : ∃ a ∈ T, cvec (mat a) = c := by
  let M : AddSubmonoid (Fin 3 → F4) :=
    { carrier := {c | ∃ a ∈ T, cvec (mat a) = c}
      zero_mem' := ⟨1, h1, by rw [mat_one, cvec_one]⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, hmul a ha b hb, cvec_mul (hT ha) (hT hb)⟩ }
  have hle : AddSubmonoid.closure (Set.range orbV) ≤ M := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, horb k, cvec_orb k⟩
  exact hle (mem_closure_orbV c)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
