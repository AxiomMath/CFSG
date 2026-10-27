module

public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSL4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSu4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_four)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def phiU : Su K p f 2 × Su K p f 2 →* Su K p f 4 :=
  MonoidHom.noncommCoprod (blockEmb K p f 4 2 0 (by norm_num)) (blockEmb K p f 4 2 2 (by norm_num))
    (fun a b => blockEmb_comm (by norm_num) (by norm_num) (Or.inl (by norm_num)) a b)

theorem phiU_apply (a b : Su K p f 2) :
    phiU K p f (a, b) =
      blockEmb K p f 4 2 0 (by norm_num) a * blockEmb K p f 4 2 2 (by norm_num) b := by
  rfl

variable (K p f) in
noncomputable abbrev xU : Su K p f 4 := rootInvSU K p f (show 2 ≤ 4 by norm_num)

theorem xU_eq : xU K p f = phiU K p f (negOneSU K p f, 1) := by
  rw [phiU_apply, map_one, mul_one]
  rfl

theorem phiU_mem_centralizer_xU (h : Su K p f 2 × Su K p f 2) :
    phiU K p f h ∈ Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, xU_eq, ← map_mul, ← map_mul]
  congr 1
  ext
  · simp [negOneSU_comm]
  · simp

theorem sup_centralizer_of_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (y₁ y₂ y₃ : G)
    (h : Subgroup.centralizer ({φ y₁} : Set H) ⊔ Subgroup.centralizer ({φ y₂} : Set H) ⊔
      Subgroup.centralizer ({φ y₃} : Set H) = ⊤) :
    Subgroup.centralizer ({y₁} : Set G) ⊔ Subgroup.centralizer ({y₂} : Set G) ⊔
      Subgroup.centralizer ({y₃} : Set G) = ⊤ := by
  have key : ∀ y : G, ∀ z ∈ Subgroup.centralizer ({φ y} : Set H),
      φ.symm z ∈ Subgroup.centralizer ({y} : Set G) := by
    intro y z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz
  set T := Subgroup.centralizer ({y₁} : Set G) ⊔ Subgroup.centralizer ({y₂} : Set G) ⊔
    Subgroup.centralizer ({y₃} : Set G) with hT
  rw [eq_top_iff]
  intro g _
  have hg : φ g ∈ Subgroup.centralizer ({φ y₁} : Set H) ⊔ Subgroup.centralizer ({φ y₂} : Set H) ⊔
      Subgroup.centralizer ({φ y₃} : Set H) := by
    rw [h]
    exact Subgroup.mem_top _
  have hle : Subgroup.centralizer ({φ y₁} : Set H) ⊔ Subgroup.centralizer ({φ y₂} : Set H) ⊔
      Subgroup.centralizer ({φ y₃} : Set H) ≤ T.comap φ.symm.toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro z hz
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (key y₁ z hz))
    · intro z hz
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (key y₂ z hz))
    · intro z hz
      exact Subgroup.mem_sup_right (key y₃ z hz)
  have := hle hg
  simpa using this

open CFSG.ClassicalInvolution.RouteD.SCRSL4 (sup_centralizer_conj)

theorem sup_eq_top_of_conj (h h' B B' : Su K p f 2)
    (key : Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹)} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹)} :
        Set (Su K p f 4)) = ⊤) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (B, B')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (B, B')} : Set (Su K p f 4)) = ⊤ := by
  have hk := sup_centralizer_conj (phiU K p f (h⁻¹, h'⁻¹)) _ _ _ key
  have e1 : phiU K p f (h⁻¹, h'⁻¹) * xU K p f * (phiU K p f (h⁻¹, h'⁻¹))⁻¹ = xU K p f := by
    have := (Subgroup.mem_centralizer_singleton_iff.mp (phiU_mem_centralizer_xU (h⁻¹, h'⁻¹)))
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have e2 : phiU K p f (h⁻¹, h'⁻¹) * phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹) *
      (phiU K p f (h⁻¹, h'⁻¹))⁻¹ = phiU K p f (B, B') := by
    simp only [← map_inv, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  have e3 : phiU K p f (h⁻¹, h'⁻¹) * (xU K p f * phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹)) *
      (phiU K p f (h⁻¹, h'⁻¹))⁻¹ = xU K p f * phiU K p f (B, B') := by
    calc phiU K p f (h⁻¹, h'⁻¹) * (xU K p f * phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹)) *
        (phiU K p f (h⁻¹, h'⁻¹))⁻¹ =
        (phiU K p f (h⁻¹, h'⁻¹) * xU K p f * (phiU K p f (h⁻¹, h'⁻¹))⁻¹) *
          (phiU K p f (h⁻¹, h'⁻¹) * phiU K p f (h * B * h⁻¹, h' * B' * h'⁻¹) *
            (phiU K p f (h⁻¹, h'⁻¹))⁻¹) := by
          group
      _ = xU K p f * phiU K p f (B, B') := by rw [e1, e2]
  rw [e1, e2, e3] at hk
  exact hk

theorem conjTr_eq_neg_of_sq (B : Su K p f 2) (hB : suMat B * suMat B = -1) :
    conjTr (unitaryInvolution K p f) (suMat B) = -suMat B := by
  have h1 : conjTr (unitaryInvolution K p f) (suMat B) * suMat B = 1 := B.2.2
  calc conjTr (unitaryInvolution K p f) (suMat B) =
      conjTr (unitaryInvolution K p f) (suMat B) * (suMat B * suMat B) * (-1) := by
        rw [hB]; simp
    _ = -suMat B := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul, mul_neg_one]

end CFSG.ClassicalInvolution.RouteD.SCRSu4
