module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoRadical

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {h : UnitaryFieldData 2 1 F} {E : Type*} [Group E]
  {θ : E →* hypPSU h 3 0} (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
include hθ hC

theorem commute_of_swap {G Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {s x y : E}
    (hs : IsLift θ G s) (hx : IsLift θ Y x) (hy : IsLift θ Y' y) {B B' : Matrix (Fin 3) (Fin 3) F}
    (hY : G * Y = nMat B * G) (hY' : G * Y' = nMat B' * G) : Commute x y :=
  (Commute.conj_iff s).mp (commute_of_isLift_nMat hθ hC (hs.conj hx hY) (hs.conj hy hY'))

theorem commute_c_a {a c : F} {x z : E} (hx : IsLift θ (lMat h (utMat a 0 0)) x)
    (hz : IsLift θ (lMat h (utMat 0 0 c)) z) : Commute z x := by
  obtain ⟨s, hs⟩ := exists_isLift hθ (swapElt h {1, 2})
  exact commute_of_swap hθ hC hs hz hx (swap_mul_lMat_c h c) (swap_mul_lMat_a h a)

theorem commute_c_b {b c : F} {y z : E} (hy : IsLift θ (lMat h (utMat 0 b 0)) y)
    (hz : IsLift θ (lMat h (utMat 0 0 c)) z) : Commute z y := by
  obtain ⟨s, hs⟩ := exists_isLift hθ (swapElt h {2})
  exact commute_of_swap hθ hC hs hz hy (swap'_mul_lMat_c h c) (swap'_mul_lMat_b h b)

theorem commute_c_c {c c' : F} {w z : E} (hw : IsLift θ (lMat h (utMat 0 0 c')) w)
    (hz : IsLift θ (lMat h (utMat 0 0 c)) z) : Commute z w := by
  obtain ⟨s, hs⟩ := exists_isLift hθ (swapElt h {1, 2})
  exact commute_of_swap hθ hC hs hz hw (swap_mul_lMat_c h c) (swap_mul_lMat_c h c')

theorem commute_of_lift_ut {c : F} {z u : E} (hz : θ z = hypProj h 3 0 (lHom h (ut 0 0 c)))
    {A : SpecialLinearGroup (Fin 3) F} (hA : A ∈ LinearFlag.unitriangular 3 F)
    (hu : θ u = hypProj h 3 0 (lHom h A)) : Commute z u := by
  obtain ⟨a, b, c', rfl⟩ := mem_unitriangular_iff.mp hA
  obtain ⟨x, hx⟩ := exists_isLift_lMat hθ (ut a 0 0)
  obtain ⟨y, hy⟩ := exists_isLift_lMat hθ (ut 0 b 0)
  obtain ⟨w, hw⟩ := exists_isLift_lMat hθ (ut 0 0 (c' + a * b))
  have hxyw : IsLift θ (lMat h (ut a b c')) (x * y * w) := by
    rw [isLift_lMat_iff, map_mul, map_mul, isLift_lMat_iff.mp hx, isLift_lMat_iff.mp hy,
      isLift_lMat_iff.mp hw, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← ut_eq_mul]
  obtain ⟨k, hk, rfl⟩ := hxyw.exists_ker (isLift_lMat_iff.mpr hu)
  have hz' : IsLift θ (lMat h (utMat 0 0 c)) z := isLift_lMat_iff.mpr hz
  exact (((commute_c_a hθ hC hx hz').mul_right (commute_c_b hθ hC hy hz')).mul_right
    (commute_c_c hθ hC hw hz')).mul_right (Subgroup.mem_center_iff.mp (hC hk) z)

theorem commutator_sq_eq_one_of_lift_ut {u v : E} {A A' : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ LinearFlag.unitriangular 3 F) (hA' : A' ∈ LinearFlag.unitriangular 3 F)
    (hu : θ u = hypProj h 3 0 (lHom h A)) (hv : θ v = hypProj h 3 0 (lHom h A')) :
    ⁅u, v⁆ ^ 2 = 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_unitriangular_iff.mp hA
  obtain ⟨a', b', c', rfl⟩ := mem_unitriangular_iff.mp hA'
  have hcomm : θ ⁅u, v⁆ = hypProj h 3 0 (lHom h (ut 0 0 (a * b' + a' * b))) := by
    rw [map_commutatorElement, hu, hv, ← map_commutatorElement, ← map_commutatorElement,
      ut_commutator]
  have hsq : θ (u ^ 2) = hypProj h 3 0 (lHom h (ut 0 0 (a * b))) := by
    rw [map_pow, hu, ← map_pow, ← map_pow, ut_sq]
  have h1 : Commute ⁅u, v⁆ u := commute_of_lift_ut hθ hC hcomm (ut_mem_unitriangular a b c) hu
  have h2 : Commute (u ^ 2) v := commute_of_lift_ut hθ hC hsq (ut_mem_unitriangular a' b' c') hv
  rw [← commutatorElement_sq_left h1.symm, commutatorElement_eq_one_iff_mul_comm.mpr h2]

omit hθ hC in
variable (θ) in
@[expose] noncomputable def utPre : Subgroup E :=
  ((LinearFlag.unitriangular 3 F).map ((hypProj h 3 0).comp (lHom h))).comap θ

omit [CharP F 2] hθ hC in
theorem mem_utPre {u : E} :
    u ∈ utPre θ ↔ ∃ A ∈ LinearFlag.unitriangular 3 F, θ u = hypProj h 3 0 (lHom h A) := by
  simp only [utPre, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp,
    Function.comp_apply]
  exact ⟨fun ⟨A, hA, e⟩ => ⟨A, hA, e.symm⟩, fun ⟨A, hA, e⟩ => ⟨A, hA, e.symm⟩⟩

theorem sq_eq_one_of_mem_commutator_utPre {z : E} (hz : z ∈ ⁅utPre θ, utPre θ⁆) : z ^ 2 = 1 := by
  let Ω : Subgroup E :=
    { carrier := {z | (∃ c : F, θ z = hypProj h 3 0 (lHom h (ut 0 0 c))) ∧ z ^ 2 = 1}
      mul_mem' := by
        rintro z₁ z₂ ⟨⟨c₁, hc₁⟩, h₁⟩ ⟨⟨c₂, hc₂⟩, h₂⟩
        refine ⟨⟨c₁ + c₂, ?_⟩, ?_⟩
        · rw [map_mul, hc₁, hc₂, ← map_mul, ← map_mul, ut_mul]
          congr 3 <;> ring
        · rw [(commute_of_lift_ut hθ hC hc₁ (ut_mem_unitriangular 0 0 c₂) hc₂).mul_pow, h₁, h₂,
            mul_one]
      one_mem' := ⟨⟨0, by rw [ut_zero, map_one, map_one, map_one]⟩, one_pow 2⟩
      inv_mem' := by
        rintro z ⟨⟨c, hc⟩, h₁⟩
        refine ⟨⟨c, ?_⟩, by rw [inv_pow, h₁, inv_one]⟩
        rw [map_inv, hc, ← map_inv, ← map_inv, ut_inv]
        congr 3
        ring }
  have hle : ⁅utPre θ, utPre θ⁆ ≤ Ω := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨A, hA, hu'⟩ := mem_utPre.mp hu
    obtain ⟨A', hA', hv'⟩ := mem_utPre.mp hv
    obtain ⟨a, b, c, rfl⟩ := mem_unitriangular_iff.mp hA
    obtain ⟨a', b', c', rfl⟩ := mem_unitriangular_iff.mp hA'
    refine ⟨⟨a * b' + a' * b, ?_⟩, commutator_sq_eq_one_of_lift_ut hθ hC hA hA' hu' hv'⟩
    rw [map_commutatorElement, hu', hv', ← map_commutatorElement, ← map_commutatorElement,
      ut_commutator]
  exact (hle hz).2

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo
