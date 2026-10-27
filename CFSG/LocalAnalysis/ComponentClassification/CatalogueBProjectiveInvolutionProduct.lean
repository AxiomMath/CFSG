module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct

open scoped commutatorElement

variable {X Y : Type*} [Group X] [Group Y]

theorem fst_image_perfect (L : Subgroup (X × Y)) [Group.IsPerfect L] :
    Group.IsPerfect (L.map (MonoidHom.fst X Y)) :=
  Group.IsPerfect.ofSurjective ((MonoidHom.fst X Y).subgroupMap_surjective L)

theorem snd_image_perfect (L : Subgroup (X × Y)) [Group.IsPerfect L] :
    Group.IsPerfect (L.map (MonoidHom.snd X Y)) :=
  Group.IsPerfect.ofSurjective ((MonoidHom.snd X Y).subgroupMap_surjective L)

theorem perfect_product_le_normal_step
    (L H K : Subgroup (X × Y)) [Group.IsPerfect L]
    (hLH : L ≤ H) (hHK : H ≤ K) (hN : (H.subgroupOf K).Normal)
    (hproduct : (L.map (MonoidHom.fst X Y)).prod
      (L.map (MonoidHom.snd X Y)) ≤ K) :
    (L.map (MonoidHom.fst X Y)).prod (L.map (MonoidHom.snd X Y)) ≤ H := by
  have hnormalize := (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN
  have hcomm : ⁅K, H⁆ ≤ H :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormalize
  let : Group.IsPerfect (L.map (MonoidHom.fst X Y)) := fst_image_perfect L
  let : Group.IsPerfect (L.map (MonoidHom.snd X Y)) := snd_image_perfect L
  apply Subgroup.prod_le_iff.mpr
  constructor
  · rw [← Subgroup.commutator_eq_self (H := L.map (MonoidHom.fst X Y)),
      Subgroup.map_commutator]
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    change z.1 = y at hzy
    have hxK : (x, (1 : Y)) ∈ K := hproduct ⟨hx, Subgroup.one_mem _⟩
    have hzH : z ∈ H := hLH hz
    have hc := hcomm (Subgroup.commutator_mem_commutator hxK hzH)
    have heq : ⁅(x, (1 : Y)), z⁆ = (⁅x, y⁆, (1 : Y)) := by
      apply Prod.ext
      · simpa only [commutatorElement_def, Prod.fst_mul, Prod.fst_inv] using
          congrArg (fun t : X => x * t * x⁻¹ * t⁻¹) hzy
      · simp [commutatorElement_def]
    rw [heq] at hc
    simpa [commutatorElement_def] using hc
  · rw [← Subgroup.commutator_eq_self (H := L.map (MonoidHom.snd X Y)),
      Subgroup.map_commutator]
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    change z.2 = y at hzy
    have hxK : ((1 : X), x) ∈ K := hproduct ⟨Subgroup.one_mem _, hx⟩
    have hzH : z ∈ H := hLH hz
    have hc := hcomm (Subgroup.commutator_mem_commutator hxK hzH)
    have heq : ⁅((1 : X), x), z⁆ = ((1 : X), ⁅x, y⁆) := by
      apply Prod.ext
      · simp [commutatorElement_def]
      · simpa only [commutatorElement_def, Prod.snd_mul, Prod.snd_inv] using
          congrArg (fun t : Y => x * t * x⁻¹ * t⁻¹) hzy
    rw [heq] at hc
    simpa [commutatorElement_def] using hc

theorem perfect_product_le_subnormal_overgroup
    (H : Subgroup (X × Y)) (hH : H.IsSubnormal)
    (L : Subgroup (X × Y)) [Group.IsPerfect L] (hLH : L ≤ H) :
    (L.map (MonoidHom.fst X Y)).prod (L.map (MonoidHom.snd X Y)) ≤ H := by
  induction hH with
  | top => exact le_top
  | step H K hHK hK hN ih =>
      exact perfect_product_le_normal_step L H K hLH hHK hN (ih (hLH.trans hHK))

theorem perfect_subnormal_eq_product
    (L : Subgroup (X × Y)) [Group.IsPerfect L] (hL : L.IsSubnormal) :
    L = (L.map (MonoidHom.fst X Y)).prod (L.map (MonoidHom.snd X Y)) := by
  apply le_antisymm
  · exact Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
  · exact perfect_product_le_subnormal_overgroup L hL L le_rfl

end CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct
