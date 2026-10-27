module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerOdd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSylowAut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {Y : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem comm_of_mul_self_eq_one [CharP E 2] (hc : U3RootCoords Y σ u v) {a : G} (ha : a ∈ Y)
    (haa : a * a = 1) {z : G} (hz : z ∈ Y) : a * z = z * a := by
  obtain ⟨-, h2⟩ := hc.sq ha
  rw [pow_two, haa, hc.v_one_eq_zero] at h2
  have hu : u a = 0 := by
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact h
    · exact (map_eq_zero σ).mp h
  exact hc.comm_of_u_eq_zero ha hu hz

end U3RootCoords

section Quadratic

variable {G : Type*} [Group G]

theorem mem_centralizer_of_mul_self_eq_one {E : Type*} [Field E] [CharP E 2] {σ : E →+* E}
    {U Y₁ Y₂ : Subgroup G} {u₁ v₁ u₂ v₂ : G → E} (hc₁ : U3RootCoords Y₁ σ u₁ v₁)
    (hc₂ : U3RootCoords Y₂ σ u₂ v₂) (hU : Y₁ ⊔ Y₂ = U) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {x : G} (hx : x ∈ U) (hxx : x * x = 1) :
    x ∈ centralizer (U : Set G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm (hU ▸ hx)
  have hab : a * b = b * a := hcomm a ha b hb
  have h1 : a * a = (b * b)⁻¹ := by
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
    rw [e] at hxx
    exact eq_inv_of_mul_eq_one_left hxx
  have h2 : a * a ∈ Y₁ ⊓ Y₂ :=
    mem_inf.mpr ⟨mul_mem ha ha, by rw [h1]; exact inv_mem (mul_mem hb hb)⟩
  rw [hinf, mem_bot] at h2
  have h3 : b * b = 1 := by
    have := congrArg (·⁻¹) h1
    simp only [inv_inv, h2, inv_one] at this
    exact this.symm
  have haz : ∀ z ∈ Y₁, a * z = z * a := fun z hz => hc₁.comm_of_mul_self_eq_one ha h2 hz
  have hbz : ∀ z ∈ Y₂, b * z = z * b := fun z hz => hc₂.comm_of_mul_self_eq_one hb h3 hz
  have hc : ∀ z ∈ U, (a * b) * z = z * (a * b) := by
    intro z hz
    refine commute_of_mem_sup_of_commute_factors hcomm (fun a' ha' => ?_) (fun b' hb' => ?_)
      (hU ▸ hz)
    · calc a * b * a' = a * (b * a') := by group
        _ = a * (a' * b) := by rw [(hcomm a' ha' b hb).symm]
        _ = (a * a') * b := by group
        _ = (a' * a) * b := by rw [haz a' ha']
        _ = a' * (a * b) := by group
    · calc a * b * b' = a * (b * b') := by group
        _ = a * (b' * b) := by rw [hbz b' hb']
        _ = (a * b') * b := by group
        _ = (b' * a) * b := by rw [hcomm a ha b' hb']
        _ = b' * (a * b) := by group
  exact mem_centralizer_iff.mpr fun z hz => (hc z hz).symm

theorem comm_mem_inf_of_mem {U U' : Subgroup G} (hU'U : U' ≤ normalizer (U : Set G))
    (hUU' : U ≤ normalizer (U' : Set G)) {y w : G} (hy : y ∈ U') (hw : w ∈ U) :
    y * w * y⁻¹ * w⁻¹ ∈ U ⊓ U' := by
  refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp (hU'U hy) w).mp hw) (inv_mem hw), ?_⟩
  have h1 : w * y⁻¹ * w⁻¹ ∈ U' := (mem_normalizer_iff.mp (hUU' hw) _).mp (inv_mem hy)
  have e : y * w * y⁻¹ * w⁻¹ = y * (w * y⁻¹ * w⁻¹) := by group
  rw [e]
  exact mul_mem hy h1

theorem comm_mem_center_of_mem_inf {U U' : Subgroup G} (hU'U : U' ≤ normalizer (U : Set G))
    (hinv : ∀ x ∈ U, x * x = 1 → x ∈ centralizer (U : Set G))
    (hU' : ∀ a ∈ U', ∀ b ∈ U', a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1)
    {y d : G} (hy : y ∈ U') (hd : d ∈ U ⊓ U') :
    y * d * y⁻¹ * d⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  obtain ⟨hdU, hdU'⟩ := mem_inf.mp hd
  have hmem : y * d * y⁻¹ * d⁻¹ ∈ U :=
    mul_mem ((mem_normalizer_iff.mp (hU'U hy) d).mp hdU) (inv_mem hdU)
  exact mem_inf.mpr ⟨hmem, hinv _ hmem (hU' y hy d hdU')⟩

theorem sq_comm_mem_center {U U' : Subgroup G} (hU'U : U' ≤ normalizer (U : Set G))
    (hUU' : U ≤ normalizer (U' : Set G))
    (hinv : ∀ x ∈ U, x * x = 1 → x ∈ centralizer (U : Set G))
    (hsq : ∀ x ∈ U, x * x ∈ centralizer (U : Set G))
    (hU' : ∀ a ∈ U', ∀ b ∈ U', a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1)
    {y w : G} (hy : y ∈ U') (hw : w ∈ U) :
    y * y * w * (y * y)⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  set c := y * w * y⁻¹ * w⁻¹ with hcdef
  have hc := comm_mem_inf_of_mem hU'U hUU' hy hw
  have hcU : c ∈ U := (mem_inf.mp hc).1
  have h1 := comm_mem_center_of_mem_inf hU'U hinv hU' hy hc
  have h2 : c * c ∈ U ⊓ centralizer (U : Set G) := mem_inf.mpr ⟨mul_mem hcU hcU, hsq c hcU⟩
  have e : y * y * w * (y * y)⁻¹ * w⁻¹ = (y * c * y⁻¹ * c⁻¹) * (c * c) := by
    rw [hcdef]
    group
  rw [e]
  exact mul_mem h1 h2

end Quadratic

end CFSG.SeitzReduction.RankOne
