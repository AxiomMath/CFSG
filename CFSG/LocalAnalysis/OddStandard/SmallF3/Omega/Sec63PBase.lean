module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.Foundations.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_mem_sup_of_comm {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h := hcomm a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [hcomm a ha b hb, mul_inv_rev] }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAS hBS hx

theorem sec63P_mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rw [e]
    exact hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by group⟩

theorem sec63P_conjugate_eq_iff {H : Subgroup G} {g : G} :
    CFSG.conjugate H g = H ↔ g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← sec63P_mem_conjugate_iff, h]
  · intro h
    ext x
    rw [sec63P_mem_conjugate_iff, ← h x]

theorem sec63P_mul_self {u : G} (hu : orderOf u = 2) : u * u = 1 := by
  have h := pow_orderOf_eq_one u
  rw [hu] at h
  simpa only [pow_two] using h

theorem sec63P_inv_eq {u : G} (hu : orderOf u = 2) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (sec63P_mul_self hu)

theorem sec63P_conj_mem_conjugate {J : Subgroup G} {u a : G} (hu : orderOf u = 2) (ha : a ∈ J) :
    u * a * u⁻¹ ∈ CFSG.conjugate J u := by
  rw [sec63P_mem_conjugate_iff]
  have h : u * (u * a * u⁻¹) * u⁻¹ = a := by
    calc u * (u * a * u⁻¹) * u⁻¹ = (u * u) * a * (u * u)⁻¹ := by group
      _ = a := by rw [sec63P_mul_self hu]; group
  rw [h]
  exact ha

end CFSG.OddStandard.SmallF3.Omega
