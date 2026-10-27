module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.CGT.Timmesfeld75.Involutions

public section

namespace CFSG.CGT.T75N

open CFSG.CGT.Timmesfeld75

variable {Y S : Type} [Group Y] [Group S]

theorem conj_mem_of_normalizes_image (π : Y →* S) (hcen : π.ker ≤ Subgroup.center Y)
    {A : Subgroup Y} (hA : IsWC A) (hA1 : A ≠ ⊥) {h : Y}
    (hh : ∀ y ∈ A.map π, π h * y * (π h)⁻¹ ∈ A.map π) {x : Y} (hx : x ∈ A) :
    h * x * h⁻¹ ∈ A := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hcent : conjSubgroup h A ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro y hy
    have hy' : h⁻¹ * y * h ∈ A := mem_conjSubgroup.1 hy
    have hπ : π y ∈ A.map π := by
      have := hh (π (h⁻¹ * y * h)) ⟨_, hy', rfl⟩
      simpa [map_mul, map_inv, mul_assoc] using this
    obtain ⟨a, ha, hay⟩ := hπ
    have hz : a⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hay, inv_mul_cancel]
    have hzc : y = a * (a⁻¹ * y) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have h1 : t * a = a * t := elemAbelian_mul_comm hA.1 ht ha
    have h2 : t * (a⁻¹ * y) = (a⁻¹ * y) * t := Subgroup.mem_center_iff.1 (hcen hz) t
    calc t * y = t * (a * (a⁻¹ * y)) := by rw [← hzc]
      _ = (t * a) * (a⁻¹ * y) := by rw [mul_assoc]
      _ = (a * t) * (a⁻¹ * y) := by rw [h1]
      _ = a * (t * (a⁻¹ * y)) := by rw [mul_assoc]
      _ = a * ((a⁻¹ * y) * t) := by rw [h2]
      _ = y * t := by rw [← mul_assoc, ← hzc]
  have heq : conjSubgroup h A = A := (hA.2 t ht ht1').2 h hcent
  have hmem : h * x * h⁻¹ ∈ conjSubgroup h A := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hx
  rw [heq] at hmem
  exact hmem

end CFSG.CGT.T75N
