module

public import CFSG.CGT.T75O.Class
public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem mem_normalizer_of_conj_mem {a x : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1)
    (hx : x * a * x⁻¹ ∈ T) : x ∈ Subgroup.normalizer (T : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  by_contra hne
  have hbot := c.hy.pair.wc.inf_conj_eq_bot hne
  have h1 : x * a * x⁻¹ ∈ conjSubgroup x T := conj_mem_conjSubgroup x (secA_le_left ha)
  have h2 : x * a * x⁻¹ ∈ T ⊓ conjSubgroup x T := ⟨hx, h1⟩
  rw [hbot, Subgroup.mem_bot] at h2
  exact conj_ne_one' rfl ha1 h2

theorem normalizer_secA_le :
    Subgroup.normalizer (secA T T₁ : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  intro x hx
  obtain ⟨a, ha, ha1⟩ := c.exists_mem_secA_ne_one
  exact c.mem_normalizer_of_conj_mem ha ha1
    (secA_le_left ((Subgroup.mem_normalizer_iff.1 hx a).1 ha))

theorem isPGroup_T : IsPGroup 2 T := fun x =>
  ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (c.mul_self_T x.2)⟩

theorem mem_secA_of_mem_member {R : Set (Subgroup G)} (hR : IsRootClass R)
    (hA : secA T T₁ ∈ R) {B : Subgroup G} (hB : B ∈ R) {y : G} (hy : y ∈ B) (hyT : y ∈ T) :
    y ∈ secA T T₁ := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hy
  by_cases ha'1 : a' = 1
  · rw [ha'1, map_one]
    exact one_mem _
  · exact c.mem_secA_of_conj_mem ha' ha'1 (by simpa [MulAut.conj_apply] using hyT)

end Cfg56

end CFSG.CGT.T75O
