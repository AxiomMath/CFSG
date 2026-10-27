module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

theorem sec5c3q_phi_comm (hm : Sec5Model58 t L z r A φ) (v w : Fin 6 → ZMod 2) :
    φ v * φ w = φ w * φ v := by
  calc φ v * φ w = φ (v + w) := (hm.perm.map_add v w).symm
    _ = φ (w + v) := by rw [add_comm]
    _ = φ w * φ v := hm.perm.map_add w v

theorem sec5c3q_A_comm (hm : Sec5Model58 t L z r A φ) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := by
  obtain ⟨v, rfl⟩ := (hm.perm.mem_iff x).mp hx
  obtain ⟨w, rfl⟩ := (hm.perm.mem_iff y).mp hy
  exact sec5c3q_phi_comm hm v w

theorem sec5c3q_A_sq (hm : Sec5Model58 t L z r A φ) {x : G} (hx : x ∈ A) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := (hm.perm.mem_iff x).mp hx
  have hvv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [← hm.perm.map_add, hvv, hm.perm.map_zero]

theorem sec5c3q_A_isElemAb2 (hm : Sec5Model58 t L z r A φ) : IsElemAb2 A 6 :=
  ⟨⟨IsMulCommutative.of_comm fun a b => Subtype.ext (sec5c3q_A_comm hm a.2 b.2),
    fun x hx => by rw [pow_two]; exact sec5c3q_A_sq hm hx⟩, by rw [hm.perm.card_A]; norm_num⟩

theorem sec5c3q_isI4PlusIn_of_wclass_four [Finite G] (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) {x : G} (hx : x ∈ wclass φ 4) : IsI4PlusIn L x := by
  obtain ⟨a, ha, hax⟩ := hm.perm.exists_conj hm.z_mem_wclass hx
  rw [← hax]
  exact sec5_isI4PlusIn_conj hR.pocket (Subgroup.le_normalizer (Subgroup.mem_inf.mp ha).1)

theorem sec5c3q_exists_vec :
    ∀ u : Fin 6 → ZMod 2, vecWeight u = 2 → ∃ v, vecWeight v = 4 ∧ vecWeight (u + v) = 4 := by
  decide +kernel

theorem sec5c3q_exists_pair [Finite G] (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    ∃ w ∈ A, IsI4PlusIn L w ∧ IsI4PlusIn L (t * z * w) := by
  obtain ⟨u, hu, hut⟩ := hm.tz_mem_wclass
  obtain ⟨v, hv4, huv4⟩ := sec5c3q_exists_vec u hu
  refine ⟨φ v, hm.perm.mem v, sec5c3q_isI4PlusIn_of_wclass_four hR hm ⟨v, hv4, rfl⟩, ?_⟩
  have h : t * z * φ v = φ (u + v) := by rw [hm.perm.map_add, hut]
  rw [h]
  exact sec5c3q_isI4PlusIn_of_wclass_four hR hm ⟨u + v, huv4, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
