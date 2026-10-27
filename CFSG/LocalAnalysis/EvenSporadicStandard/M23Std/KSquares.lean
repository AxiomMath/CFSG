module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {F : Subgroup G}

theorem sq_mem_F [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) {k : G}
    (hk : k ∈ Ksub z F) : k * k ∈ F := by
  have hkk : k * k ∈ Ksub z F := Subgroup.mul_mem _ hk hk
  have hphi : phiv z (k * k) = 1 := by
    rw [phiv_mul h D hk hk]
    exact D.F_sq _ (phiv_mem h D hk)
  have hE := (phiv_eq_one_iff h D hkk).1 hphi
  obtain ⟨f, hf, b, hb, hfb⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) hE
  rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
  · rw [hfb, hb1, mul_one]
    exact hf
  · exfalso
    rw [hbz] at hfb
    apply h.not_isConj_of_sq ⟨k, rfl⟩
    rw [hfb, ← h.z_comm f (D.F_le hf)]
    exact isConj_z_mul h hZ D hf

end CFSG.EvenSporadicStandard.M23Std
