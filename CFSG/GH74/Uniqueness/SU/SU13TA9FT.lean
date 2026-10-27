module

public import CFSG.GH74.Uniqueness.SU.SU13TA9F
public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem card_centralizer_s₁ (hπ : TwoCover π) (c : Cfg π) :
    Nat.card ↥(centralizer ({c.s₁} : Set H)) = 2160 := by
  rw [hπ.card_centralizer_singleton (odd_orderOf_s₁ c), c.π_s₁, card_centralizer_ec]

theorem card_T (hπ : TwoCover π) {T : Subgroup H} (hT : IsSylowIn (Fh π) T) :
    Nat.card T = 16 := by
  have := hπ.finite'
  obtain ⟨-, k, m, hk, ⟨j, hj⟩, hm⟩ := (isSylowIn_iff_card).mp hT
  rw [card_Fh hπ, hj] at hm
  have hdvd : 2 ^ k ∣ 720 := ⟨2 * j + 1, hm⟩
  have hle : 2 ^ k ≤ 720 := Nat.le_of_dvd (by norm_num) hdvd
  have hk12 : k ≤ 12 := by
    by_contra hcon
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk]
  interval_cases k <;> omega

theorem mem_T (hπ : TwoCover π) {T : Subgroup H} (hT : IsSylowIn (Fh π) T) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) : z ∈ T := by
  have := hπ.finite'
  by_contra hzT
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  have hzc : ∀ g : H, Commute g z := fun g => Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) g
  have hdisj : Disjoint T (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    rw [zpow_eq_zpow_emod k (show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2)] at hxT ⊢
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk with hk | hk
    · rw [hk]; exact zpow_zero z
    · rw [hk] at hxT
      exact absurd (by simpa using hxT) hzT
  have hcard : Nat.card ↥(T ⊔ zpowers z) = 32 := by
    rw [card_sup_of_commute (fun x _ y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hzc x).zpow_right k) hdisj, card_T hπ hT, Nat.card_zpowers,
      orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) hz2 hz1]
  have hle : T ⊔ zpowers z ≤ Fh π := sup_le hT.le (by
    rw [Subgroup.zpowers_le]
    exact ker_le_Fh hz)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard, card_Fh hπ] at hdvd
  omega

theorem eq_of_orderOf_eq_two_T (hπ : TwoCover π) {T : Subgroup H} (hT : IsSylowIn (Fh π) T)
    {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) {y : H} (hy : y ∈ T) (hy2 : orderOf y = 2) : y = z := by
  have hy2' : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
  have hyF : π y ∈ AS := hT.le hy
  by_cases hπy : π y = 1
  · exact hπ.eq_of_mem_ker_ne_one' hπy hz hy1 hz1
  · exfalso
    have hsq : (π y) ^ 2 = 1 := by rw [← map_pow, hy2', map_one]
    exact (hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := y)
      (cycleType_eq_of_sq_eq_one_of_mem_AS hyF hsq hπy)).2 hy2'

theorem not_isCyclic_T (hπ : TwoCover π) {T : Subgroup H} (hT : IsSylowIn (Fh π) T) {z : H}
    (hz : z ∈ π.ker) (hz1 : z ≠ 1) : ¬ IsCyclic ↥T := by
  have := hπ.finite'
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
  have hord : orderOf (g : H) = 16 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, card_T hπ hT]
  set y : H := (g : H) with hy
  have hyT : y ∈ T := g.2
  have hy8T : y ^ 8 ∈ T := T.pow_mem hyT 8
  have hy8ord : orderOf (y ^ 8) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; norm_num), hord]
  have hy8 : y ^ 8 = z := eq_of_orderOf_eq_two_T hπ hT hz hz1 hy8T hy8ord
  have hπ8 : (π y) ^ 8 = 1 := by rw [← map_pow, hy8]; exact MonoidHom.mem_ker.mp hz
  have hπ4 : (π y) ^ 4 = 1 := pow_four_eq_one_of_pow_eight_of_mem_AS (hT.le hyT) hπ8
  have hy4k : y ^ 4 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hπ4]
  have hy41 : y ^ 4 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have hy4z : y ^ 4 = z := hπ.eq_of_mem_ker_ne_one' hy4k hz hy41 hz1
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  apply hz1
  rw [← hy8, show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hy4z, hz2]

theorem exists_T (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    ∃ T : Subgroup H, IsSylowIn (centralizer ({c.s₁} : Set H) ⊓ centralizer ({z} : Set H)) T ∧
      z ∈ T ∧ (∀ y ∈ T, orderOf y = 2 → y = z) ∧
      ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥T ≃* QuaternionGroup (2 ^ k)) := by
  have := hπ.finite'
  obtain ⟨T, hT⟩ := exists_isSylowIn (Fh π)
  have hzcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzcen g)
  have hTle : T ≤ centralizer ({c.s₁} : Set H) ⊓ centralizer ({z} : Set H) := by
    rw [hzz, inf_top_eq, centralizer_s₁_eq hπ c]
    exact hT.le.trans le_sup_right
  have huniq := fun y (hy : y ∈ T) (hy2 : orderOf y = 2) => eq_of_orderOf_eq_two_T hπ hT hz hz1 hy hy2
  refine ⟨T, ?_, mem_T hπ hT hz hz1, huniq, ?_⟩
  · refine (isSylowIn_iff_card).mpr ⟨hTle, 4, 135, by rw [card_T hπ hT]; norm_num, by decide, ?_⟩
    rw [hzz, inf_top_eq, card_centralizer_s₁ hπ c]
    norm_num
  · have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥T :=
      fun a b _ => Subtype.ext (Subtype.ext
        ((huniq a.1.1 a.1.2 (by rw [Subgroup.orderOf_coe]; exact a.2)).trans
          (huniq b.1.1 b.1.2 (by rw [Subgroup.orderOf_coe]; exact b.2)).symm))
    rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion
      hT.isPGroup hrank with hcyc | ⟨k, hk, ⟨e⟩⟩
    · exact absurd hcyc (not_isCyclic_T hπ hT hz hz1)
    · exact ⟨k, hk, ⟨e.symm⟩⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
