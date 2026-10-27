module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic CFSG.Sporadic.Schreier CFSG.ClassicalInvolution.Asc77

variable {n : ℕ}

theorem q8_comm_or_inv : ∀ a b : QuaternionGroup 2, a * a ≠ 1 →
    b * a = a * b ∨ b * a * b⁻¹ = a⁻¹ := by
  decide

theorem comm_or_inv_of_q8 {G : Type*} [Group G] {K : Subgroup G} (e : ↥K ≃* QuaternionGroup 2)
    {u y : G} (hu : u ∈ K) (hy : y ∈ K) (hu2 : u * u ≠ 1) :
    y * u = u * y ∨ y * u * y⁻¹ = u⁻¹ := by
  have h1 : e ⟨u, hu⟩ * e ⟨u, hu⟩ ≠ 1 := by
    rw [← map_mul, ← map_one e]
    intro h
    exact hu2 (congrArg Subtype.val (e.injective h))
  rcases q8_comm_or_inv _ (e ⟨y, hy⟩) h1 with h | h
  · left
    have h2 : e (⟨y, hy⟩ * ⟨u, hu⟩) = e (⟨u, hu⟩ * ⟨y, hy⟩) := by rw [map_mul, map_mul, h]
    exact congrArg Subtype.val (e.injective h2)
  · right
    have h2 : e (⟨y, hy⟩ * ⟨u, hu⟩ * (⟨y, hy⟩ : K)⁻¹) = e (⟨u, hu⟩ : K)⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, h]
    exact congrArg Subtype.val (e.injective h2)

theorem eq_of_identSqCheck {H K : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    (hd : Vtx.AmbientQuatDatum H K r) {S W : List (Equiv.Perm (Fin n))}
    {Ls : List (List (Equiv.Perm (Fin n)))} (hc : identSqCheck r S W Ls = true)
    (hS : ∀ u ∈ H, u * u = r → u ∈ S) (hW : ∀ c ∈ W, c ∈ H ∧ c * r = r * c) :
    ∃ L ∈ Ls, ∀ x, x ∈ K ↔ x ∈ L := by
  obtain ⟨e⟩ := hd.q8
  set ρ : Equiv.Perm (Fin n) := ((e.symm (QuaternionGroup.a 1) : K) : Equiv.Perm (Fin n))
    with hρ
  have hρK : ρ ∈ K := (e.symm (QuaternionGroup.a 1)).2
  have hρ4 : orderOf ρ = 4 := by
    rw [hρ, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hρne : ρ * ρ ≠ 1 := fun h1 => by
    have h2 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hρ4] at h2
    norm_num at h2
  have hρr : ρ * ρ = r := by
    have h4 : ρ ^ 4 = 1 := hρ4 ▸ pow_orderOf_eq_one ρ
    have hsq : ρ * ρ * (ρ * ρ) = 1 := by
      rw [← h4]
      simp [pow_succ, mul_assoc]
    exact (hd.inv.unique _ (K.mul_mem hρK hρK) hsq).resolve_left hρne
  obtain ⟨j, hjK, hjj, hjρ, hKT⟩ := exists_q8_gen e hρK hρne
  rw [hρr] at hjj hKT
  simp only [identSqCheck, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hc
  rcases hc ρ (hS ρ (hd.le hρK) hρr) with ⟨w, hwW, hbad⟩ | hall
  · exfalso
    obtain ⟨hwH, hwr⟩ := hW w hwW
    simp only [badWit, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hbad
    obtain ⟨hb1, hb2⟩ := hbad
    rcases hd.twins w hwH hwr with h1 | h1
    · have hy : w * ρ * w⁻¹ ∈ K := by
        rw [← h1]
        exact conj_mem_conjSub hρK
      rcases comm_or_inv_of_q8 e hρK hy hρne with h | h
      · exact hb1 h
      · exact hb2 h
    · exact hb1 (h1 ρ hρK _ (conj_mem_conjSub hρK)).symm
  · rcases hall j (hS j (hd.le hjK) hjj) with hnot | ⟨L, hL, hsL⟩ | ⟨c, hcW, hv⟩
    · exact absurd hjρ hnot
    · exact ⟨L, hL, fun x => (hKT x).trans (sameSet_spec hsL x)⟩
    · exfalso
      obtain ⟨hcH, hcr⟩ := hW c hcW
      obtain ⟨⟨x, hxT, hxc⟩, a, ha, b, hb, hab⟩ := violates_spec hv
      rcases hd.twins c hcH hcr with h1 | h1
      · apply hxc
        rw [← hKT, ← h1]
        exact conj_mem_conjSub ((hKT x).mpr hxT)
      · have haK : a ∈ K := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact hρK
          · exact hjK
        have hbK : b ∈ conjSub c K := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact conj_mem_conjSub hρK
          · exact conj_mem_conjSub hjK
        exact hab (h1 a haK b hbK)

end CFSG.ClassicalInvolution.Q3.TL4.E4C
