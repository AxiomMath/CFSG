module

public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Complement

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.suzuki_normal_two_complement
    {n e : ℕ} (h : BenderType K n 2 e)
    {J U Y : Subgroup K} (hUJ : U ≤ J) (hYJ : Y ≤ J) (hJ : J = U ⊔ Y)
    (hUn : ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U) (hU1 : U ≠ ⊥) (hUsq : ∀ u ∈ U, u * u = 1)
    (hY : Odd (Nat.card Y)) :
    IsCyclic Y ∧ Nat.card Y ∣ 2 ^ n - 1 ∧
      (∀ y ∈ Y, y ≠ 1 → centralizer ({y} : Set K) ⊓ J = Y) ∧
      (∀ x ∈ U, x ≠ 1 → centralizer ({x} : Set K) ⊓ J = U) := by
  classical
  have he : e = 1 := h.e_eq_one_of_two
  subst he
  have hU2 : IsPGroup 2 U := isPGroup_two_of_sq_eq_one hUsq
  obtain ⟨Q, hUQ⟩ := hU2.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hJN : J ≤ normalizer (U : Set K) := le_normalizer_of_forall_conj_mem hUn
  have hJQ : J ≤ borel (Q : Subgroup K) :=
    hJN.trans (IsStronglyEmbedded.normalizer_le hc.strong (hUQ.trans (le_borel _)) hU2 hU1)
  have hYM : Y ≤ borel (Q : Subgroup K) := hYJ.trans hJQ
  obtain ⟨q', hq'Q, hq'⟩ := hc.exists_conj_cartan_of_odd Q.isPGroup' hYM hY
  have hYD : Y.map (MulAut.conj q').toMonoidHom ≤ cartan (Q : Subgroup K) t := by
    rintro _ ⟨y, hy, rfl⟩
    exact hq' y hy
  have hYcyc : IsCyclic Y :=
    ((Subgroup.equivMapOfInjective Y (MulAut.conj q').toMonoidHom
      (MulAut.conj q').injective).isCyclic).mpr (isCyclic_of_le_isCyclic hc.isCyclic hYD)
  refine ⟨hYcyc, ?_, ?_, ?_⟩
  · have h1 : Nat.card Y = Nat.card (Y.map (MulAut.conj q').toMonoidHom) :=
      (Subgroup.card_map_of_injective (MulAut.conj q').injective).symm
    rw [h1]
    have := Subgroup.card_dvd_of_le hYD
    rwa [hc.card_cartan, mul_one] at this
  · intro y hy hy1
    have hy'D : q' * y * q'⁻¹ ∈ cartan (Q : Subgroup K) t := hq' y hy
    have hy'1 : q' * y * q'⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      have : y = q'⁻¹ * (q' * y * q'⁻¹) * q' := by group
      rw [this, h1]
      group
    have hcen := hc.centralizer_cartan_eq Q.isPGroup' hy'D hy'1
    apply le_antisymm
    · rintro j ⟨hjc, hjJ⟩
      have hjUY : j ∈ U ⊔ Y := hJ ▸ hjJ
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left U Y
        (fun y₁ hy₁ => by
          have := hJN (hYJ hy₁)
          exact this)
      have hmem : j ∈ ((U ⊔ Y : Subgroup K) : Set K) := hjUY
      rw [hset] at hmem
      obtain ⟨u, hu, y₁, hy₁, rfl⟩ := Set.mem_mul.mp hmem
      have hjc' : q' * (u * y₁) * q'⁻¹ ∈ centralizer ({q' * y * q'⁻¹} : Set K) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hjc
        calc q' * (u * y₁) * q'⁻¹ * (q' * y * q'⁻¹) = q' * ((u * y₁) * y) * q'⁻¹ := by group
          _ = q' * (y * (u * y₁)) * q'⁻¹ := by rw [h1]
          _ = q' * y * q'⁻¹ * (q' * (u * y₁) * q'⁻¹) := by group
      rw [hcen] at hjc'
      have hy₁'D : q' * y₁ * q'⁻¹ ∈ cartan (Q : Subgroup K) t := hq' y₁ hy₁
      have hu'Q : q' * u * q'⁻¹ ∈ (Q : Subgroup K) :=
        Q.mul_mem (Q.mul_mem hq'Q (hUQ hu)) (Q.inv_mem hq'Q)
      have hu'D : q' * u * q'⁻¹ ∈ cartan (Q : Subgroup K) t := by
        have h1 := (cartan (Q : Subgroup K) t).mul_mem hjc'
          ((cartan (Q : Subgroup K) t).inv_mem hy₁'D)
        have h2 : q' * u * q'⁻¹ = q' * (u * y₁) * q'⁻¹ * (q' * y₁ * q'⁻¹)⁻¹ := by group
        rw [h2]
        exact h1
      have hu'1 : q' * u * q'⁻¹ = 1 := by
        have : q' * u * q'⁻¹ ∈ (Q : Subgroup K) ⊓ cartan (Q : Subgroup K) t := ⟨hu'Q, hu'D⟩
        rw [hc.inf_eq, Subgroup.mem_bot] at this
        exact this
      have hu1 : u = 1 := by
        have : u = q'⁻¹ * (q' * u * q'⁻¹) * q' := by group
        rw [this, hu'1]
        group
      rw [hu1, one_mul]
      exact hy₁
    · intro j hj
      refine Subgroup.mem_inf.mpr ⟨?_, hYJ hj⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := (IsMulCommutative.is_comm (M := ↥Y)).comm ⟨j, hj⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
  · intro x hx hx1
    have hxQ : x ∈ (Q : Subgroup K) := hUQ hx
    have hxr : x ∈ rootCenter (Q : Subgroup K) := hc.mem_rootCenter_of_mul_self hxQ (hUsq x hx)
    have hcen := hc.centralizer_eq_of_e_one hxr hx1
    rw [hcen]
    apply le_antisymm
    · rintro j ⟨hjQ, hjJ⟩
      have hjUY : j ∈ U ⊔ Y := hJ ▸ hjJ
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left U Y
        (fun y₁ hy₁ => by
          have := hJN (hYJ hy₁)
          exact this)
      have hmem : j ∈ ((U ⊔ Y : Subgroup K) : Set K) := hjUY
      rw [hset] at hmem
      obtain ⟨u, hu, y₁, hy₁, rfl⟩ := Set.mem_mul.mp hmem
      have hy₁Q : y₁ ∈ (Q : Subgroup K) := by
        have := Q.mul_mem (Q.inv_mem (hUQ hu)) hjQ
        simpa using this
      have hy₁1 : y₁ = 1 := eq_one_of_isPGroup_two_of_odd Q.isPGroup' hY hy₁Q hy₁
      rw [hy₁1, mul_one]
      exact hu
    · intro u hu
      exact ⟨hUQ hu, hUJ hu⟩

end Complement

section Eight

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.suzuki_eight_solvable_card
    {e : ℕ} (h : BenderType K 3 2 e) {J : Subgroup K}
    [Group.IsSolvable J] (h7 : 7 ∣ Nat.card J) (h2 : 2 ∣ Nat.card J) (h4 : ¬ 4 ∣ Nat.card J) :
    Nat.card J = 14 := by
  classical
  have he : e = 1 := h.e_eq_one_of_two
  subst he
  have hJ1 : J ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h7
    omega
  obtain ⟨m, hm⟩ := h7
  rcases h.suzuki_solvable_subgroup hJ1 with ⟨Q, hJQ⟩ | ⟨x, hx1, hxodd, hJN⟩
  · obtain ⟨t, hc⟩ := h.exists_benderCore Q
    have hdvd : Nat.card J ∣ Nat.card (borel (Q : Subgroup K)) := Subgroup.card_dvd_of_le hJQ
    rw [hc.card_borel] at hdvd
    norm_num at hdvd
    have hm64 : m ∣ 64 := by
      rw [hm] at hdvd
      have : 7 * m ∣ 7 * 64 := by simpa using hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hm64' : m ≤ 64 := Nat.le_of_dvd (by norm_num) hm64
    interval_cases m <;> omega
  · obtain ⟨-, -, hTcard, hNcard⟩ := h.suzuki_odd_centralizer hx1 hxodd
    have hdvd : Nat.card J ∣
        Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) :=
      Subgroup.card_dvd_of_le hJN
    have hT : Nat.card (centralizer ({x} : Set K)) = 7 ∨ Nat.card (centralizer ({x} : Set K)) = 5 ∨
        Nat.card (centralizer ({x} : Set K)) = 13 := by
      rcases hTcard with h1 | ⟨a, hn, h2 | h3⟩
      · left
        rw [h1]
        norm_num
      · have ha : a = 1 := by omega
        subst ha
        right
        left
        rw [h2]
        norm_num
      · have ha : a = 1 := by omega
        subst ha
        right
        right
        rw [h3]
        norm_num
    have hpos : 0 < Nat.card J := Nat.card_pos
    have h7N : 7 ∣ Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) :=
      (Dvd.intro _ hm.symm).trans hdvd
    have hleN := Nat.le_of_dvd Nat.card_pos hdvd
    rcases hNcard with h1 | h1 <;> rcases hT with h3 | h3 | h3 <;> rw [h1, h3] at h7N hleN <;>
      omega

end Eight

end CFSG.GH74.Uniqueness.Bender
