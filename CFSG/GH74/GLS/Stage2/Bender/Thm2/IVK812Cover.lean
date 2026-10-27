module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Perm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

section Generic

variable {X Y : Type*} [Group X] [Group Y] [Finite X]

theorem eq_bot_of_le_ker {ρ : X →* Y} (hker2 : Nat.card ρ.ker = 2) {W : Subgroup X}
    (hW : IsPGroup 3 ↥W) (hle : W ≤ ρ.ker) : W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hdvd : Nat.card ↥W ∣ Nat.card ρ.ker := Subgroup.card_dvd_of_le hle
  rw [hn, hker2] at hdvd
  have hn0 : n = 0 := by
    by_contra h
    have h1 : 3 ≤ 3 ^ n := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero h)
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [← Subgroup.card_eq_one, hn, hn0]
  rfl

theorem ker_inf_eq_bot {ρ : X →* Y} (hker2 : Nat.card ρ.ker = 2) {W : Subgroup X}
    (hW : IsPGroup 3 ↥W) : ρ.ker ⊓ W = ⊥ :=
  eq_bot_of_le_ker hker2 (hW.to_le inf_le_right) inf_le_left

theorem card_map_of_isPGroup {ρ : X →* Y} (hker2 : Nat.card ρ.ker = 2) {W : Subgroup X}
    (hW : IsPGroup 3 ↥W) : Nat.card ↥(W.map ρ) = Nat.card ↥W := by
  rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, ker_inf_eq_bot hker2 hW,
    Subgroup.relIndex_bot_left]

theorem map_ne_bot {ρ : X →* Y} (hker2 : Nat.card ρ.ker = 2) {W : Subgroup X}
    (hW : IsPGroup 3 ↥W) (h1 : W ≠ ⊥) : W.map ρ ≠ ⊥ := fun h =>
  h1 (eq_bot_of_le_ker hker2 hW ((Subgroup.map_eq_bot_iff W).1 h))

omit [Finite X] in
theorem le_of_map_eq {ρ : X →* Y} (hker : ρ.ker ≤ center X) (hker2 : Nat.card ρ.ker = 2)
    {W W' : Subgroup X} (hW : IsPGroup 3 ↥W) (hW' : IsPGroup 3 ↥W')
    (h : W.map ρ = W'.map ρ) : W ≤ W' := by
  intro x hx
  have hxm : ρ x ∈ W'.map ρ := h ▸ Subgroup.mem_map_of_mem ρ hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxm
  have hz : y⁻¹ * x ∈ ρ.ker := by simp [MonoidHom.mem_ker, map_mul, hyx]
  have hzc : y⁻¹ * x ∈ center X := hker hz
  have hz2 : (y⁻¹ * x) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ρ.ker) (x := ⟨y⁻¹ * x, hz⟩)
    rw [hker2] at this
    simpa [Subgroup.coe_pow] using congrArg Subtype.val this
  obtain ⟨k, hk⟩ := hW ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hW' ⟨y, hy⟩
  have hxk : x ^ (3 ^ k) = 1 := by simpa [Subgroup.coe_pow] using congrArg Subtype.val hk
  have hyl : y ^ (3 ^ l) = 1 := by simpa [Subgroup.coe_pow] using congrArg Subtype.val hl
  have hxm' : x ^ (3 ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hxk, one_pow]
  have hym' : y ^ (3 ^ (k + l)) = 1 := by rw [add_comm, pow_add, pow_mul, hyl, one_pow]
  have hxeq : x = y * (y⁻¹ * x) := by simp
  have hcomm : Commute y (y⁻¹ * x) := by
    exact Subgroup.mem_center_iff.1 hzc y
  have hzm : (y⁻¹ * x) ^ (3 ^ (k + l)) = 1 := by
    have h3 : (y * (y⁻¹ * x)) ^ (3 ^ (k + l)) = y ^ (3 ^ (k + l)) * (y⁻¹ * x) ^ (3 ^ (k + l)) :=
      hcomm.mul_pow _
    rw [← hxeq, hxm', hym', one_mul] at h3
    exact h3.symm
  obtain ⟨j, hj⟩ : Odd (3 ^ (k + l)) := Odd.pow (by decide)
  have hz1 : y⁻¹ * x = 1 := by
    have : (y⁻¹ * x) ^ (3 ^ (k + l)) = y⁻¹ * x := by
      rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [← this]
    exact hzm
  have : x = y := by
    have := congrArg (fun t => y * t) hz1
    simpa using this
  rw [this]
  exact hy

end Generic

variable {X : Type*} [Group X] [Finite X]

theorem card_map_eq_two_pow_seven (ρ : X →* Perm (Fin 11))
    (hrange : ρ.range ≤ alternatingGroup (Fin 11)) (hker2 : Nat.card ρ.ker = 2) {A : Subgroup X}
    (hA : Nat.card ↥A = 2 ^ 8) : Nat.card ↥(A.map ρ) = 2 ^ 7 := by
  have hTA : A.map ρ ≤ alternatingGroup (Fin 11) := (Subgroup.map_le_range ρ A).trans hrange
  have hup : Nat.card ↥(A.map ρ) ≤ 2 ^ 7 := by
    have h1 : Nat.card ↥(A.map ρ) ∣ 2 ^ 8 := hA ▸ Subgroup.card_map_dvd A ρ
    have h2 : Nat.card ↥(A.map ρ) ∣ 19958400 :=
      card_alternatingGroup_eleven ▸ Subgroup.card_dvd_of_le hTA
    have h3 : Nat.card ↥(A.map ρ) ∣ Nat.gcd (2 ^ 8) 19958400 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd (2 ^ 8) 19958400 = 2 ^ 7 := by norm_num
    rw [h4] at h3
    exact Nat.le_of_dvd (by positivity) h3
  have hlow : 2 ^ 7 ≤ Nat.card ↥(A.map ρ) := by
    have hmul := Subgroup.card_ker_mul_card_of_surjective (ρ.subgroupMap_surjective A)
    rw [hA] at hmul
    have hinj : Nat.card (ρ.subgroupMap A).ker ≤ Nat.card ρ.ker := by
      refine Nat.card_le_card_of_injective
        (fun k => (⟨((k : A) : X), ?_⟩ : ρ.ker)) ?_
      · have hk := k.2
        rw [MonoidHom.mem_ker] at hk ⊢
        simpa using congrArg Subtype.val hk
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        simpa using congrArg Subtype.val hab
    rw [hker2] at hinj
    nlinarith
  exact le_antisymm hup hlow

theorem cover_unique (ρ : X →* Perm (Fin 11)) (hrange : ρ.range ≤ alternatingGroup (Fin 11))
    (hker : ρ.ker ≤ center X) (hker2 : Nat.card ρ.ker = 2) {A : Subgroup X}
    (hA : Nat.card ↥A = 2 ^ 8) {W W' : Subgroup X} (hW : IsPGroup 3 ↥W) (hW' : IsPGroup 3 ↥W')
    (h1 : W ≠ ⊥) (h1' : W' ≠ ⊥) (hn : A ≤ normalizer (W : Set X))
    (hn' : A ≤ normalizer (W' : Set X)) : W = W' ∧ Nat.card ↥W = 3 := by
  have hTA : A.map ρ ≤ alternatingGroup (Fin 11) := (Subgroup.map_le_range ρ A).trans hrange
  have hT := card_map_eq_two_pow_seven ρ hrange hker2 hA
  have hnorm : ∀ {U : Subgroup X}, A ≤ normalizer (U : Set X) →
      A.map ρ ≤ normalizer ((U.map ρ : Subgroup (Perm (Fin 11))) : Set (Perm (Fin 11))) :=
    fun hU => (Subgroup.map_mono hU).trans (Subgroup.le_normalizer_map ρ)
  obtain ⟨hVV, hV3⟩ := three_sub_unique hTA hT (hW.map ρ) (hW'.map ρ)
    ((Subgroup.map_le_range ρ W).trans hrange) ((Subgroup.map_le_range ρ W').trans hrange)
    (map_ne_bot hker2 hW h1) (map_ne_bot hker2 hW' h1') (hnorm hn) (hnorm hn')
  refine ⟨le_antisymm (le_of_map_eq hker hker2 hW hW' hVV)
    (le_of_map_eq hker hker2 hW' hW hVV.symm), ?_⟩
  rw [← card_map_of_isPGroup hker2 hW]
  exact hV3

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
