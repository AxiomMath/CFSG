module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenWreath

open CFSG.RankThree.PartTwo.Sec4.Item434Kit Subgroup

variable {H : Type*} [Group H] {z : Fin 3 → H} {t : H}

theorem commute_vecElt (hf : WreathFacts z t) (v w : Fin 3 → ZMod 3) :
    Commute (vecElt z v) (vecElt z w) := by
  change vecElt z v * vecElt z w = vecElt z w * vecElt z v
  rw [← vecElt_add hf, ← vecElt_add hf, add_comm]

theorem commute_vecElt_z (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) (i : Fin 3) :
    Commute (vecElt z v) (z i) := by
  have h := commute_vecElt hf v (Pi.single i 1)
  rwa [vecElt_single_one] at h

theorem zpow_vecElt (hf : WreathFacts z t) (w : Fin 3 → ZMod 3) (m : ℤ) :
    vecElt z w ^ m = vecElt z (m • w) := by
  have h := map_zpow (vecHom hf) (Multiplicative.ofAdd w) m
  rw [vecHom_apply, vecHom_apply] at h
  simp only [toAdd_zpow, toAdd_ofAdd] at h
  exact h.symm

theorem exists_pow_three_eq_const (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) {j : Fin 3}
    (hj : j ≠ 0) :
    ∃ w : Fin 3 → ZMod 3, w 0 = w 1 ∧ w 1 = w 2 ∧
      (vecElt z v * t ^ (j : ℕ)) ^ 3 = vecElt z w := by
  set a := vecElt z v with ha
  set u := t ^ (j : ℕ) with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, hf.pow_t, one_pow]
  have hnorm : ∀ y ∈ baseA z, u * y * u⁻¹ ∈ baseA z := fun y hy =>
    (mem_normalizer_iff.mp (pow_mem (t_mem_normalizer hf) (j : ℕ)) y).mp hy
  have haA : a ∈ baseA z := vecElt_mem_baseA hf v
  have hx3 : (a * u) ^ 3 = a * (u * a * u⁻¹) * (u * (u * a * u⁻¹) * u⁻¹) := by
    calc (a * u) ^ 3 = a * u * (a * u) * (a * u) := pow_three' _
      _ = a * (u * a * u⁻¹) * (u * (u * a * u⁻¹) * u⁻¹) * u ^ 3 := by group
      _ = _ := by rw [hu3, mul_one]
  have hmem : (a * u) ^ 3 ∈ baseA z := by
    rw [hx3]
    exact mul_mem (mul_mem haA (hnorm a haA)) (hnorm _ (hnorm a haA))
  obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp hmem
  refine ⟨w, ?_⟩
  have hcomm : vecElt z w * u = u * vecElt z w := by
    have h1 : Commute ((a * u) ^ 3) (a * u) := (Commute.refl _).pow_left 3
    have h2 : Commute ((a * u) ^ 3) a := by
      rw [← hw]
      exact commute_vecElt hf w v
    have h3 : Commute ((a * u) ^ 3) (a⁻¹ * (a * u)) := h2.inv_right.mul_right h1
    rw [inv_mul_cancel_left, ← hw] at h3
    exact h3.eq
  obtain ⟨h01, h12⟩ := eq_of_commute hf hj hcomm
  exact ⟨h01, h12, hw.symm⟩

theorem conj_z_zero (hf : WreathFacts z t) {j : Fin 3} (hj : j ≠ 0) :
    t ^ (j : ℕ) * z 0 * (t ^ (j : ℕ))⁻¹ = z j := by
  fin_cases j
  · exact absurd rfl hj
  · simpa using hf.conj0
  · calc t ^ 2 * z 0 * (t ^ 2)⁻¹ = t * (t * z 0 * t⁻¹) * t⁻¹ := by rw [sq]; group
      _ = z 2 := by rw [hf.conj0, hf.conj1]

theorem pow_three_eq_one_of_conj_mem (hf : WreathFacts z t) {x : H} (hx : x ∈ wreathW z t)
    (hc : z 0 * x * (z 0)⁻¹ ∈ zpowers x) : x ^ 3 = 1 := by
  obtain ⟨v, j, rfl⟩ := mem_wreathW hf hx
  by_cases hj : j = 0
  · subst hj
    rw [Fin.val_zero, pow_zero, mul_one]
    exact (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf v)
  by_contra hne
  obtain ⟨w, hw01, hw12, hxw⟩ := exists_pow_three_eq_const hf v hj
  set a := vecElt z v with ha
  set u := t ^ (j : ℕ) with hu
  set x := a * u with hxdef
  have hwc : ∀ i, w i = w 0 := fun i => by
    fin_cases i
    · rfl
    · exact hw01.symm
    · exact hw12.symm.trans hw01.symm
  have hy3 : (x ^ 3) ^ 3 = 1 := by
    rw [hxw]
    exact (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf w)
  have hyo : orderOf (x ^ 3) = 3 := orderOf_eq_prime hy3 hne
  have hconj : u * (z 0)⁻¹ * u⁻¹ = (z j)⁻¹ := by
    rw [← conj_z_zero hf hj, ← hu]
    group
  have hcomm : z 0 * x * (z 0)⁻¹ * x⁻¹ = z 0 * (z j)⁻¹ := by
    calc z 0 * (a * u) * (z 0)⁻¹ * (a * u)⁻¹ = z 0 * a * (u * (z 0)⁻¹ * u⁻¹) * a⁻¹ := by group
      _ = z 0 * (a * (z j)⁻¹ * a⁻¹) := by rw [hconj]; group
      _ = z 0 * (z j)⁻¹ := by
        rw [(commute_vecElt_z hf v j).inv_right.eq, mul_inv_cancel_right]
  have hcz : z 0 * x * (z 0)⁻¹ * x⁻¹ ∈ zpowers x := mul_mem hc (inv_mem (mem_zpowers x))
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hcz
  have hc3 : (z 0 * (z j)⁻¹) ^ 3 = 1 := by
    have hcm : Commute (z 0) (z j)⁻¹ := (show Commute (z 0) (z j) from hf.comm_z 0 j).inv_right
    rw [hcm.mul_pow, hf.pow_z, inv_pow, hf.pow_z, inv_one, one_mul]
  have hn3 : (x ^ 3) ^ n = 1 := by
    have h1 : (x ^ n) ^ 3 = 1 := by rw [hn, hcomm]; exact hc3
    calc (x ^ 3) ^ n = (x ^ n) ^ 3 := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      _ = 1 := h1
  have h3n : (3 : ℤ) ∣ n := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hn3
    rwa [hyo] at h
  obtain ⟨m, rfl⟩ := h3n
  have hzinv : (z j)⁻¹ = z j ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', hf.pow_z]
  have hd : z 0 * (z j)⁻¹ = vecElt z (Pi.single 0 1 + Pi.single j 2) := by
    rw [vecElt_add hf, vecElt_single_one, vecElt_single, hzinv]
    rfl
  have hcm : vecElt z (Pi.single 0 1 + Pi.single j 2) = vecElt z (m • w) := by
    calc vecElt z (Pi.single 0 1 + Pi.single j 2) = z 0 * (z j)⁻¹ := hd.symm
      _ = x ^ (3 * m) := by rw [hn, hcomm]
      _ = (x ^ 3) ^ m := by rw [zpow_mul]; simp only [zpow_ofNat]
      _ = vecElt z (m • w) := by rw [hxw, zpow_vecElt hf]
  have he := congrFun (vecElt_injective hf hcm)
  have h0 := he 0
  have hj' := he j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hj, hj, if_true, if_false,
    hwc j] at h0 hj'
  have h12 : (1 : ZMod 3) + 0 = 0 + 2 := h0.trans hj'.symm
  revert h12
  decide

theorem card_le_three_of_normal_cyclic (hf : WreathFacts z t) {N : Subgroup H}
    (hN : N ≤ wreathW z t) (hnorm : wreathW z t ≤ normalizer (N : Set H)) (hcyc : IsCyclic N) :
    Nat.card N ≤ 3 := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hz0 : z 0 ∈ wreathW z t := (le_sup_left : baseA z ≤ wreathW z t) (z_mem_baseA 0)
  have hconj : z 0 * (g : H) * (z 0)⁻¹ ∈ zpowers (g : H) := by
    have h1 : z 0 * (g : H) * (z 0)⁻¹ ∈ N := (mem_normalizer_iff.mp (hnorm hz0) g).mp g.2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨_, h1⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hx3 : (g : H) ^ 3 = 1 := pow_three_eq_one_of_conj_mem hf (hN g.2) hconj
  have hg3 : g ^ 3 = 1 := Subtype.ext hx3
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_le_of_pow_eq_one (by norm_num) hg3

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenWreath
