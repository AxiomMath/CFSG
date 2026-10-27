module

public import CFSG.Quasithin.Background.B19Block
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] {X : Type*} [Group X]

private theorem eq_one_of_mul_self_of_odd [Finite X] {y : X} (hy : Odd (orderOf y))
    (h2 : y * y = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hy
    exact absurd hy (by decide)

theorem exists_inverted_of_transvection [Finite V] [Finite X] (hV : ∀ v : V, v * v = 1)
    {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d : X} (hd : IsTransvection (ρ d))
    {K : Subgroup X} (hK : Odd (Nat.card K)) (hdK : ∀ k ∈ K, d * k * d⁻¹ ∈ K) :
    ∃ x ∈ K, x ^ 3 = 1 ∧ d * x * d⁻¹ = x⁻¹ ∧ ⁅K, Subgroup.zpowers d⁆ = Subgroup.zpowers x ∧
      ∀ y ∈ K, d * y * d⁻¹ = y⁻¹ → y ∈ Subgroup.zpowers x := by
  classical
  have hoddK : ∀ y ∈ K, Odd (orderOf y) := fun y hy => by
    have := Subgroup.orderOf_dvd_natCard K hy
    exact hK.of_dvd_nat this
  by_cases hc : ∀ k ∈ K, k * d = d * k
  · refine ⟨1, K.one_mem, one_pow 3, by group, ?_, ?_⟩
    · rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (hc k hk).symm n)).eq
    · intro y hy hyd
      have hyy : y = y⁻¹ := by
        rw [← hyd, ← hc y hy, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : y * y = 1 := by
        calc y * y = y * y⁻¹ := by rw [← hyy]
          _ = 1 := mul_inv_cancel y
      rw [eq_one_of_mul_self_of_odd (hoddK y hy) h2]
      exact Subgroup.one_mem _
  · push Not at hc
    obtain ⟨k₀, hk₀, hk₀d⟩ := hc
    obtain ⟨ht1, w, htw⟩ := hd
    have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
    set Φ : Subgroup (MulAut V) := K.map ρ with hΦ
    have hΦodd : Odd (Nat.card Φ) := by
      rw [hΦ, Subgroup.card_map_of_injective hρ]
      exact hK
    haveI : Group.IsSolvable Φ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hΦodd
    have htΦ : ∀ f ∈ Φ, ρ d * f * (ρ d)⁻¹ ∈ Φ := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨d * k * d⁻¹, hdK k hk, by simp [map_mul, map_inv]⟩
    have hnt : ∃ f ∈ Φ, f * ρ d ≠ ρ d * f := by
      refine ⟨ρ k₀, ⟨k₀, hk₀, rfl⟩, fun h => hk₀d (hρ ?_)⟩
      rw [map_mul, map_mul]
      exact h
    obtain ⟨x', hB⟩ := B19.exists_tvBlock hV' hΦodd htw ht1 htΦ hnt
    obtain ⟨x, hx, rfl⟩ := hB.mem
    refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
    · apply hρ
      rw [map_pow, hB.x3, map_one]
    · apply hρ
      rw [map_mul, map_mul, map_inv, map_inv, hB.inv]
    · apply Subgroup.map_injective hρ
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      exact hB.comm_eq
    · intro y hy hyd
      have h1 : ρ y ∈ Subgroup.zpowers (ρ x) := hB.inverted (ρ y) ⟨y, hy, rfl⟩ (by
        rw [← map_inv, ← map_mul, ← map_mul, hyd, map_inv])
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, hρ (by rw [map_zpow, hn])⟩

private theorem moves_mem_closure {ρ : X →* MulAut V} {d : X} {w : V}
    (htw : IsTransvectionWith (ρ d) w) {a : X}
    (ha : a ∈ Subgroup.normalClosure ({d} : Set X)) (v : V) :
    ρ a v * v⁻¹ ∈ Subgroup.closure (Set.range fun g : X => ρ g w) := by
  set W := Subgroup.closure (Set.range fun g : X => ρ g w)
  revert v
  refine Subgroup.closure_induction (p := fun a _ => ∀ v : V, ρ a v * v⁻¹ ∈ W) ?_ ?_ ?_ ?_ ha
  · intro c hc v
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hconj
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hct := B1.tv_conj htw (ρ g)
    have hρc : ρ (g * d * g⁻¹) = ρ g * ρ d * (ρ g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rcases hct.2 v with h | h
    · rw [hρc, h, mul_inv_cancel]
      exact W.one_mem
    · rw [hρc, h, mul_comm v, mul_inv_cancel_right]
      exact Subgroup.subset_closure ⟨g, rfl⟩
  · intro v
    rw [map_one, MulAut.one_apply, mul_inv_cancel]
    exact W.one_mem
  · intro a b _ _ ha hb v
    have e : ρ (a * b) v * v⁻¹ = (ρ a (ρ b v) * (ρ b v)⁻¹) * (ρ b v * v⁻¹) := by
      rw [map_mul, MulAut.mul_apply]
      group
    rw [e]
    exact W.mul_mem (ha _) (hb v)
  · intro a _ ha v
    have e : ρ a⁻¹ v * v⁻¹ = (ρ a (ρ a⁻¹ v) * (ρ a⁻¹ v)⁻¹)⁻¹ := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      group
    rw [e]
    exact W.inv_mem (ha _)

theorem eq_one_of_mem_normalClosure_of_commute [Finite X] (hV : ∀ v : V, v * v = 1)
    {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d : X} (hd : IsTransvection (ρ d))
    {z : X} (hz : z ∈ Subgroup.normalClosure ({d} : Set X))
    (hzc : ∀ a ∈ Subgroup.normalClosure ({d} : Set X), a * z = z * a)
    (hodd : Odd (orderOf z)) : z = 1 := by
  obtain ⟨ht1, w, htw⟩ := hd
  set W := Subgroup.closure (Set.range fun g : X => ρ g w) with hWdef
  have hfix : ∀ g : X, ρ z (ρ g w) = ρ g w := by
    intro g
    have hmem : g * d * g⁻¹ ∈ Subgroup.normalClosure ({d} : Set X) :=
      Subgroup.conjugatesOfSet_subset_normalClosure
        (Group.mem_conjugatesOfSet_iff.mpr ⟨d, rfl, isConj_iff.mpr ⟨g, rfl⟩⟩)
    have hcomm : ρ z * (ρ g * ρ d * (ρ g)⁻¹) = (ρ g * ρ d * (ρ g)⁻¹) * ρ z := by
      have := congrArg ρ (hzc _ hmem)
      simp only [map_mul, map_inv] at this
      exact this.symm
    exact B1.tv_comm_centre (B1.tv_conj htw (ρ g)) (B1.tv_conj_ne_one ht1 (ρ g)) hcomm
  have hfixW : ∀ c ∈ W, ρ z c = c := by
    intro c hc
    refine Subgroup.closure_induction (p := fun c _ => ρ z c = c) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨g, rfl⟩
      exact hfix g
    · exact map_one _
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
    · intro a _ ha
      rw [map_inv, ha]
  have hρz : ρ z = 1 := by
    refine MulEquiv.ext fun v => ?_
    set c := ρ z v * v⁻¹ with hc
    have hcW : c ∈ W := moves_mem_closure htw hz v
    have hzv : ρ z v = v * c := by rw [hc, mul_comm v, inv_mul_cancel_right]
    have hpow : ∀ n : ℕ, ρ (z ^ n) v = v * c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, hzv, map_pow, hfixW c hcW,
          pow_succ]
        group
    obtain ⟨k, hk⟩ := hodd
    have h1 : v * c ^ (orderOf z) = v := by
      rw [← hpow, pow_orderOf_eq_one, map_one, MulAut.one_apply]
    have hc1 : c ^ (orderOf z) = 1 := by
      have := congrArg (fun u => v⁻¹ * u) h1
      simpa using this
    have hcc : c ^ 2 = 1 := by rw [pow_two]; exact hV c
    have : c = 1 := by
      rw [hk, pow_succ, pow_mul, hcc, one_pow, one_mul] at hc1
      exact hc1
    show ρ z v = v
    rw [hzv, this, mul_one]
  exact hρ (hρz.trans (map_one ρ).symm)

end CFSG.CGT.Foote81L6.Normalizer
