module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22TripleCover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def fiPrimeToThree {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y)
    (hNc : N ≤ Subgroup.center Y) : Subgroup Y where
  carrier := {n | n ∈ N ∧ ¬ 3 ∣ orderOf n}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
    refine ⟨N.mul_mem ha hb, fun h => ?_⟩
    have hc : Commute a b := (Subgroup.mem_center_iff.1 (hNc hb) a)
    have h1 : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := hc.orderOf_mul_dvd_lcm
    have h2 : 3 ∣ orderOf a * orderOf b :=
      h.trans (h1.trans (Nat.lcm_dvd_mul _ _))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h2 with h3 | h3
    · exact ha3 h3
    · exact hb3 h3
  inv_mem' := by
    rintro a ⟨ha, ha3⟩
    exact ⟨N.inv_mem ha, by rwa [orderOf_inv]⟩

theorem card_N_inf_P_le_three
    (Y : Type) [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) (N : Subgroup Y) [N.Normal] (hNc : N ≤ Subgroup.center Y)
    (hF : IsFiTwentyTwo (Y ⧸ N)) (P : Subgroup Y) (hP : IsPGroup 3 P) :
    Nat.card ↥(N ⊓ P) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect Y := Group.isPerfect_def.2 hY
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  obtain ⟨e0⟩ := hF
  let φ : (Y ⧸ N) ≃* NativeSporadic.Carrier .Fi22 := e0.trans b.symm
  set N' := fiPrimeToThree N hNc with hN'
  have hN'N : N' ≤ N := fun x hx => hx.1
  have : N'.Normal := ⟨fun n hn g => by
    rw [show g * n * g⁻¹ = n by
      rw [(Subgroup.mem_center_iff.1 (hNc hn.1) g)]; group]
    exact hn⟩
  let πE : (Y ⧸ N') →* NativeSporadic.Carrier .Fi22 :=
    QuotientGroup.lift N' ((φ : (Y ⧸ N) →* NativeSporadic.Carrier .Fi22).comp
      (QuotientGroup.mk' N)) (fun x hx => by
        rw [MonoidHom.mem_ker]
        have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).2 (hN'N hx)
        show φ (QuotientGroup.mk' N x) = 1
        rw [h1, map_one])
  have hπE : ∀ y : Y, πE (QuotientGroup.mk' N' y) = φ (QuotientGroup.mk' N y) := fun y => rfl
  have hsurj : Function.Surjective πE := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (φ.symm c)
    refine ⟨QuotientGroup.mk' N' y, ?_⟩
    rw [hπE, hy]
    simp
  have hkerN : ∀ y : Y, πE (QuotientGroup.mk' N' y) = 1 → y ∈ N := fun y h => by
    rw [hπE] at h
    exact (QuotientGroup.eq_one_iff y).1 (φ.injective (by
      show φ (QuotientGroup.mk' N y) = φ 1
      rw [h, map_one]))
  have hc : πE.ker ≤ Subgroup.center (Y ⧸ N') := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' x
    have hy := hkerN y hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N' g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hNc hy) z]
  have hp : IsPGroup 3 πE.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' x
    have hy := hkerN y hx
    have hord : orderOf y ≠ 0 := (orderOf_pos y).ne'
    obtain ⟨a, m, hm, hym⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 Nat.prime_three.ne_one
    refine ⟨a, Subtype.ext ?_⟩
    have hz : y ^ 3 ^ a ∈ N' := by
      refine ⟨N.pow_mem hy _, ?_⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨m, hym⟩, hym,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    show (QuotientGroup.mk' N' y) ^ 3 ^ a = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hz
  have hdvd := card_ker_dvd_three_of_perfect_central_Fi22 (Y ⧸ N') πE hsurj hc hp
  let g : ↥(N ⊓ P) →* Y ⧸ N' := (QuotientGroup.mk' N').comp (N ⊓ P).subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : Y) ∈ N' := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk⟩ := hP ⟨(x : Y), x.2.2⟩
    have hxk : (x : Y) ^ 3 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hxk)
    have hj0 : j = 0 := by
      by_contra hne
      exact hx'.2 (by rw [hj]; exact dvd_pow_self 3 hne)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact Subtype.ext hj
  have hrange : g.range ≤ πE.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    change πE (QuotientGroup.mk' N' (x : Y)) = 1
    have h1 : QuotientGroup.mk' N (x : Y) = 1 := (QuotientGroup.eq_one_iff _).2 x.2.1
    rw [hπE, h1, map_one]
  calc Nat.card ↥(N ⊓ P) = Nat.card g.range := Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
    _ ≤ Nat.card πE.ker := Subgroup.card_le_of_le hrange
    _ ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd

end CFSG.HardMathSupport.Solomon.Coordinator
