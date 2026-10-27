module

public import CFSG.LieType.SeitzGeneration.HyperCoverLift

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Open CFSG.LieType.SeitzGeneration

variable {Y : Type*} [Group Y]

theorem centerQuotientHom_mk (K : Subgroup Y) [K.Normal] (g : MulAut K) (k : K) :
    centerQuotientHom K g (QuotientGroup.mk k) = QuotientGroup.mk (g k) :=
  onCenterQuotient_apply_mk g k

theorem exists_pow_lift {K : Type*} [Group K] [Finite K] (x : K ⧸ Subgroup.center K)
    (hx : (orderOf x).Coprime 3) :
    ∃ (m : ℕ) (k₁ : K), m.Coprime 3 ∧ (QuotientGroup.mk k₁ : K ⧸ Subgroup.center K) = x ∧
      k₁ ^ m = 1 := by
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective x
  set n := orderOf k₀ with hn
  have hn0 : n ≠ 0 := (orderOf_pos k₀).ne'
  set a := n.factorization 3 with ha
  set m := n / 3 ^ a with hm
  have hmc : m.Coprime 3 := (Nat.coprime_ordCompl Nat.prime_three hn0).symm
  have hnm : n = 3 ^ a * m := (Nat.ordProj_mul_ordCompl_eq_self n 3).symm
  set o := orderOf (QuotientGroup.mk k₀ : K ⧸ Subgroup.center K) with ho
  have hco : (3 ^ a).Coprime o := (Nat.Coprime.pow_left a hx.symm)
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hco 0 1
  refine ⟨m, k₀ ^ e, hmc, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow]
    have : (QuotientGroup.mk k₀ : K ⧸ Subgroup.center K) ^ e =
        (QuotientGroup.mk k₀ : K ⧸ Subgroup.center K) ^ 1 := by
      rw [pow_eq_pow_iff_modEq]
      exact he1
    rw [this, pow_one]
  · obtain ⟨e', he'⟩ := (Nat.modEq_zero_iff_dvd.1 he0)
    rw [← pow_mul, he', show 3 ^ a * e' * m = n * e' by rw [hnm]; ring, pow_mul,
      hn, pow_orderOf_eq_one, one_pow]

@[expose] def centerTorsion (K : Type*) [Group K] (m : ℕ) : Subgroup K where
  carrier := {z | z ∈ Subgroup.center K ∧ z ^ m = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hc : Commute a b := (Subgroup.mem_center_iff.1 hb a)
    rw [hc.mul_pow, ha1, hb1, one_mul]
  one_mem' := ⟨one_mem _, one_pow m⟩
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    exact ⟨inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩

theorem coprime_card_centerTorsion {K : Type*} [Group K] [Finite K] {m : ℕ} (hm : m.Coprime 3) :
    (Nat.card (centerTorsion K m)).Coprime 3 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hz1 : (z : K) ^ m = 1 := z.2.2
  have hzo : orderOf (z : K) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have : 3 ∣ m := hzo ▸ orderOf_dvd_of_pow_eq_one hz1
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hm.symm this

theorem exists_fixed_lift [Finite Y] (K : Subgroup Y) [K.Normal] (F : Subgroup Y)
    (hF : IsPGroup 3 F) (x : K ⧸ Subgroup.center K) (hx : (orderOf x).Coprime 3)
    (hfix : ∀ f ∈ F, centerQuotientHom K (MulAut.conjNormal f) x = x) :
    ∃ k : K, (QuotientGroup.mk k : K ⧸ Subgroup.center K) = x ∧
      ∀ f ∈ F, f * (k : Y) = (k : Y) * f := by
  classical
  obtain ⟨m, k₁, hm, hk₁x, hk₁m⟩ := exists_pow_lift x hx
  let X := {k : K // (QuotientGroup.mk k : K ⧸ Subgroup.center K) = x ∧ k ^ m = 1}
  have hstab : ∀ g ∈ F, ∀ k : X,
      ((QuotientGroup.mk (MulAut.conjNormal g k.1) : K ⧸ Subgroup.center K) = x ∧
        (MulAut.conjNormal g k.1) ^ m = 1) := by
    intro g hg k
    refine ⟨?_, ?_⟩
    · rw [← centerQuotientHom_mk, k.2.1]
      exact hfix g hg
    · rw [← map_pow, k.2.2, map_one]
  have hcentral : ∀ (z : K), z ∈ Subgroup.center K → ∀ w : K, w * z = z * w :=
    fun z hz w => ((Subgroup.mem_center_iff.1 hz) w)
  let eqv : centerTorsion K m ≃ X :=
    { toFun := fun z => ⟨k₁ * z.1, by
        refine ⟨?_, ?_⟩
        · rw [QuotientGroup.mk_mul, hk₁x]
          have : (QuotientGroup.mk (z.1) : K ⧸ Subgroup.center K) = 1 :=
            (QuotientGroup.eq_one_iff _).2 z.2.1
          rw [this, mul_one]
        · rw [(Commute.mul_pow ((Subgroup.mem_center_iff.1 z.2.1) k₁) m), hk₁m, z.2.2,
            one_mul]⟩
      invFun := fun k => ⟨k₁⁻¹ * k.1, by
        have hz : k₁⁻¹ * k.1 ∈ Subgroup.center K := by
          have : (QuotientGroup.mk k₁ : K ⧸ Subgroup.center K) = QuotientGroup.mk k.1 := by
            rw [hk₁x, k.2.1]
          exact QuotientGroup.eq.1 this
        refine ⟨hz, ?_⟩
        have hk : k.1 = k₁ * (k₁⁻¹ * k.1) := by group
        have h1 : k.1 ^ m = k₁ ^ m * (k₁⁻¹ * k.1) ^ m := by
          conv_lhs => rw [hk]
          exact (Commute.mul_pow ((Subgroup.mem_center_iff.1 hz) k₁) m)
        rw [k.2.2, hk₁m, one_mul] at h1
        exact h1.symm⟩
      left_inv := fun z => by
        apply Subtype.ext
        simp
      right_inv := fun k => by
        apply Subtype.ext
        simp }
  have hcardX : Nat.card X = Nat.card (centerTorsion K m) := (Nat.card_congr eqv).symm
  let φ : F →* Equiv.Perm X :=
    { toFun := fun f =>
        { toFun := fun k => ⟨MulAut.conjNormal (f : Y) k.1, hstab f f.2 k⟩
          invFun := fun k => ⟨MulAut.conjNormal ((f : Y)⁻¹) k.1, hstab f⁻¹ (F.inv_mem f.2) k⟩
          left_inv := fun k => by
            apply Subtype.ext
            change MulAut.conjNormal ((f : Y)⁻¹) (MulAut.conjNormal (f : Y) k.1) = k.1
            rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
          right_inv := fun k => by
            apply Subtype.ext
            change MulAut.conjNormal (f : Y) (MulAut.conjNormal ((f : Y)⁻¹) k.1) = k.1
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
      map_one' := by
        refine Equiv.ext fun k => Subtype.ext (Subtype.ext ?_)
        simp
      map_mul' := fun f g => by
        refine Equiv.ext fun k => Subtype.ext (Subtype.ext ?_)
        simp [mul_assoc] }
  let _ : MulAction F X := MulAction.compHom X φ
  have hmod := hF.card_modEq_card_fixedPoints X
  have hne : Nat.card (MulAction.fixedPoints F X) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h3 : 3 ∣ Nat.card X := (Nat.modEq_zero_iff_dvd.1 hmod)
    rw [hcardX] at h3
    have := coprime_card_centerTorsion (K := K) hm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 this.symm h3
  obtain ⟨⟨k, hk⟩⟩ := Nat.card_ne_zero.1 hne |>.1
  refine ⟨k.1, k.2.1, fun f hf => ?_⟩
  have := MulAction.mem_fixedPoints.1 hk ⟨f, hf⟩
  have h2 : (MulAut.conjNormal f k.1 : K) = k.1 := congrArg Subtype.val this
  have h3 : f * (k.1 : Y) * f⁻¹ = (k.1 : Y) := by
    have := congrArg Subtype.val h2
    simpa [MulAut.conjNormal_apply] using this
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem isPGroup_three_of_le {E F : Subgroup Y} (hE : ∀ x ∈ E, x ^ 3 = 1) (hFE : F ≤ E) :
    IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hE g (hFE g.2))⟩

theorem hyperGen_of_generation [Finite Y] (K E : Subgroup Y) [K.Normal] (hK : Open.IsQuasisimple K)
    (hE : IsElemAbelian 3 E)
    (hgen : Subgroup.closure {x : K ⧸ Subgroup.center K | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup Y, H ≤ E ∧ H.relIndex E = 3 ∧
        ∀ y ∈ H, centerQuotientHom K (MulAut.conjNormal y) x = x} = ⊤) :
    HyperGen 3 K E := by
  classical
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  set N : Subgroup Y := Subgroup.closure {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E ∧
    F.relIndex E = 3 ∧ ∀ f ∈ F, f * k = k * f} with hN
  have hmap : (N.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x ⟨hx3, H, hHE, hHi, hfix⟩
    obtain ⟨k, hk, hcomm⟩ := exists_fixed_lift K H (isPGroup_three_of_le hE.2 hHE) x hx3 hfix
    refine ⟨k, ?_, hk⟩
    exact Subgroup.subset_closure ⟨k.2, H, hHE, hHi, hcomm⟩
  have htop := eq_top_of_map_eq_top_of_perfect (QuotientGroup.mk' (Subgroup.center K))
    (by simp) hmap
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ N.subgroupOf K := by rw [htop]; trivial
  exact this

end CFSG.HardMathSupport.Foote.ModuleExclusions
