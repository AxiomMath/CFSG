module

public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.Unitary.Perfect
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix CFSG.Assembly.LowTwoRank CFSG.Glauberman CFSG.RankThree.SubgroupLists

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem isSimpleGroup_statedProj_three [Fact p.Prime] (hK : Nat.card K = (p ^ f) ^ 2)
    (hq4 : p ^ f % 4 = 1) : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
  CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl (by
    intro h
    have h2 : p ^ f = 2 := (Prod.mk.inj h).2
    omega)

theorem isPerfect_statedSU_three_odd [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Group.IsPerfect (StatedSU 3 (p ^ f) K) := by
  have := CFSG.ClassicalGroups.Unitary.isPerfect_SUid (n := 3)
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
    fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
      (CFSG.LieType.Steinberg.pow_ne_two_of_ne_two Fact.out hp2 f)
  rwa [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3] at this

theorem involved_qdSL_statedProj_three [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Involved (qdSL p) (StatedProj (StatedSU 3 (p ^ f) K)) := by
  obtain ⟨e₁⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := p) (f := f) hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_leviPSU3 (K := K) (p ^ f)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  let ι : ZMod p →+* ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) := ZMod.castHom (dvd_refl p) _
  let φ : SpecialLinearGroup (Fin 2) (ZMod p) →*
      SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) :=
    SpecialLinearGroup.map ι
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) =>
      (g : Matrix (Fin 2) (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f))) h
    exact Matrix.map_injective ι.injective this
  let ψ : qdSL p →* StatedProj (StatedSU 3 (p ^ f) K) :=
    (leviPSU3 (K := K) (p ^ f)).subtype.comp (e₂.toMonoidHom.comp (e₁.toMonoidHom.comp φ))
  have hψ : Function.Injective ψ :=
    Subtype.val_injective.comp (e₂.injective.comp (e₁.injective.comp hφ))
  exact ⟨ψ.range, ⊥, Subgroup.normal_bot,
    ⟨(QuotientGroup.quotientBot).trans (MonoidHom.ofInjective hψ).symm⟩⟩

theorem not_cube_dvd_three_factorial {q : ℕ} (hq4 : q % 4 = 1) (hq5 : 5 ≤ q) :
    ¬ q ^ 3 ∣ 119750400 := by
  intro key
  have hle : q ^ 3 ≤ 119750400 := Nat.le_of_dvd (by norm_num) key
  have hq' : q ≤ 500 := by
    by_contra hcon
    have : 500 ^ 3 < q ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  clear hle
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  have hm : m ≤ 124 := by omega
  have hm1 : 1 ≤ m := by omega
  clear hq4 hq5 hq'
  interval_cases m <;> revert key <;> decide

omit [Finite K] in
theorem not_card_dvd_factorial_statedProj_three [Fact p.Prime] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1) :
    ¬ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) ∣ Nat.factorial 11 := by
  intro hdvd
  have hp : p.Prime := Fact.out
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hp hf hK (by norm_num)
  have hq5 : 5 ≤ p ^ f := by
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hq1 : 1 ≤ p ^ f := by omega
  have e1 : (∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    have a1 : ((((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    have a2 : ((((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    rw [a1, a2]
  rw [e1] at hcard
  have hg3 : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgd : Nat.gcd 3 (p ^ f + 1) ∣ (p ^ f) ^ 3 + 1 := by
    have h1 : p ^ f + 1 ∣ (p ^ f) ^ 3 + 1 ^ 3 :=
      Odd.nat_add_dvd_pow_add_pow (p ^ f) 1 (by decide)
    rw [one_pow] at h1
    exact dvd_trans (Nat.gcd_dvd_right _ _) h1
  have hmul : Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [hcard]
    exact Nat.div_mul_cancel
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hgd _) _)
  have key : (p ^ f) ^ 3 ∣ 3 * Nat.factorial 11 := by
    have h1 : (p ^ f) ^ 3 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) *
        Nat.gcd 3 (p ^ f + 1) := by
      rw [hmul]
      exact dvd_mul_right _ _
    rw [mul_comm 3]
    exact dvd_trans h1 (Nat.mul_dvd_mul hdvd hg3)
  have h3f : 3 * Nat.factorial 11 = 119750400 := by decide
  rw [h3f] at key
  exact not_cube_dvd_three_factorial hq4 hq5 key

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
