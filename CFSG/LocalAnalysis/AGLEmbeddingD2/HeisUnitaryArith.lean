module

public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.RankThree.PartOne.Q1327T.R8Homo
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbeddingD2.HeisUnitary

open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Unitary CFSG.Quasithin
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem two_pow_mod_five_eq (f : ℕ) : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod f 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_five_cases (f : ℕ) :
    (f % 4 = 0 ∧ 2 ^ f % 5 = 1) ∨ (f % 4 = 1 ∧ 2 ^ f % 5 = 2) ∨
      (f % 4 = 2 ∧ 2 ^ f % 5 = 4) ∨ (f % 4 = 3 ∧ 2 ^ f % 5 = 3) := by
  have h := two_pow_mod_five_eq f
  have hr : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hh : f % 4 <;> simp_all

theorem five_dvd_two_pow_add_one_iff (f : ℕ) : 5 ∣ 2 ^ f + 1 ↔ f % 4 = 2 := by
  rcases two_pow_mod_five_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem not_five_dvd_two_pow (f : ℕ) : ¬ 5 ∣ 2 ^ f := fun h =>
  absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
    (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)

theorem orderOf_neg_two_pow_zmod_five_of_mod_two (f : ℕ) (h : f % 4 = 2) :
    orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) = 1 := by
  rcases two_pow_mod_five_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    try omega
  rw [← ZMod.natCast_mod, h2, orderOf_eq_one_iff]
  decide

theorem orderOf_neg_two_pow_zmod_five_of_mod_zero (f : ℕ) (h : f % 4 = 0) :
    orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) = 2 := by
  rcases two_pow_mod_five_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    try omega
  rw [← ZMod.natCast_mod, h2]
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_neg_two_pow_zmod_five_of_odd (f : ℕ) (h : f % 2 = 1) :
    orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) = 4 := by
  rcases two_pow_mod_five_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    try omega
  · rw [← ZMod.natCast_mod, h2, orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  · rw [← ZMod.natCast_mod, h2, orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide

theorem div_orderOf_lt_five {f n : ℕ} (h : (f % 2 = 1 ∧ n < 20) ∨ (f % 4 = 0 ∧ n < 10) ∨
    (f % 4 = 2 ∧ n < 5)) : n / orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) < 5 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [orderOf_neg_two_pow_zmod_five_of_odd f h1]
    omega
  · rw [orderOf_neg_two_pow_zmod_five_of_mod_zero f h1]
    omega
  · rw [orderOf_neg_two_pow_zmod_five_of_mod_two f h1]
    omega

section Field

variable {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem exists_order_five (hf : Even f) : ∃ ω : Fˣ, ω ^ 5 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hd : 5 ∣ Nat.card F - 1 := by
    obtain ⟨k, rfl⟩ := hf
    have h16 : (2 ^ (k + k)) ^ 2 = 16 ^ k := by
      rw [← pow_mul, show (k + k) * 2 = 4 * k by ring, pow_mul]; norm_num
    rw [hF, h16]
    exact Nat.dvd_trans (by norm_num : 5 ∣ 15) (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 k)
  have h : 5 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 h
  exact ⟨z, by rw [← hz]; exact pow_orderOf_eq_one z, fun h1 => by
    rw [h1, orderOf_one] at hz; omega⟩

variable [CharP F 2]

theorem unitaryInvolution_eq_pow_of_pow_five {ω : Fˣ} (hω5 : ω ^ 5 = 1) :
    unitaryInvolution F 2 f (ω : F) = ((ω ^ (2 ^ f % 5) : Fˣ) : F) := by
  rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, pow_eq_pow_mod _ hω5]

theorem unitaryInvolution_eq_self_of_pow_five {ω : Fˣ} (hω5 : ω ^ 5 = 1) (hf : f % 4 = 0) :
    unitaryInvolution F 2 f (ω : F) = ω := by
  rw [unitaryInvolution_eq_pow_of_pow_five hω5]
  rcases two_pow_mod_five_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    try omega
  rw [h2, pow_one]

end Field

section Weir

theorem isMulCommutative_of_isPGroup_five_statedGU {K : Type} [Field K] [Finite K] {q N : ℕ}
    (hK : Nat.card K = q ^ 2) (hq5 : ¬ 5 ∣ q) (hN : 1 ≤ N)
    (h : N / orderOf (-(q : ZMod 5)) < 5) {P : Subgroup (StatedGU N q K)} (hP : IsPGroup 5 P) :
    IsMulCommutative P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = q ^ 2 := by rw [← hK, Nat.card_eq_fintype_card]
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨e⟩ := sylow_GU (by decide : Odd 5) K hcard hq5 hN S
  obtain ⟨φ⟩ := (CFSG.RankThree.PartOne.Q1327T.R8.nonempty_sigmaModel_mulEquiv_homo h).map
    (fun e' => e.trans e')
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab : (⟨a.1, hPS a.2⟩ : (S : Subgroup (StatedGU N q K))) *
      ⟨b.1, hPS b.2⟩ = ⟨b.1, hPS b.2⟩ * ⟨a.1, hPS a.2⟩ :=
    φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hab' : a.1 * b.1 = b.1 * a.1 := congrArg Subtype.val hab
  exact Subtype.ext hab'

theorem isMulCommutative_of_isPGroup_five_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 1 ≤ n)
    (h : n / orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) < 5)
    {Q : Subgroup (SU (unitaryInvolution F 2 f) n)} (hQ : IsPGroup 5 Q) : IsMulCommutative Q := by
  have hle : StatedSU n (2 ^ f) F ≤ StatedGU n (2 ^ f) F :=
    Subgroup.closure_mono (fun A hA => hA.2)
  let ψ : SU (unitaryInvolution F 2 f) n →* StatedGU n (2 ^ f) F :=
    (Subgroup.inclusion hle).comp (equivStatedSU hF n).toMonoidHom
  have hψ : Function.Injective ψ :=
    (Subgroup.inclusion_injective hle).comp (equivStatedSU hF n).injective
  have hc := isMulCommutative_of_isPGroup_five_statedGU hF (not_five_dvd_two_pow f) hn h
    (hQ.map ψ)
  refine ⟨⟨fun a b => ?_⟩⟩
  have := hc.is_comm.comm ⟨ψ a, a, a.2, rfl⟩ ⟨ψ b, b, b.2, rfl⟩
  have h1 : ψ (a * b) = ψ (b * a) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val this
  exact Subtype.ext (hψ h1)

end Weir

end CFSG.AGLEmbeddingD2.HeisUnitary
