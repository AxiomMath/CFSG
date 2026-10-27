module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.GorensteinWalter

section Psl2

variable {K : Type} [Field K] [Finite K]

theorem exists_commuting_involutions_psl2 (hK : IsOddPrimePower (Nat.card K)) :
    ∃ a b : PSL2 K, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (PSL2 K) := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK S
  have h2m : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (m - 1) := by positivity
  set a₀ : DihedralGroup (2 ^ m) := DihedralGroup.r (2 ^ (m - 1) : ℕ) with ha₀
  set b₀ : DihedralGroup (2 ^ m) := DihedralGroup.sr 0 with hb₀
  have ha2 : a₀ * a₀ = 1 := by
    rw [ha₀, DihedralGroup.r_mul_r, DihedralGroup.one_def]
    congr 1
    rw [← Nat.cast_add, ← two_mul, ← h2m]
    exact ZMod.natCast_self _
  have hb2 : b₀ * b₀ = 1 := by
    rw [hb₀, DihedralGroup.sr_mul_self]
  have hab : a₀ * b₀ = b₀ * a₀ := by
    rw [ha₀, hb₀, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    have hz : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [← Nat.cast_add, ← two_mul, ← h2m]; exact ZMod.natCast_self _
    simpa using neg_eq_of_add_eq_zero_left hz
  have ha1 : a₀ ≠ 1 := by
    rw [ha₀, DihedralGroup.one_def]
    intro h
    have h' := DihedralGroup.r.inj h
    have h'' : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := h'
    rw [ZMod.natCast_eq_zero_iff] at h''
    have := Nat.le_of_dvd hpos h''
    omega
  have hb1 : b₀ ≠ 1 := by
    rw [hb₀, DihedralGroup.one_def]
    intro h
    cases h
  have hab1 : a₀ ≠ b₀ := by
    rw [ha₀, hb₀]
    intro h
    cases h
  refine ⟨((e.symm a₀ : S) : PSL2 K), ((e.symm b₀ : S) : PSL2 K), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (fun x => ((e.symm x : S) : PSL2 K)) ha2
    simpa [map_mul] using this
  · have := congrArg (fun x => ((e.symm x : S) : PSL2 K)) hb2
    simpa [map_mul] using this
  · have := congrArg (fun x => ((e.symm x : S) : PSL2 K)) hab
    simpa [map_mul] using this
  · intro h
    apply ha1
    have : e.symm a₀ = 1 := Subtype.ext (by simpa using h)
    simpa using this
  · intro h
    apply hb1
    have : e.symm b₀ = 1 := Subtype.ext (by simpa using h)
    simpa using this
  · intro h
    apply hab1
    have : e.symm a₀ = e.symm b₀ := Subtype.ext h
    exact e.symm.injective this


end Psl2

section TR

variable {W : Type} [Group W] [Finite W] {K : Type} [Field K] [Finite K]

omit [Finite W] [Finite K] in
theorem exists_invol_lift (ψ : W →* PSL2 K) (hψ : Function.Surjective ψ)
    (hker : ∀ w, ψ w = 1 → Odd (orderOf w)) {a : PSL2 K} (ha2 : a * a = 1) :
    ∃ w : W, w * w = 1 ∧ ψ w = a := by
  obtain ⟨w₀, hw₀⟩ := hψ a
  have hsq : ψ (w₀ * w₀) = 1 := by rw [map_mul, hw₀, ha2]
  have hodd := hker _ hsq
  obtain ⟨k, hk⟩ := hodd
  refine ⟨w₀ ^ orderOf (w₀ * w₀), ?_, ?_⟩
  · calc w₀ ^ orderOf (w₀ * w₀) * w₀ ^ orderOf (w₀ * w₀) = (w₀ * w₀) ^ orderOf (w₀ * w₀) := by
          rw [← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := pow_orderOf_eq_one _
  · rw [map_pow, hw₀, hk]
    calc a ^ (2 * k + 1) = (a * a) ^ k * a := by rw [pow_succ, pow_mul, sq]
      _ = a := by rw [ha2, one_pow, one_mul]

omit [Finite W] in
theorem tr_conj (hK : IsOddPrimePower (Nat.card K)) (ψ : W →* PSL2 K)
    (hker : ∀ w, ψ w = 1 → (∀ v : W, v * w = w * v) ∧ Odd (orderOf w)) (hψ : Function.Surjective ψ)
    {a b : W} (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ c : W, c * a * c⁻¹ = b := by
  have hψne : ∀ w : W, w * w = 1 → w ≠ 1 → ψ w ≠ 1 := by
    intro w hw2 hw1 h1
    have hodd := (hker w h1).2
    have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
    rw [hord] at hodd
    exact absurd hodd (by decide)
  have hia : BenderSuzuki.PFAppendixIII.IsInvolution (ψ a) :=
    ⟨hψne a ha2 ha1, by rw [sq, ← map_mul, ha2, map_one]⟩
  have hib : BenderSuzuki.PFAppendixIII.IsInvolution (ψ b) :=
    ⟨hψne b hb2 hb1, by rw [sq, ← map_mul, hb2, map_one]⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K hK (ψ a) (ψ b) hia hib
  obtain ⟨c, rfl⟩ := hψ g
  set ζ : W := (c * a * c⁻¹)⁻¹ * b with hζ
  have hζk : ψ ζ = 1 := by
    rw [hζ, map_mul, map_inv, map_mul, map_mul, map_inv, hg]
    group
  obtain ⟨hζc, hζodd⟩ := hker ζ hζk
  have hcac : c * a * c⁻¹ = b * ζ⁻¹ := by rw [hζ]; group
  have hsq : (b * ζ⁻¹) * (b * ζ⁻¹) = 1 := by
    rw [← hcac]
    calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hζ2 : ζ * ζ = 1 := by
    have hcomm : ζ⁻¹ * b = b * ζ⁻¹ := by
      have := hζc b
      calc ζ⁻¹ * b = ζ⁻¹ * (b * ζ) * ζ⁻¹ := by group
        _ = ζ⁻¹ * (ζ * b) * ζ⁻¹ := by rw [this]
        _ = b * ζ⁻¹ := by group
    have : b * ζ⁻¹ * (b * ζ⁻¹) = (b * b) * (ζ⁻¹ * ζ⁻¹) := by
      calc b * ζ⁻¹ * (b * ζ⁻¹) = b * (ζ⁻¹ * b) * ζ⁻¹ := by group
        _ = b * (b * ζ⁻¹) * ζ⁻¹ := by rw [hcomm]
        _ = (b * b) * (ζ⁻¹ * ζ⁻¹) := by group
    rw [this, hb2, one_mul] at hsq
    have : ζ⁻¹ * ζ⁻¹ = (ζ * ζ)⁻¹ := by group
    rw [this] at hsq
    exact inv_eq_one.mp hsq
  have hζ1 : ζ = 1 := by
    by_contra hne
    have hord : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hζ2) hne
    rw [hord] at hζodd
    exact absurd hζodd (by decide)
  refine ⟨c, ?_⟩
  rw [hcac, hζ1]; group

omit [Finite W] in
theorem tr_four (hK : IsOddPrimePower (Nat.card K)) (ψ : W →* PSL2 K)
    (hker : ∀ w, ψ w = 1 → (∀ v : W, v * w = w * v) ∧ Odd (orderOf w)) (hψ : Function.Surjective ψ) :
    ∃ a c : W, a * a = 1 ∧ c * c = 1 ∧ a * c = c * a ∧ a ≠ 1 ∧ c ≠ 1 ∧ a ≠ c := by
  obtain ⟨a1, b1, ha12, hb12, ha1b1, ha11, hb11, hab1⟩ := exists_commuting_involutions_psl2 hK
  obtain ⟨a, ha2, haψ⟩ := exists_invol_lift ψ hψ (fun w hw => (hker w hw).2) ha12
  obtain ⟨b, hb2, hbψ⟩ := exists_invol_lift ψ hψ (fun w hw => (hker w hw).2) hb12
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hsq : ψ ((a * b) * (a * b)) = 1 := by
    simp only [map_mul, haψ, hbψ]
    calc a1 * b1 * (a1 * b1) = a1 * (b1 * a1) * b1 := by group
      _ = a1 * (a1 * b1) * b1 := by rw [← ha1b1]
      _ = (a1 * a1) * (b1 * b1) := by group
      _ = 1 := by rw [ha12, hb12, one_mul]
  have hodd := (hker _ hsq).2
  obtain ⟨k, hk⟩ := hodd
  set n := orderOf ((a * b) * (a * b)) with hn
  set c := (a * b) ^ n with hc
  have hc2 : c * c = 1 := by
    calc c * c = ((a * b) * (a * b)) ^ n := by rw [hc, ← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := pow_orderOf_eq_one _
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hψc : ψ c = a1 * b1 := by
    rw [hc, map_pow, map_mul, haψ, hbψ, hk]
    have hsq' : (a1 * b1) * (a1 * b1) = 1 := by
      calc a1 * b1 * (a1 * b1) = a1 * (b1 * a1) * b1 := by group
        _ = a1 * (a1 * b1) * b1 := by rw [← ha1b1]
        _ = (a1 * a1) * (b1 * b1) := by group
        _ = 1 := by rw [ha12, hb12, one_mul]
    calc (a1 * b1) ^ (2 * k + 1) = ((a1 * b1) * (a1 * b1)) ^ k * (a1 * b1) := by rw [pow_succ, pow_mul, sq]
      _ = a1 * b1 := by rw [hsq', one_pow, one_mul]
  have hcomm : a * c = c * a := by
    have h1 : a * c * a⁻¹ = c := by
      have e1 : a * (a * b) * a⁻¹ = b * a := by
        rw [hai]
        calc a * (a * b) * a = (a * a) * b * a := by group
          _ = b * a := by rw [ha2, one_mul]
      calc a * c * a⁻¹ = (a * (a * b) * a⁻¹) ^ n := by rw [conj_pow]
        _ = (b * a) ^ n := by rw [e1]
        _ = ((a * b)⁻¹) ^ n := by rw [mul_inv_rev, hai, hbi]
        _ = c⁻¹ := by rw [inv_pow]
        _ = c := hci
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h1]
  refine ⟨a, c, ha2, hc2, hcomm, ?_, ?_, ?_⟩
  · intro h
    apply ha11
    rw [← haψ, h, map_one]
  · intro h
    have : ψ c = 1 := by rw [h, map_one]
    rw [hψc] at this
    have hb : b1 = a1⁻¹ := eq_inv_of_mul_eq_one_right this
    have hai' : a1⁻¹ = a1 := inv_eq_of_mul_eq_one_right ha12
    exact hab1 (hai' ▸ hb).symm
  · intro h
    have : ψ c = ψ a := by rw [h]
    rw [hψc, haψ] at this
    exact hb11 (mul_eq_left.mp this)


omit [Finite W] in
theorem tr_center (ψ : W →* PSL2 K) (hker : ∀ w, ψ w = 1 → (∀ v : W, v * w = w * v) ∧ Odd (orderOf w))
    (hψ : Function.Surjective ψ) {w : W} (hwc : ∀ v : W, v * w = w * v) (hw2 : w * w = 1) : w = 1 := by
  have hcen : ψ w ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨v, rfl⟩ := hψ g
    rw [← map_mul, ← map_mul, hwc v]
  rw [psl2_center_eq_bot K, Subgroup.mem_bot] at hcen
  have hodd := (hker w hcen).2
  by_contra hne
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hne
  rw [hord] at hodd
  exact absurd hodd (by decide)

end TR

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
