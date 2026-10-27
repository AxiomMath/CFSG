module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralMovedFixedSubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BottomCentralInvolutionInverts

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem odd_of_isPrimePow {e : ℕ} (he : 2 < e) (hr : IsPrimePow (2 ^ e - 1)) : Odd e := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, rfl⟩ := hodd
  have hk : 2 ≤ k := by omega
  obtain ⟨q, n, hq, hn, hqn⟩ := hr
  have hq' : q.Prime := hq.nat_prime
  set a := 2 ^ k - 1 with ha
  set b := 2 ^ k + 1 with hb
  have hpos : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hab : (2 : ℕ) ^ (k + k) - 1 = a * b := by
    have : (2:ℕ) ^ (k + k) = 2 ^ k * 2 ^ k := pow_add _ _ _
    rw [this, ha, hb]
    generalize 2 ^ k = t at *
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    apply Nat.sub_eq_of_eq_add
    simp only [Nat.add_sub_cancel]
    ring
  have hcop : Nat.Coprime a b := by
    have hb' : b = 2 + a := by omega
    rw [hb']
    have hodd : Odd a := by
      have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rw [ha]; obtain ⟨m, hm⟩ := this; exact ⟨m - 1, by omega⟩
    exact Nat.coprime_add_self_right.mpr (Nat.coprime_two_right.mpr hodd)
  rw [hab] at hqn
  have h1 : a ∣ q ^ n := ⟨b, hqn⟩
  have h2 : b ∣ q ^ n := ⟨a, by rw [hqn]; ring⟩
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow hq').1 h1
  obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow hq').1 h2
  have hi0 : i ≠ 0 := by rintro rfl; simp at hai; omega
  have hj0 : j ≠ 0 := by rintro rfl; simp at hbj; omega
  have hqa : q ∣ a := hai ▸ dvd_pow_self q hi0
  have hqb : q ∣ b := hbj ▸ dvd_pow_self q hj0
  exact hq'.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqa hqb)

theorem inverts {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXbot : CentralBinaryBlocks.X hc = ⊥) :
    ∀ y ∈ CentralBinaryBlocks.Y hc, y ≠ 1 → ∀ x : P, y x = x⁻¹ := by
  intro y hy hy1 x
  have he : Odd e := odd_of_isPrimePow hc.oddPrimeClassTwoAction.two_lt hr
  have hy2 : y ^ 2 = 1 := (CentralBinarySubgroup.Y_elemAbelian hc).2 y hy
  have hzY : Subgroup.zpowers y ≤ CentralBinaryBlocks.Y hc :=
    (Subgroup.zpowers_le).2 hy
  have hne : Subgroup.zpowers y ≠ ⊥ := by
    intro h
    exact hy1 (by simpa using (Subgroup.zpowers_eq_bot.mp h))
  have hXT := hzY.trans (CentralBinarySubgroup.Y_le hc)
  have hcent : ∀ ψ ∈ Subgroup.zpowers y, ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal),
      Commute ψ φ := fun ψ hψ =>
    CentralBinarySubgroup.Y_commute hc ψ (hzY hψ)
  have hBX : Bstar P B ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (MulAut P)) := by
    intro b hb
    have hcomm : ⁅y, b⁆ = 1 := by
      have : ⁅y, b⁆ ∈ CentralBinaryBlocks.X hc := Subgroup.commutator_mem_commutator hy hb
      rw [hXbot] at this
      simpa using this
    have hcy : Commute y b := commutatorElement_eq_one_iff_commute.mp hcomm
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hcy.zpow_left n).eq
  have hfix := CentralMovedFixedSubgroup.fixed_eq_one hc he (Subgroup.zpowers y) hne hXT
    hcent hBX
  have hcomm : ∀ a b : P, a * b = b * a := fun a b =>
    (CentralBinaryBlocks.elemAbelian hc).1.is_comm.comm a b
  have hyy : ∀ z : P, y (y z) = z := fun z => by
    have : (y * y) z = z := by
      rw [← pow_two, hy2]; rfl
    simpa using this
  have h1 : y x * x = 1 := by
    apply hfix
    intro ψ hψ
    rw [Subgroup.zpowers_eq_closure] at hψ
    induction hψ using Subgroup.closure_induction with
    | mem a ha =>
      rw [Set.mem_singleton_iff.mp ha, map_mul, hyy]
      exact hcomm _ _
    | one => rfl
    | mul a b _ _ iha ihb =>
      rw [MulAut.mul_apply, ihb, iha]
    | inv a _ iha =>
      have := congrArg (a⁻¹ : MulAut P) iha
      rw [← MulAut.mul_apply, inv_mul_cancel] at this
      exact this.symm
  exact eq_inv_of_mul_eq_one_left h1

end CFSG.LocalAnalysis.RankThreeUC.Section5.BottomCentralInvolutionInverts
