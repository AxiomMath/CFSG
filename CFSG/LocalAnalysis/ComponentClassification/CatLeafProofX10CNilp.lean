module

public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10CNilp

open CFSG Subgroup

theorem hasNormalPComplement_of_ker {W A : Type*} [Group W] [Finite W] [Group A] [Finite A]
    (φ : W →* A) {C : Subgroup A} (hφC : ∀ w, φ w ∈ C) (hC : HasNormalPComplement 2 C)
    (hker : ∀ y : W, Odd (orderOf y) → ∀ Q₀ : Subgroup W, IsPGroup 2 Q₀ → Q₀ ≤ φ.ker →
      y ∈ normalizer (Q₀ : Set W) → ∀ x ∈ Q₀, y * x * y⁻¹ = x) :
    HasNormalPComplement 2 W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hcop, hq2⟩ := hC
  have hoddN : ∀ c : C, Odd (orderOf c) → c ∈ N := by
    intro c hc
    obtain ⟨n, hn⟩ := hq2 (c : C ⧸ N)
    have h1 : orderOf (c : C ⧸ N) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf (c : C ⧸ N) ∣ orderOf c := orderOf_map_dvd (QuotientGroup.mk' N) c
    have h3 : Nat.Coprime (orderOf (c : C ⧸ N)) (2 ^ n) :=
      ((Nat.coprime_two_right.2 hc).pow_right n).coprime_dvd_left h2
    rw [← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
    exact h3.eq_one_of_dvd h1
  have h2N : ∀ c ∈ N, (∃ n : ℕ, orderOf c = 2 ^ n) → c = 1 := by
    intro c hc ⟨n, hn⟩
    have h1 : orderOf (⟨c, hc⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hn] at h1
    have h2 : Nat.Coprime (2 ^ n) (Nat.card N) := Nat.Coprime.pow_left n hcop
    have h3 : 2 ^ n = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
    rw [← orderOf_eq_one_iff, hn, h3]
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ m
  induction m using QuotientGroup.induction_on with
  | H m =>
    obtain ⟨k, o, hodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    set y : W := ((m ^ 2 ^ k : ↥(normalizer (Q : Set W))) : W) with hy
    have hyN : y ∈ normalizer (Q : Set W) := (m ^ 2 ^ k).2
    have hyo : Odd (orderOf y) := by
      have h1 : orderOf (m ^ 2 ^ k) ∣ o := orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, ← hord, pow_orderOf_eq_one])
      rw [hy, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hodd h1
    have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hyN q).mp hq
    have hcomm : ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ φ.ker := by
      intro q hq
      set yc : C := ⟨φ y, hφC y⟩ with hyc
      set qc : C := ⟨φ q, hφC q⟩ with hqc
      have hycN : yc ∈ N := hoddN yc (by
        rw [hyc, Subgroup.orderOf_mk]
        exact Odd.of_dvd_nat hyo (orderOf_map_dvd φ y))
      have hcN : yc * qc * yc⁻¹ * qc⁻¹ ∈ N := by
        have e : yc * qc * yc⁻¹ * qc⁻¹ = yc * (qc * yc⁻¹ * qc⁻¹) := by group
        rw [e]
        exact mul_mem hycN (hN.conj_mem _ (inv_mem hycN) qc)
      have hc2 : ∃ n : ℕ, orderOf (yc * qc * yc⁻¹ * qc⁻¹) = 2 ^ n := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ)
          ⟨y * q * y⁻¹ * q⁻¹, mul_mem (hyQ q hq) (inv_mem hq)⟩
        have h1 : orderOf (yc * qc * yc⁻¹ * qc⁻¹) ∣ 2 ^ n := by
          have e : ((yc * qc * yc⁻¹ * qc⁻¹ : C) : A) = φ (y * q * y⁻¹ * q⁻¹) := by
            simp [hyc, hqc, map_mul, map_inv]
          rw [← Subgroup.orderOf_coe, e]
          refine (orderOf_map_dvd φ (y * q * y⁻¹ * q⁻¹)).trans ?_
          rw [← hn, Subgroup.orderOf_mk]
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
        exact ⟨j, hj⟩
      have h1 := h2N _ hcN hc2
      rw [MonoidHom.mem_ker]
      have h2 := congrArg Subtype.val h1
      simpa [hyc, hqc, map_mul, map_inv] using h2
    have hQ₀ : ∀ x ∈ Q ⊓ φ.ker, y * x * y⁻¹ = x := by
      refine hker y hyo _ (hQ.to_le inf_le_left) inf_le_right ?_
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨hxQ, hxK⟩ := mem_inf.mp hx
        refine mem_inf.mpr ⟨hyQ x hxQ, ?_⟩
        exact (φ.normal_ker).conj_mem x hxK y
      · intro hx
        obtain ⟨hxQ, hxK⟩ := mem_inf.mp hx
        have hyi : y⁻¹ ∈ normalizer (Q : Set W) := inv_mem hyN
        have e1 : x = y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ := by group
        rw [e1]
        refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hyi _).mp hxQ, ?_⟩
        exact (φ.normal_ker).conj_mem _ hxK y⁻¹
    rw [mem_centralizer_iff]
    intro q hq
    set c := y * q * y⁻¹ * q⁻¹ with hc
    have hcQ : c ∈ Q ⊓ φ.ker := mem_inf.mpr ⟨mul_mem (hyQ q hq) (inv_mem hq), hcomm q hq⟩
    have hyc : y * c * y⁻¹ = c := hQ₀ c hcQ
    have hstep : y * q * y⁻¹ = c * q := by rw [hc]; group
    clear_value c
    have hpow : ∀ j : ℕ, y ^ j * q * (y ^ j)⁻¹ = c ^ j * q := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc y ^ (j + 1) * q * (y ^ (j + 1))⁻¹ = y * (y ^ j * q * (y ^ j)⁻¹) * y⁻¹ := by
              rw [pow_succ']
              group
          _ = (y * c * y⁻¹) ^ j * (y * q * y⁻¹) := by rw [ih, conj_pow]; group
          _ = c ^ (j + 1) * q := by rw [hyc, hstep, pow_succ, ← mul_assoc]
    have hcn : c ^ orderOf y = 1 := by
      have h1 := hpow (orderOf y)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
      exact (mul_eq_right.mp h1.symm)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp (hQ.to_le inf_le_left))
      (⟨c, hcQ⟩ : ↥(Q ⊓ φ.ker))
    rw [Subgroup.orderOf_mk] at hn
    have h1 : orderOf c ∣ orderOf y := orderOf_dvd_of_pow_eq_one hcn
    have h3 : Nat.Coprime (orderOf c) 2 := by
      have := Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_right.2 hyo)
      exact this
    have hc1 : c = 1 := by
      rw [← orderOf_eq_one_iff, hn]
      rw [hn] at h3
      rcases n with _ | n
      · rfl
      · exact absurd h3 (by
          rw [Nat.coprime_two_right, Nat.not_odd_iff_even]
          exact Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero n⟩)
    have h4 : y * q * y⁻¹ = q := by rw [hstep, hc1, one_mul]
    calc q * y = y * (y⁻¹ * q * y) := by group
      _ = y * q := by
        congr 1
        calc y⁻¹ * q * y = y⁻¹ * (y * q * y⁻¹) * y := by rw [h4]
          _ = q := by group

end CFSG.ComponentClassification.GSThmB.X10CNilp
