module

public import CFSG.HardMathSupport.Malle.Coordinator.OuterFive
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {g : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : g ^ a ∈ H) (hb : g ^ b ∈ H) : g ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have : g = (g ^ a) ^ (Nat.gcdA a b) * (g ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

namespace OuterFiveData

variable {P Z : Subgroup G} {φ : G} (D : OuterFiveData P Z φ)
include D

theorem mem_normalizer : φ ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => D.conj_inv_mem y hy, fun hy => ?_⟩
  have := D.conj_mem _ hy
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro z
  constructor
  · intro hz
    have hzP : n * z * n⁻¹ ∈ P := (hn z).mp (D.le hz)
    refine D.omega _ hzP ?_
    rw [conj_pow, D.pow_five z hz]
    group
  · intro hz
    have hzP : z ∈ P := (hn z).mpr (D.le hz)
    refine D.omega _ hzP ?_
    have h5 : (n * z * n⁻¹) ^ 5 = 1 := D.pow_five _ hz
    rw [conj_pow] at h5
    have : z ^ 5 = n⁻¹ * (n * z ^ 5 * n⁻¹) * n := by group
    rw [this, h5]
    group

theorem pow_five_mem_of_mul_pow_five {n : G} (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (htw : n⁻¹ * (φ⁻¹ * n * φ) ∈ P) (h5 : (n * φ) ^ 5 = 1) : n ^ 5 ∈ P := by
  set W := Subgroup.normalizer (P : Set G) with hW
  have hPW : P ≤ W := Subgroup.le_normalizer
  have : (P.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPW).mpr le_rfl
  let a : W := ⟨n, hnP⟩
  let b : W := ⟨φ, D.mem_normalizer⟩
  have hab : Commute (a : W ⧸ P.subgroupOf W) (b : W ⧸ P.subgroupOf W) := by
    show ((a * b : W) : W ⧸ P.subgroupOf W) = ((b * a : W) : W ⧸ P.subgroupOf W)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((a * b)⁻¹ * (b * a) : W) = (φ⁻¹ * n * φ)⁻¹ * n := by
      simp only [a, b, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    have h := P.inv_mem htw
    simpa [mul_assoc] using h
  have hb5 : (b : W ⧸ P.subgroupOf W) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : b ^ 5 = 1 := Subtype.ext (by simpa [b] using D.order)
    rw [this, QuotientGroup.mk_one]
  have hab5 : ((a * b : W) : W ⧸ P.subgroupOf W) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (a * b) ^ 5 = 1 := Subtype.ext (by simpa [a, b] using h5)
    rw [this, QuotientGroup.mk_one]
  have ha5 : (a : W ⧸ P.subgroupOf W) ^ 5 = 1 := by
    rw [QuotientGroup.mk_mul, hab.mul_pow, hb5, mul_one] at hab5
    exact hab5
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha5
  simpa [a] using ha5

theorem exists_mul_commute_of_conj_mem_normalizer [Finite G] {K M : Subgroup G}
    (hPcard : Nat.card P = Nat.card Z * Nat.card Z) (hPM : P ≤ M) (hMK : M ≤ K)
    (hφK : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K) (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hφM : φ ∈ Subgroup.normalizer (M : Set G)) (hidx : ¬ 5 ∣ P.relIndex M)
    {m : G} (hm : m ∈ M) (hmφ : m⁻¹ * φ * m ∈ Subgroup.normalizer (P : Set G)) :
    ∃ p ∈ P, φ * (m * p) = m * p * φ := by
  set NM := M ⊓ Subgroup.normalizer (P : Set G) with hNM
  set n₁ := m⁻¹ * φ * m * φ⁻¹ with hn₁
  have hφmM : φ * m * φ⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hφM m).mp hm
  have hn₁M : n₁ ∈ M := by
    have : n₁ = m⁻¹ * (φ * m * φ⁻¹) := by rw [hn₁]; group
    rw [this]; exact M.mul_mem (M.inv_mem hm) hφmM
  have hn₁P : n₁ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ hmφ (Subgroup.inv_mem _ D.mem_normalizer)
  have hn₁N : n₁ ∈ NM := ⟨hn₁M, hn₁P⟩
  have htw : n₁⁻¹ * (φ⁻¹ * n₁ * φ) ∈ P :=
    D.twist_mem_of_centralizer_le (N := NM) (fun x hx => hMK hx.1)
      (fun x hx => D.normalizer_le_normalizer hx.2) hCZ hφK hn₁N
  have h5 : (n₁ * φ) ^ 5 = 1 := by
    have : n₁ * φ = m⁻¹ * φ * m := by rw [hn₁]; group
    rw [this, inv_conj_pow, D.order]
    group
  have hn₁5 : n₁ ^ 5 ∈ P := D.pow_five_mem_of_mul_pow_five hn₁P htw h5
  have hPNM : P ≤ NM := le_inf hPM Subgroup.le_normalizer
  have hnorm : (P.subgroupOf NM).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPNM).mpr inf_le_right
  have hn₁r : n₁ ^ P.relIndex NM ∈ P := by
    have h := (P.subgroupOf NM).pow_index_mem (⟨n₁, hn₁N⟩ : NM)
    rw [Subgroup.mem_subgroupOf] at h
    simpa [Subgroup.relIndex] using h
  have hcop : Nat.Coprime 5 (P.relIndex NM) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h
    apply hidx
    rw [← Subgroup.relIndex_mul_relIndex P NM M hPNM inf_le_left]
    exact Dvd.dvd.mul_right h _
  have hn₁mem : n₁ ∈ P := mem_of_pow_mem_of_coprime hcop hn₁5 hn₁r
  set y := φ⁻¹ * n₁ * φ with hy
  have hyP : y ∈ P := D.conj_mem _ hn₁mem
  have hny : n₁ * φ = φ * y := by rw [hy]; group
  have hyZ : y ∈ Z := (D.mul_pow_five_eq_one_iff hyP).mp (by rw [← hny]; exact h5)
  obtain ⟨p, hp, hpeq⟩ := D.exists_conj_eq_mul hPcard hyZ
  refine ⟨p⁻¹, P.inv_mem hp, ?_⟩
  have key : p⁻¹ * φ * p = m⁻¹ * φ * m := by
    rw [hpeq, ← hny, hn₁]; group
  calc φ * (m * p⁻¹) = m * (m⁻¹ * φ * m) * p⁻¹ := by group
    _ = m * (p⁻¹ * φ * p) * p⁻¹ := by rw [key]
    _ = m * p⁻¹ * φ := by group

end OuterFiveData

end CFSG.HardMathSupport.Malle.Coordinator
