module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Finite.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

def normExponent (p q : ℕ) : ℕ := (p ^ q - 1) / (p - 1)

theorem normExponent_def (p q : ℕ) : normExponent p q = (p ^ q - 1) / (p - 1) := (rfl)

theorem normExponent_mul_sub_one (p q : ℕ) : normExponent p q * (p - 1) = p ^ q - 1 :=
  Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p q)

structure AppendixCSetup (p q : ℕ) (F : Type*) [Field F] [Finite F]
    (G : Type*) [Group G] where
  p_prime : p.Prime
  q_prime : q.Prime
  q_lt_p : q < p
  card_field : Nat.card F = p ^ q
  coprime_normExponent : Nat.Coprime (normExponent p q) (p - 1)
  pt : Multiplicative F →* G
  pt_injective : Function.Injective pt
  ut : rootsOfUnity (normExponent p q) F →* G
  ut_injective : Function.Injective ut
  disjoint_ranges : Disjoint pt.range ut.range
  conj_pt : ∀ (z : F) (u : rootsOfUnity (normExponent p q) F),
    (ut u)⁻¹ * pt (Multiplicative.ofAdd z) * ut u
      = pt (Multiplicative.ofAdd (z * ((u : Fˣ) : F)))

namespace AppendixCSetup

variable {p q : ℕ} {F : Type*} [Field F] [Finite F] {G : Type*} [Group G]

def P (S : AppendixCSetup p q F G) : Subgroup G := S.pt.range

def U (S : AppendixCSetup p q F G) : Subgroup G := S.ut.range

def H (S : AppendixCSetup p q F G) : Subgroup G := S.P ⊔ S.U

def s (S : AppendixCSetup p q F G) : G := S.pt (Multiplicative.ofAdd 1)

def P₀ (S : AppendixCSetup p q F G) : Subgroup G :=
  Subgroup.map S.pt (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup)

theorem P_def (S : AppendixCSetup p q F G) : S.P = S.pt.range := (rfl)

theorem U_def (S : AppendixCSetup p q F G) : S.U = S.ut.range := (rfl)

theorem H_def (S : AppendixCSetup p q F G) : S.H = S.P ⊔ S.U := (rfl)

theorem s_def (S : AppendixCSetup p q F G) : S.s = S.pt (Multiplicative.ofAdd 1) := (rfl)

theorem P₀_def (S : AppendixCSetup p q F G) :
    S.P₀ = Subgroup.map S.pt (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup) := (rfl)

theorem P₀_le_P (S : AppendixCSetup p q F G) : S.P₀ ≤ S.P := by
  rintro g ⟨w, -, rfl⟩
  exact ⟨w, rfl⟩

theorem charP_field (S : AppendixCSetup p q F G) : CharP F p := by
  have : Fact p.Prime := ⟨S.p_prime⟩
  have : Fintype F := Fintype.ofFinite F
  refine charP_of_card_eq_prime_pow (p := p) (f := q) ?_
  rw [← Nat.card_eq_fintype_card]
  exact S.card_field

theorem P₀_eq_zpowers (S : AppendixCSetup p q F G) : S.P₀ = Subgroup.zpowers S.s := by
  have : Fact p.Prime := ⟨S.p_prime⟩
  have := S.charP_field
  apply le_antisymm
  · rintro g ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp (show Multiplicative.toAdd w ∈ _ from hw)
    have hwn : w = Multiplicative.ofAdd (n • (1 : F)) := by
      rw [zsmul_eq_mul, mul_one, hn]; rfl
    subst hwn
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simp [s, ← map_zpow, ← ofAdd_zsmul]⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨Multiplicative.ofAdd 1, Subfield.one_mem (⊥ : Subfield F), rfl⟩

theorem s_mem_P₀ (S : AppendixCSetup p q F G) : S.s ∈ S.P₀ := by
  rw [S.P₀_eq_zpowers]; exact mem_zpowers _

end AppendixCSetup

variable {G : Type*} [Group G]

def comparisonWord (s y r₁ r₃ : G) : G :=
  (r₃⁻¹ * y * r₃)⁻¹ * (s * y * s⁻¹) * (s * r₁ * y * (s * r₁)⁻¹)⁻¹ * y

theorem comparisonWord_def (s y r₁ r₃ : G) :
    comparisonWord s y r₁ r₃ =
      (r₃⁻¹ * y * r₃)⁻¹ * (s * y * s⁻¹) * (s * r₁ * y * (s * r₁)⁻¹)⁻¹ * y := (rfl)

private theorem rearrange_of_commGroup {A : Type*} [CommGroup A] (v₀ v₁ v₂ v₃ v₄ v₅ v₆ : A)
    (h : v₀⁻¹ * v₁ * v₂⁻¹ * v₃ = v₄⁻¹ * v₅) :
    v₁⁻¹ * v₅ * v₃⁻¹ * v₆ = v₀⁻¹ * v₆ * v₂⁻¹ * v₄ := by
  have key : v₁⁻¹ * v₅ * v₃⁻¹ * v₆ * (v₀⁻¹ * v₆ * v₂⁻¹ * v₄)⁻¹
      = (v₀⁻¹ * v₁ * v₂⁻¹ * v₃)⁻¹ * (v₄⁻¹ * v₅) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [h, inv_mul_cancel] at key
  exact mul_inv_eq_one.mp key

private theorem rearrange_of_mem_isMulCommutative {S : Subgroup G} [IsMulCommutative ↥S]
    {u₀ u₁ u₂ u₃ u₄ u₅ u₆ : G}
    (h₀ : u₀ ∈ S) (h₁ : u₁ ∈ S) (h₂ : u₂ ∈ S) (h₃ : u₃ ∈ S) (h₄ : u₄ ∈ S) (h₅ : u₅ ∈ S)
    (h₆ : u₆ ∈ S) (h : u₀⁻¹ * u₁ * u₂⁻¹ * u₃ = u₄⁻¹ * u₅) :
    u₁⁻¹ * u₅ * u₃⁻¹ * u₆ = u₀⁻¹ * u₆ * u₂⁻¹ * u₄ := by
  let _ : CommGroup ↥S := IsMulCommutative.instCommGroup
  have h' : (⟨u₀, h₀⟩ : ↥S)⁻¹ * ⟨u₁, h₁⟩ * (⟨u₂, h₂⟩ : ↥S)⁻¹ * ⟨u₃, h₃⟩
      = (⟨u₄, h₄⟩ : ↥S)⁻¹ * ⟨u₅, h₅⟩ := by
    apply Subtype.ext; push_cast; exact h
  have hg := rearrange_of_commGroup (⟨u₀, h₀⟩ : ↥S) ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ ⟨u₃, h₃⟩ ⟨u₄, h₄⟩
    ⟨u₅, h₅⟩ ⟨u₆, h₆⟩ h'
  have := congrArg (fun v : ↥S => (v : G)) hg
  push_cast at this
  exact this

theorem le_normalizer_commutator_of_le_normalizer {Q P₀ : Subgroup G}
    (hP₀ : P₀ ≤ normalizer (Q : Set G)) :
    P₀ ≤ normalizer ((⁅Q, P₀⁆ : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_commutator, mem_normalizer_iff_map_conj_eq.mp (hP₀ hg),
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)]

theorem comparisonWord_mem_commutator {Q P₀ : Subgroup G} {s y r₁ r₃ : G}
    (hP₀ : P₀ ≤ normalizer (Q : Set G)) (hs : s ∈ P₀) (hr₁ : r₁ ∈ P₀) (hr₃ : r₃ ∈ P₀)
    (hy : y ∈ ⁅Q, P₀⁆) : comparisonWord s y r₁ r₃ ∈ ⁅Q, P₀⁆ := by
  have hK := le_normalizer_commutator_of_le_normalizer hP₀
  have h₁ : r₃⁻¹ * y * r₃ ∈ ⁅Q, P₀⁆ := (mem_normalizer_iff''.mp (hK hr₃) y).mp hy
  have h₂ : s * y * s⁻¹ ∈ ⁅Q, P₀⁆ := (mem_normalizer_iff.mp (hK hs) y).mp hy
  have h₃ : s * r₁ * y * (s * r₁)⁻¹ ∈ ⁅Q, P₀⁆ :=
    (mem_normalizer_iff.mp (hK (mul_mem hs hr₁)) y).mp hy
  simpa [comparisonWord] using mul_mem (mul_mem (mul_mem (inv_mem h₁) h₂) (inv_mem h₃)) hy

theorem conj_comparisonWord_eq_self {Q : Subgroup G} [IsMulCommutative ↥Q] {s y r₁ r₂ r₃ : G}
    (hs : s ∈ normalizer (Q : Set G)) (hy : y ∈ ⁅Q, zpowers s⁆)
    (hr₁ : r₁ ∈ zpowers s) (hr₃ : r₃ ∈ zpowers s)
    (hword : y⁻¹ * s * y * r₂⁻¹ * (y⁻¹ * s * y) = r₃ * (y⁻¹ * s * y) ^ 2 * r₁)
    (hprod : r₁ * r₂ * r₃ = 1) :
    s * comparisonWord s y r₁ r₃ * s⁻¹ = comparisonWord s y r₁ r₃ := by
  obtain ⟨a₁, rfl⟩ := mem_zpowers_iff.mp hr₁
  obtain ⟨a₃, rfl⟩ := mem_zpowers_iff.mp hr₃
  have hsn : zpowers s ≤ normalizer (Q : Set G) := zpowers_le.mpr hs
  have hyQ : y ∈ Q := le_normalizer_iff_commutator_le_left.mp hsn hy
  have hr₂ : r₂ = s ^ (-(a₁ + a₃)) := by
    have h : r₂ = (s ^ a₁)⁻¹ * 1 * (s ^ a₃)⁻¹ := by rw [← hprod]; group
    rw [h]; group
  obtain ⟨E, hE⟩ : ∃ E : ℤ → G, ∀ k : ℤ, E k = s ^ k * y * s ^ (-k) := ⟨_, fun _ => rfl⟩
  have hEmem : ∀ k : ℤ, E k ∈ Q := by
    intro k
    rw [hE, zpow_neg]
    exact (mem_normalizer_iff.mp (hsn (zpow_mem (mem_zpowers s) k)) y).mp hyQ
  have hstar : (E 0)⁻¹ * E 1 * (E (1 + (a₁ + a₃)))⁻¹ * E (2 + (a₁ + a₃))
      = (E a₃)⁻¹ * E (a₃ + 2) := by
    have hA : y⁻¹ * s * y * (s ^ (-(a₁ + a₃)))⁻¹ * (y⁻¹ * s * y)
        = ((E 0)⁻¹ * E 1 * (E (1 + (a₁ + a₃)))⁻¹ * E (2 + (a₁ + a₃))) * s ^ (2 + (a₁ + a₃)) := by
      simp only [hE]; group
    have hB : s ^ a₃ * (y⁻¹ * s * y) ^ 2 * s ^ a₁
        = ((E a₃)⁻¹ * E (a₃ + 2)) * s ^ (2 + (a₁ + a₃)) := by
      simp only [hE, pow_two]
      group
      rw [show ((2 : ℤ)) = 1 + 1 by norm_num, zpow_add]
      group
    refine mul_right_cancel (b := s ^ (2 + (a₁ + a₃))) ?_
    rw [← hA, ← hB, ← hr₂]; exact hword
  have hstar' : (E (-a₃))⁻¹ * E (1 - a₃) * (E (a₁ + 1))⁻¹ * E (a₁ + 2) = (E 0)⁻¹ * E 2 := by
    have e₁ : (E (-a₃))⁻¹ * E (1 - a₃) * (E (a₁ + 1))⁻¹ * E (a₁ + 2)
        = s ^ (-a₃) * ((E 0)⁻¹ * E 1 * (E (1 + (a₁ + a₃)))⁻¹ * E (2 + (a₁ + a₃))) * s ^ a₃ := by
      simp only [hE]; group
    have e₂ : (E 0)⁻¹ * E 2 = s ^ (-a₃) * ((E a₃)⁻¹ * E (a₃ + 2)) * s ^ a₃ := by
      simp only [hE]; group
    rw [e₁, e₂, hstar]
  have hL : s * comparisonWord s y (s ^ a₁) (s ^ a₃) * s⁻¹
      = (E (1 - a₃))⁻¹ * E 2 * (E (a₁ + 2))⁻¹ * E 1 := by
    simp only [comparisonWord, hE]; group
  have hR : comparisonWord s y (s ^ a₁) (s ^ a₃)
      = (E (-a₃))⁻¹ * E 1 * (E (a₁ + 1))⁻¹ * E 0 := by
    simp only [comparisonWord, hE]; group
  rw [hL, hR]
  exact rearrange_of_mem_isMulCommutative (hEmem _) (hEmem _) (hEmem _) (hEmem _) (hEmem _)
    (hEmem _) (hEmem _) hstar'

theorem comparisonWord_mem_commutator_and_conj_eq_self
    {p q : ℕ} {F : Type*} [Field F] [Finite F] (S : AppendixCSetup p q F G)
    {Q : Subgroup G} [IsMulCommutative ↥Q] (_hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (_hyQ : y ∈ Q)
    (_hP₁ : Subgroup.map (MulAut.conj y⁻¹) S.P₀ ≤ normalizer (S.U : Set G))
    (hycomm : y ∈ ⁅Q, S.P₀⁆) {r₁ r₂ r₃ : G} (hr₁ : r₁ ∈ S.P₀) (_hr₂ : r₂ ∈ S.P₀)
    (hr₃ : r₃ ∈ S.P₀)
    (hword : (y⁻¹ * S.s * y) * r₂⁻¹ * (y⁻¹ * S.s * y) = r₃ * (y⁻¹ * S.s * y) ^ 2 * r₁)
    (hprod : r₁ * r₂ * r₃ = 1) :
    comparisonWord S.s y r₁ r₃ ∈ ⁅Q, S.P₀⁆ ∧
      S.s * comparisonWord S.s y r₁ r₃ * S.s⁻¹ = comparisonWord S.s y r₁ r₃ := by
  refine ⟨comparisonWord_mem_commutator hQnorm S.s_mem_P₀ hr₁ hr₃ hycomm, ?_⟩
  rw [S.P₀_eq_zpowers] at hQnorm hycomm hr₁ hr₃
  exact conj_comparisonWord_eq_self (hQnorm (mem_zpowers _)) hycomm hr₁ hr₃ hword hprod

end CFSG.FeitThompson
