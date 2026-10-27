module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Lemma1

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem torusElt_pow (i : Fin Tag.E8.rank) (u : Kˣ) (n : ℕ) :
    (torusElt Tag.E8 K i u) ^ n = torusElt Tag.E8 K i (u ^ n) := by
  induction n with
  | zero => simp [torusElt_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, torusElt_mul]

theorem torus_pow_card_sub_one [Finite K] {t : ModGL Tag.E8 K} (ht : t ∈ torusGroup Tag.E8 K) :
    t ^ (Nat.card K - 1) = 1 := by
  haveI := Fintype.ofFinite K
  have hq : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hgen : ∀ (i : Fin Tag.E8.rank) (u : Kˣ), (torusElt Tag.E8 K i u) ^ (Nat.card K - 1) = 1 := by
    intro i u
    rw [torusElt_pow]
    have : u ^ (Nat.card K - 1) = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, hq, FiniteField.pow_card_sub_one_eq_one _ u.ne_zero,
        Units.val_one]
    rw [this, torusElt_one]
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    exact hgen i u
  | one => exact one_pow _
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (torus_comm K hx hy) _), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem pow_mul_mem_X2 {x t : ModGL Tag.E8 K} (hx : x ∈ X2 K) (ht : t ∈ torusGroup Tag.E8 K)
    (n : ℕ) : ∃ y ∈ X2 K, (x * t) ^ n = y * t ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, h⟩ := ih
    refine ⟨y * (t ^ n * x * (t ^ n)⁻¹), mul_mem hy ?_, ?_⟩
    · have hn : t ^ n ∈ Subgroup.normalizer (X2 K : Set (ModGL Tag.E8 K)) :=
        pow_mem (torus_le_normalizer_X2 K ht) n
      exact (Subgroup.mem_normalizer_iff.1 hn x).1 hx
    · rw [pow_succ, h, pow_succ]
      group

theorem pinnedX_pow (α : Fin Tag.E8.rank → ℤ) (c : K) (n : ℕ) :
    (pinnedX Tag.E8 K α c) ^ n = pinnedX Tag.E8 K α (n • c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, ← pinnedX_add, succ_nsmul]

theorem pow_char_eq_one_of_mem_conjSub {g₀ b : ModGL Tag.E8 K} {α : Fin Tag.E8.rank → ℤ}
    (hb : b ∈ conjSub g₀ (rootSubgroup Tag.E8 K α)) : b ^ (ringChar K) = 1 := by
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hb)
  have hb' : b = g₀ * pinnedX Tag.E8 K α c * g₀⁻¹ := by rw [hc]; group
  rw [hb', conj_pow, pinnedX_pow]
  have : (ringChar K) • c = 0 := by
    rw [nsmul_eq_mul, CharP.cast_eq_zero K (ringChar K), zero_mul]
  rw [this, pinnedX_zero]
  group

theorem mem_X2_of_pow_eq_one [Finite K] {b : ModGL Tag.E8 K}
    (hb : b ∈ torusGroup Tag.E8 K ⊔ X2 K) (hbp : b ^ (ringChar K) = 1) : b ∈ X2 K := by
  haveI := Fintype.ofFinite K
  have hb' : b ∈ ((X2 K ⊔ torusGroup Tag.E8 K : Subgroup (ModGL Tag.E8 K)) :
      Set (ModGL Tag.E8 K)) := by
    rw [sup_comm]
    exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (X2 K) (torusGroup Tag.E8 K)
    (torus_le_normalizer_X2 K)] at hb'
  obtain ⟨x, hx, t, ht, rfl⟩ := hb'
  obtain ⟨y, hy, hxt⟩ := pow_mul_mem_X2 K hx ht (ringChar K)
  rw [hbp] at hxt
  have htp : t ^ ringChar K ∈ X2 K := by
    have : t ^ ringChar K = y⁻¹ := eq_inv_of_mul_eq_one_right hxt.symm
    rw [this]
    exact inv_mem hy
  obtain ⟨n, hp, hq⟩ := FiniteField.card K (ringChar K)
  have hq' : Nat.card K = (ringChar K) ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hq
  have hcop : Nat.Coprime (ringChar K) (Nat.card K - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_
    have hpq : ringChar K ∣ Nat.card K := by
      rw [hq']
      exact dvd_pow_self _ n.ne_zero
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h1 := Nat.dvd_sub hpq hdvd
    have : Nat.card K - (Nat.card K - 1) = 1 := by omega
    rw [this] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hord : orderOf t ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (torus_pow_card_sub_one K ht)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (hcop.coprime_dvd_right hord)
  have ht2 : t ∈ X2 K := by
    rw [← hm]
    exact pow_mem htp m
  exact mul_mem hx ht2

theorem conjSub_Uθ_le_X2 [Finite K] {g₀ : ModGL Tag.E8 K} (hg₀ : g₀ ∈ adjointGroup Tag.E8 K)
    (hcomm : ∀ b ∈ conjSub g₀ (Uθ Tag.E8 K), ∀ x ∈ X1 K, b * x = x * b) :
    conjSub g₀ (Uθ Tag.E8 K) ≤ X2 K := by
  intro b hb
  have hbG : b ∈ adjointGroup Tag.E8 K := by
    have h1 := mem_conjSub_iff.1 hb
    have h2 : g₀⁻¹ * b * g₀ ∈ adjointGroup Tag.E8 K := rootSubgroup_le_adjointGroup _ h1
    have : b = g₀ * (g₀⁻¹ * b * g₀) * g₀⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hg₀ h2) (inv_mem hg₀)
  exact mem_X2_of_pow_eq_one K (centralizer_X1_le K hbG (hcomm b hb))
    (pow_char_eq_one_of_mem_conjSub K hb)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
