module

public import CFSG.ClassicalInvolution.Q3.TL4ConnBendCom
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem coord_commutator_val (z w : hermitianUnipotentCoord J) :
    ((z * w * z⁻¹ * w⁻¹ : hermitianUnipotentCoord J) : K × K) =
      (0, w.1.1 * J.conj z.1.1 - z.1.1 * J.conj w.1.1) := by
  change ((hermitianUnipotentMul J (hermitianUnipotentMul J (hermitianUnipotentMul J z w)
      (hermitianUnipotentInv J z)) (hermitianUnipotentInv J w) : hermitianUnipotentCoord J) :
    K × K) = _
  apply Prod.ext
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    ring
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    rw [map_neg, map_neg]
    linear_combination z.2 + w.2

theorem coord_mul_val (z w : hermitianUnipotentCoord J) :
    ((z * w : hermitianUnipotentCoord J) : K × K) =
      (z.1.1 + w.1.1, z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1) := rfl

theorem coord_one_val : ((1 : hermitianUnipotentCoord J) : K × K) = (0, 0) := rfl

variable [Finite K] [CharP K 2]

theorem exists_coord_snd {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q) (c : K) :
    ∃ d : K, d + J.conj d + c * J.conj c = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let τ : K →+ K := AddMonoidHom.mk' (fun d => d + J.conj d) (fun x y => by
    rw [map_add]
    ring)
  have hker : ∀ d, τ d = 0 ↔ J.conj d = d := by
    intro d
    change d + J.conj d = 0 ↔ J.conj d = d
    constructor
    · intro h
      linear_combination h - d * h2
    · intro h
      rw [h]
      linear_combination d * h2
  have hrange : ∀ d, J.conj (τ d) = τ d := by
    intro d
    change J.conj (d + J.conj d) = d + J.conj d
    rw [map_add, J.conj_involutive d, add_comm]
  have hkercard : Nat.card τ.ker = q := by
    rw [← hfix]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun d => hker d)
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup τ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange τ).toEquiv, hkercard, hK] at hmul
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · exfalso
      rw [h0] at hK
      have : 0 < Nat.card K := Nat.card_pos
      simp at hK
      omega
    · exact h0
  have hrc : Nat.card τ.range = q := by
    have : q * q = Nat.card τ.range * q := by rw [← hmul]; ring
    exact (Nat.eq_of_mul_eq_mul_right hq0 this).symm
  let ι : τ.range → {x : K // J.conj x = x} := fun y => ⟨y, by
    obtain ⟨d, hd⟩ := y.2
    rw [← hd]
    exact hrange d⟩
  have hι : Function.Injective ι := fun y y' h =>
    Subtype.ext (congrArg (fun w : {x : K // J.conj x = x} => (w : K)) h)
  have hbij : Function.Bijective ι :=
    hι.bijective_of_nat_card_le (by rw [hfix, hrc])
  obtain ⟨⟨_, ⟨d, rfl⟩⟩, hd⟩ := hbij.2 ⟨c * J.conj c, by
    rw [map_mul, J.conj_involutive c, mul_comm]⟩
  refine ⟨d, ?_⟩
  have hd' : d + J.conj d = c * J.conj c := congrArg Subtype.val hd
  rw [hd']
  linear_combination (c * J.conj c) * h2

theorem coord_bigComm {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q) (hq : 4 ≤ q) :
    BigCommT (hermitianUnipotentCoord J) := by
  classical
  intro x z hxz y
  by_cases ha : x.1.1 = 0
  · apply Subtype.ext
    rw [coord_mul_val, coord_mul_val, ha, map_zero, mul_zero, zero_mul, sub_zero, sub_zero,
      zero_add, add_zero, add_comm y.1.2]
  exfalso
  set a := x.1.1 with hadef
  have hN : a * J.conj a ≠ 0 := mul_ne_zero ha ((map_ne_zero J.conj).mpr ha)
  have hy : ∀ l : K, ∃ w : hermitianUnipotentCoord J, w.1.1 = l * a := by
    intro l
    obtain ⟨d, hd⟩ := exists_coord_snd J hK hfix (l * a)
    exact ⟨⟨(l * a, d), by simpa using hd⟩, rfl⟩
  choose w hw using hy
  have hval : ∀ l : K, ((x * w l * x⁻¹ * (w l)⁻¹ : hermitianUnipotentCoord J) : K × K) =
      (0, (l - J.conj l) * (a * J.conj a)) := by
    intro l
    rw [coord_commutator_val, hw l, map_mul]
    ext
    · rfl
    · simp only [← hadef]
      ring
  have hfixd : ∀ l : K, (l - J.conj l) * (a * J.conj a) = 0 ↔ J.conj l = l := by
    intro l
    rw [mul_eq_zero, or_iff_left hN, sub_eq_zero, eq_comm]
  have hsame : ∀ l₁ l₂ : K, J.conj l₁ ≠ l₁ → J.conj l₂ ≠ l₂ → J.conj (l₁ - l₂) = l₁ - l₂ := by
    intro l₁ l₂ h₁ h₂
    have hz : ∀ l, J.conj l ≠ l → x * w l * x⁻¹ * (w l)⁻¹ = z := by
      intro l hl
      refine (hxz (w l)).resolve_left fun h1 => hl ?_
      have := congrArg Subtype.val h1
      rw [hval l, coord_one_val] at this
      exact (hfixd l).mp (Prod.ext_iff.mp this).2
    have heq := congrArg Subtype.val ((hz l₁ h₁).trans (hz l₂ h₂).symm)
    rw [hval, hval] at heq
    have h2 := (Prod.ext_iff.mp heq).2
    have h3 : ((l₁ - l₂) - J.conj (l₁ - l₂)) * (a * J.conj a) = 0 := by
      rw [map_sub]
      linear_combination h2
    exact (hfixd _).mp h3
  have hcard : Nat.card K ≤ 2 * q := by
    by_cases hex : ∃ l₁ : K, J.conj l₁ ≠ l₁
    · obtain ⟨l₁, hl₁⟩ := hex
      let f : K → Bool × {x : K // J.conj x = x} := fun l =>
        if hl : J.conj l = l then (false, ⟨l, hl⟩)
        else (true, ⟨l - l₁, hsame l l₁ hl hl₁⟩)
      have hf : Function.Injective f := by
        intro l l' hll'
        by_cases hl : J.conj l = l <;> by_cases hl' : J.conj l' = l' <;>
          simp only [f, hl, hl', dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
            Bool.false_eq_true, Bool.true_eq_false, false_and] at hll'
        · exact hll'.2
        · linear_combination hll'.2
      have := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod, hfix, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
      exact this
    · push Not at hex
      have := Nat.card_le_card_of_injective (fun l : K => (⟨l, hex l⟩ : {x : K // J.conj x = x}))
        (fun l l' h => congrArg Subtype.val h)
      rw [hfix] at this
      omega
  rw [hK] at hcard
  have : q * q ≤ 2 * q := by nlinarith
  have := Nat.le_of_mul_le_mul_right this (by omega)
  omega

end CFSG.ClassicalInvolution.Q3.TL4.Bend
