module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec124_z4_comm {V : Subgroup G} (hV : IsZ4Pow4 V) : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
  obtain ⟨e⟩ := hV
  intro v hv w hw
  have h : (⟨v, hv⟩ : ↥V) * ⟨w, hw⟩ = ⟨w, hw⟩ * ⟨v, hv⟩ :=
    e.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

theorem sec124_z4_pow_four {V : Subgroup G} (hV : IsZ4Pow4 V) : ∀ v ∈ V, v ^ 4 = 1 := by
  obtain ⟨e⟩ := hV
  intro v hv
  have h : (⟨v, hv⟩ : ↥V) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    generalize e ⟨v, hv⟩ i = a
    revert a
    decide
  simpa using congrArg Subtype.val h

theorem sec124_z4_mem_of_sq {V B : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB16 : Nat.card B = 2 ^ 4) (hB2 : ∀ b ∈ B, b * b = 1) :
    ∀ v ∈ V, v * v = 1 → v ∈ B := by
  obtain ⟨e⟩ := hV
  have hcard : Nat.card {v : ↥V // v * v = 1} = 2 ^ 4 := by
    have hequiv : {v : ↥V // v * v = 1} ≃ {x : Fin 4 → Multiplicative (ZMod 4) // x * x = 1} :=
      e.toEquiv.subtypeEquiv (fun v => by
        constructor
        · intro h
          rw [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, h, map_one]
        · intro h
          apply e.injective
          rw [map_mul, map_one]
          exact h)
    rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card]
    decide +kernel
  let ι : ↥B → {v : ↥V // v * v = 1} := fun b =>
    ⟨⟨b, hBV b.2⟩, Subtype.ext (by simpa using hB2 b b.2)⟩
  have hι : Function.Injective ι := by
    intro b b' h
    apply Subtype.ext
    simpa [ι] using congrArg (fun x : {v : ↥V // v * v = 1} => ((x : ↥V) : G)) h
  haveI : Finite {v : ↥V // v * v = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le (by rw [hcard, hB16])
  intro v hv hv2
  obtain ⟨b, hb⟩ := hbij.2 ⟨⟨v, hv⟩, Subtype.ext (by simpa using hv2)⟩
  have hbv : (b : G) = v := by
    simpa [ι] using congrArg (fun x : {v : ↥V // v * v = 1} => ((x : ↥V) : G)) hb
  rw [← hbv]
  exact b.2

theorem sec124_z4_sq_mem {V B : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB16 : Nat.card B = 2 ^ 4) (hB2 : ∀ b ∈ B, b * b = 1) :
    ∀ v ∈ V, v * v ∈ B := by
  intro v hv
  refine sec124_z4_mem_of_sq hV hBV hB16 hB2 (v * v) (V.mul_mem hv hv) ?_
  have h4 := sec124_z4_pow_four hV v hv
  calc v * v * (v * v) = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h4

theorem sec124_z4_root {V B : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB2 : ∀ b ∈ B, b * b = 1) : ∀ b ∈ B, ∃ x ∈ V, x * x = b := by
  obtain ⟨e⟩ := hV
  intro b hb
  have hy : e ⟨b, hBV hb⟩ * e ⟨b, hBV hb⟩ = 1 := by
    rw [← map_mul]
    have h : (⟨b, hBV hb⟩ : ↥V) * ⟨b, hBV hb⟩ = 1 := Subtype.ext (by simpa using hB2 b hb)
    rw [h, map_one]
  let g : Multiplicative (ZMod 4) → Multiplicative (ZMod 4) :=
    fun a => if a = 1 then 1 else Multiplicative.ofAdd 1
  have hg : ∀ a : Multiplicative (ZMod 4), a * a = 1 → g a * g a = a := by
    decide
  let x : ↥V := e.symm (fun i => g (e ⟨b, hBV hb⟩ i))
  refine ⟨x, x.2, ?_⟩
  have hx : x * x = ⟨b, hBV hb⟩ := by
    apply e.injective
    rw [map_mul]
    simp only [x, MulEquiv.apply_symm_apply]
    funext i
    simp only [Pi.mul_apply]
    exact hg _ (by simpa using congrFun hy i)
  exact congrArg Subtype.val hx

end CFSG.OddStandard.SmallF3.Omega
