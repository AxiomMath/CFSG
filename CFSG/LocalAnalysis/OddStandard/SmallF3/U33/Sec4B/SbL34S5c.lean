module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem false_of_conj_in_coset (P V S : Subgroup G) (t : G) (hP : Nat.card P = 2 ^ 10)
    (hP2 : IsPGroup 2 P) (hV : Nat.card V = 4)
    (hS : S ≤ centralizer ({t} : Set G))
    (hSodd : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) (hS7 : Nat.card S = 2 ^ 7)
    (h : ∀ p ∈ P, p * t * p⁻¹ ∈ t • (V : Set G)) : False := by
  classical
  let K : Subgroup G := centralizer ({t} : Set G)
  let C : Subgroup G := P ⊓ K
  have hcard_smul : Nat.card ↥(t • (V : Set G)) = 4 := by
    have e : V ≃ ↥(t • (V : Set G)) :=
      { toFun := fun v => ⟨t * (v : G), Set.mem_smul_set.mpr ⟨(v : G), v.2, rfl⟩⟩
        invFun := fun x => ⟨t⁻¹ * (x : G), by
          obtain ⟨v, hv, hvx⟩ := Set.mem_smul_set.mp x.2
          rw [← hvx]
          change t⁻¹ * (t * v) ∈ V
          simpa using hv⟩
        left_inv := fun v => by
          apply Subtype.ext
          change t⁻¹ * (t * (v : G)) = (v : G)
          simp
        right_inv := fun x => by
          apply Subtype.ext
          change t * (t⁻¹ * (x : G)) = (x : G)
          simp }
    rw [← Nat.card_congr e, hV]
  let r : ↥(t • (V : Set G)) → P := fun x =>
    if hx : ∃ p : P, (p : G) * t * (p : G)⁻¹ = (x : G) then hx.choose else 1
  have hr : ∀ (x : ↥(t • (V : Set G)))
      (hx : ∃ p : P, (p : G) * t * (p : G)⁻¹ = (x : G)),
      (r x : G) * t * (r x : G)⁻¹ = (x : G) := by
    intro x hx
    dsimp only [r]
    rw [dif_pos hx]
    exact hx.choose_spec
  let xm : P → ↥(t • (V : Set G)) := fun p => ⟨(p : G) * t * (p : G)⁻¹, h (p : G) p.2⟩
  have hxm : ∀ p : P, (r (xm p) : G) * t * (r (xm p) : G)⁻¹ =
      (p : G) * t * (p : G)⁻¹ := fun p => hr (xm p) ⟨p, rfl⟩
  have hcK : ∀ p : P, (p : G)⁻¹ * (r (xm p) : G) ∈ K := by
    intro p
    have hconj : ((p : G)⁻¹ * (r (xm p) : G)) * t *
        ((p : G)⁻¹ * (r (xm p) : G))⁻¹ = t := by
      rw [show (p : G)⁻¹ * ↑(r (xm p)) * t * ((p : G)⁻¹ * ↑(r (xm p)))⁻¹
            = (p : G)⁻¹ * (↑(r (xm p)) * t * (↑(r (xm p)))⁻¹) * (p : G) by group]
      rw [hxm p]
      group
    have hct : ((p : G)⁻¹ * (r (xm p) : G)) * t =
        t * ((p : G)⁻¹ * (r (xm p) : G)) := by
      have := congrArg (fun z => z * ((p : G)⁻¹ * (r (xm p) : G))) hconj
      simpa [mul_assoc] using this
    change ((p : G)⁻¹ * (r (xm p) : G)) ∈ centralizer ({t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hct
  let Φ : P → C × ↥(t • (V : Set G)) := fun p =>
    (⟨(p : G)⁻¹ * (r (xm p) : G),
      Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem p.2) (r (xm p)).2, hcK p⟩⟩, xm p)
  have hΦinj : Function.Injective Φ := by
    intro p p' hp
    have h2 : xm p = xm p' := congrArg Prod.snd hp
    have h1c : ((Φ p).1 : C) = ((Φ p').1 : C) := congrArg Prod.fst hp
    have h1 : (p : G)⁻¹ * (r (xm p) : G) = (p' : G)⁻¹ * (r (xm p') : G) := by
      have := congrArg (fun z : C => (z : G)) h1c
      dsimp only [Φ] at this
      exact this
    have hr_eq : r (xm p) = r (xm p') := congrArg r h2
    rw [hr_eq] at h1
    have hinv : (p : G)⁻¹ = (p' : G)⁻¹ := mul_right_cancel h1
    exact Subtype.ext (inv_injective hinv)
  have hcardP : Nat.card P ≤ Nat.card C * 4 := by
    have := Nat.card_le_card_of_injective Φ hΦinj
    rwa [Nat.card_prod, hcard_smul] at this
  have hC2 : IsPGroup 2 C := hP2.to_le inf_le_left
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hC_dvd_K : Nat.card C ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
  have hK_eq : Nat.card K = S.relIndex K * Nat.card S := by
    rw [← Subgroup.relIndex_mul_card (H := S) (K := K), inf_eq_left.mpr hS]
  have hC_dvd : Nat.card C ∣ S.relIndex K * 2 ^ 7 := by
    rw [hK_eq, hS7] at hC_dvd_K
    exact hC_dvd_K
  have hcop2 : Nat.Coprime 2 (S.relIndex K) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hSodd
  have hcop : Nat.Coprime (Nat.card C) (S.relIndex K) := by
    rw [hk]
    exact hcop2.pow_left k
  have hC_dvd27 : Nat.card C ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_left hC_dvd
  have hle27 : Nat.card C ≤ 2 ^ 7 := Nat.le_of_dvd (by norm_num) hC_dvd27
  have h256 : 2 ^ 8 ≤ Nat.card C := by
    have h10 : 2 ^ 10 ≤ Nat.card C * 4 := by
      rw [← hP]
      exact hcardP
    have h1024 : 1024 ≤ Nat.card C * 4 := by
      norm_num at h10
      exact h10
    have hgoal : (2 : ℕ) ^ 8 = 256 := by norm_num
    omega
  exact absurd (le_trans h256 hle27) (by norm_num)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
