module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Per

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

theorem centralizes_of_quotEquivTo {Γ : Type} [Group Γ] [Finite Γ] {H M N Q : Subgroup Γ}
    (hMH : M ≤ H) (hQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (h : QuotEquivTo M N (alternatingGroup (Fin 6)))
    (hcard : Nat.card (MulAut ↥Q) < 360) (hN : ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n) :
    ∀ m ∈ M, ∀ q ∈ Q, m * q = q * m := by
  intro m hm q hq
  let ρ : ↥M →* MulAut ↥Q :=
    MonoidHom.mk' (fun a =>
      { toFun := fun x => ⟨(a : Γ) * x * (a : Γ)⁻¹, hQ a (hMH a.2) x x.2⟩
        invFun := fun x => ⟨(a : Γ)⁻¹ * x * (a : Γ), by
          simpa using hQ (a : Γ)⁻¹ (inv_mem (hMH a.2)) x x.2⟩
        left_inv := by
          intro x
          apply Subtype.ext
          simp only
          group
        right_inv := by
          intro x
          apply Subtype.ext
          simp only
          group
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group }) (by
      intro a b
      ext x
      rw [MulAut.mul_apply]
      change (↑(a * b) : Γ) * (x : Γ) * (↑(a * b) : Γ)⁻¹ =
        (a : Γ) * ((b : Γ) * (x : Γ) * (b : Γ)⁻¹) * (a : Γ)⁻¹
      rw [Subgroup.coe_mul]
      group)
  obtain ⟨n, hn, hρ⟩ := exists_eq_of_quotEquivTo_card_lt h ρ hcard ⟨m, hm⟩
  have hmain : m * q * m⁻¹ = (n : Γ) * q * (n : Γ)⁻¹ := by
    have h1 := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : Γ)) hρ
    change m * q * m⁻¹ = (n : Γ) * q * (n : Γ)⁻¹ at h1
    exact h1
  have hnq : (n : Γ) * q * (n : Γ)⁻¹ = q := by
    rw [hN (n : Γ) hn q hq]
    group
  have hmul : m * q * m⁻¹ = q := by rw [hmain, hnq]
  calc m * q = (m * q * m⁻¹) * m := by group
    _ = q * m := by rw [hmul]

theorem commute_of_central {Γ : Type} [Group Γ] [Finite Γ] {M1 M2 P : Subgroup Γ}
    (hPM2 : P ≤ M2) (hcomm : ∀ a ∈ M1, ∀ b ∈ M2, a * b * a⁻¹ * b⁻¹ ∈ P)
    (hPc : ∀ p ∈ P, ∀ m ∈ M1 ⊔ M2, m * p = p * m)
    (hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (h2 : QuotEquivTo M2 P (alternatingGroup (Fin 6))) :
    ∀ a ∈ M1, ∀ b ∈ M2, a * b = b * a := by
  intro a ha b hb
  have hsup1 : M1 ≤ M1 ⊔ M2 := le_sup_left
  have hsup2 : M2 ≤ M1 ⊔ M2 := le_sup_right
  have hPcomm' : ∀ p q : ↥P, p * q = q * p := fun p q => Subtype.ext (hPcomm p p.2 q q.2)
  let F : ↥M2 → ↥P :=
    fun b => ⟨a * (b : Γ) * a⁻¹ * (b : Γ)⁻¹, hcomm a ha (b : Γ) b.2⟩
  have hmul : ∀ b b' : ↥M2, F (b * b') = F b * F b' := by
    intro b b'
    apply Subtype.ext
    change a * ((b : Γ) * (b' : Γ)) * a⁻¹ * ((b : Γ) * (b' : Γ))⁻¹ =
      (a * (b : Γ) * a⁻¹ * (b : Γ)⁻¹) * (a * (b' : Γ) * a⁻¹ * (b' : Γ)⁻¹)
    have hbp : (b : Γ) * (a * (b' : Γ) * a⁻¹ * (b' : Γ)⁻¹) =
        (a * (b' : Γ) * a⁻¹ * (b' : Γ)⁻¹) * (b : Γ) :=
      hPc _ (hcomm a ha (b' : Γ) b'.2) _ (hsup2 b.2)
    calc a * ((b : Γ) * (b' : Γ)) * a⁻¹ * ((b : Γ) * (b' : Γ))⁻¹
        = (a * (b : Γ) * a⁻¹ * (b : Γ)⁻¹) *
            ((b : Γ) * (a * (b' : Γ) * a⁻¹ * (b' : Γ)⁻¹) * (b : Γ)⁻¹) := by group
      _ = (a * (b : Γ) * a⁻¹ * (b : Γ)⁻¹) * (a * (b' : Γ) * a⁻¹ * (b' : Γ)⁻¹) := by
            rw [hbp]; group
  let g : ↥M2 →* ↥P := MonoidHom.mk' F hmul
  obtain ⟨n, hn, hgn⟩ := exists_eq_of_quotEquivTo_comm h2 g hPcomm' ⟨b, hb⟩
  have hna : a * (n : Γ) = (n : Γ) * a := hPc (n : Γ) hn a (hsup1 ha)
  have hgn1 : g n = 1 := by
    apply Subtype.ext
    change a * (n : Γ) * a⁻¹ * (n : Γ)⁻¹ = 1
    rw [hna]
    group
  have hgb1 : g ⟨b, hb⟩ = 1 := by rw [hgn, hgn1]
  have hval : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h1 := congrArg (fun x : ↥P => (x : Γ)) hgb1
    change (F ⟨b, hb⟩ : Γ) = 1 at h1
    change (F ⟨b, hb⟩ : Γ) = 1
    exact h1
  have h1 : (a * b) * (b * a)⁻¹ = 1 := by
    rw [mul_inv_rev]
    calc a * b * (a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by group
      _ = 1 := hval
  exact mul_inv_eq_one.mp h1

theorem exists_involution_of_quotEquivTo {Γ : Type} [Group Γ] [Finite Γ] {M N : Subgroup Γ}
    (h : QuotEquivTo M N (alternatingGroup (Fin 6))) (hodd : Odd (Nat.card N)) :
    ∃ x ∈ M, x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨φ, hφ, hk⟩ := h
  let g : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    change (g : Equiv.Perm (Fin 6)) * (g : Equiv.Perm (Fin 6)) = 1
    ext i
    fin_cases i <;> decide
  have hg1 : g ≠ 1 := by
    intro hcon
    have h0 : (g : Equiv.Perm (Fin 6)) 0 = (1 : Equiv.Perm (Fin 6)) 0 :=
      congrArg (fun x : alternatingGroup (Fin 6) => (x : Equiv.Perm (Fin 6)) 0) hcon
    revert h0
    decide
  obtain ⟨m, hm⟩ := hφ g
  have hmm_ker : m * m ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hm]
    exact hg2
  have hmmN : ((m * m : ↥M) : Γ) ∈ N := by
    rw [← Subgroup.mem_subgroupOf, ← hk]
    exact hmm_ker
  have hpowN : ((m * m : ↥M) : Γ) ^ Nat.card N = 1 := by
    have hx : (⟨((m * m : ↥M) : Γ), hmmN⟩ : ↥N) ^ Nat.card N = 1 :=
      pow_card_eq_one'
    have hx' := congrArg (fun x : ↥N => (x : Γ)) hx
    rw [Subgroup.coe_pow, Subgroup.coe_one] at hx'
    simpa using hx'
  refine ⟨(m : Γ) ^ Nat.card N, pow_mem m.2 (Nat.card N), ?_, ?_⟩
  · have hm2 : ((m * m : ↥M) : Γ) = (m : Γ) * (m : Γ) := by simp
    rw [← pow_add, ← two_mul, pow_mul, pow_two, ← hm2]
    exact hpowN
  · intro hx1
    have hmk1 : m ^ Nat.card N = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hx1
    have hφg : φ (m ^ Nat.card N) = g := by
      rw [map_pow, hm]
      obtain ⟨j, hj⟩ := hodd
      rw [hj, pow_succ, pow_mul, show g ^ 2 = 1 by rw [pow_two]; exact hg2]
      simp
    rw [hmk1, map_one] at hφg
    exact hg1 hφg.symm

end C10

end CFSG.OddStandard.SmallF3.Omega
