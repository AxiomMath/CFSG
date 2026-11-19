module

public import CFSG.GH74.QTGen4.U42.U0CoreE

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5

theorem card_le_32_of_normalized_Bc {X : Subgroup Mc} (hXT : X ≤ Thc)
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hXV : ¬ Wc ≤ X) :
    Nat.card X ≤ 32 := by
  have hK := right_InK4 hXT hXB
  let ρ : X →* Equiv.Perm (Fin 5) :=
    (SemidirectProduct.rightHom : Mc →* Equiv.Perm (Fin 5)).comp X.subtype
  have hmem : ∀ n : ρ.ker, ((n : X) : Mc).left ∈ W3 := by
    intro n
    have hn1 : ((n : X) : Mc).right = 1 := MonoidHom.mem_ker.mp n.2
    exact mem_W3.mpr (left_mem_W3_of_right_one hXB hXV (n : X).2 hn1)
  have hker : Nat.card ρ.ker ≤ 8 := by
    rw [← card_W3]
    refine Nat.card_le_card_of_injective
      (fun n : ρ.ker => (⟨((n : X) : Mc).left, hmem n⟩ : W3)) ?_
    intro n m hnm
    have hl : ((n : X) : Mc).left = ((m : X) : Mc).left := congrArg Subtype.val hnm
    have hn1 : ((n : X) : Mc).right = 1 := MonoidHom.mem_ker.mp n.2
    have hm1 : ((m : X) : Mc).right = 1 := MonoidHom.mem_ker.mp m.2
    exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hl (hn1.trans hm1.symm)))
  have hrmem : ∀ σ : ρ.range, InK4 (σ : Equiv.Perm (Fin 5)) := by
    intro σ
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp σ.2
    rw [← hx]
    exact hK (x : Mc) x.2
  have hrange : Nat.card ρ.range ≤ 4 := by
    have h := Nat.card_le_card_of_injective
      (fun σ : ρ.range => (⟨(σ : Equiv.Perm (Fin 5)), hrmem σ⟩ : {σ // InK4 σ})) (by
        intro a b hab
        exact Subtype.ext (congrArg (fun t : {σ : Equiv.Perm (Fin 5) // InK4 σ} => t.val) hab))
    have h4 : Nat.card {σ : Equiv.Perm (Fin 5) // InK4 σ} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rwa [h4] at h
  have hprod := Subgroup.card_ker_mul_card_range ρ
  calc
    Nat.card X = Nat.card ρ.ker * Nat.card ρ.range := hprod.symm
    _ ≤ 8 * 4 := Nat.mul_le_mul hker hrange
    _ = 32 := rfl

theorem K4_orbit_injective : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ ≠ 1 →
    Function.Injective (fun i : Fin 4 =>
      (![1, σ, c3p * σ * c3p⁻¹, c3p ^ 2 * σ * (c3p ^ 2)⁻¹] : Fin 4 → Equiv.Perm (Fin 5)) i) := by
  decide +kernel

theorem not_Wc_le_of_card32_normalized_Bc {X : Subgroup Mc} (hXT : X ≤ Thc)
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hX : Nat.card X = 32) :
    ¬ Wc ≤ X := by
  intro hW
  let ρ : X →* Equiv.Perm (Fin 5) :=
    (SemidirectProduct.rightHom : Mc →* Equiv.Perm (Fin 5)).comp X.subtype
  have hK := right_InK4 hXT hXB
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ X, x.right ≠ 1 := by
    by_contra hn
    push Not at hn
    have hc : Nat.card X ≤ Nat.card W5 := Nat.card_le_card_of_injective
      (fun x : X => (x : Mc).left) (by
        intro a b hab
        exact Subtype.ext (SemidirectProduct.ext hab ((hn a a.2).trans (hn b b.2).symm)))
    rw [hX, CFSG.Quasithin.H13.A5.card_W5] at hc
    omega
  have hker : 16 ≤ Nat.card ρ.ker := by
    rw [← CFSG.Quasithin.H13.A5.card_W5]
    refine Nat.card_le_card_of_injective
      (fun w : W5 => (⟨⟨SemidirectProduct.inl w, hW ⟨w, rfl⟩⟩,
        by change (SemidirectProduct.inl w : Mc).right = 1; rfl⟩ : ρ.ker)) ?_
    intro a b hab
    exact congrArg (fun y : ρ.ker => ((y : X) : Mc).left) hab
  have hc : c3p.sign = 1 ∧ c3p 4 = 4 ∧ (c3p ^ 2).sign = 1 ∧ (c3p ^ 2) 4 = 4 := by
    decide +kernel
  let x0 : X := ⟨x, hx⟩
  let x1 : X := ⟨SemidirectProduct.inr c3p * x * (SemidirectProduct.inr c3p)⁻¹,
    conjB_mem hXB hx c3p hc.1 hc.2.1⟩
  let x2 : X := ⟨SemidirectProduct.inr (c3p ^ 2) * x * (SemidirectProduct.inr (c3p ^ 2))⁻¹,
    conjB_mem hXB hx (c3p ^ 2) hc.2.2.1 hc.2.2.2⟩
  let f : Fin 4 → ρ.range := ![
    ⟨1, ρ.range.one_mem⟩,
    ⟨x.right, ⟨x0, rfl⟩⟩,
    ⟨c3p * x.right * c3p⁻¹, ⟨x1, conjB_right x c3p⟩⟩,
    ⟨c3p ^ 2 * x.right * (c3p ^ 2)⁻¹, ⟨x2, conjB_right x (c3p ^ 2)⟩⟩]
  have hf : Function.Injective f := by
    intro i j hij
    apply K4_orbit_injective x.right (hK x hx) hx1
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> exact h
  have hrange : 4 ≤ Nat.card ρ.range := by
    have h := Nat.card_le_card_of_injective f hf
    simpa using h
  have hprod := Subgroup.card_ker_mul_card_range ρ
  rw [hX] at hprod
  have h64 : 64 ≤ Nat.card ρ.ker * Nat.card ρ.range := by
    exact Nat.mul_le_mul hker hrange
  omega

end CFSG.GH74.QTGen4.U42
