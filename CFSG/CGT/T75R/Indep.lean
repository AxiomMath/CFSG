module

public import CFSG.CGT.T75R.SPrime

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eight_le_card_of_indep [Finite G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    {a b c : G} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hc1 : c ≠ 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (habc : c ≠ a * b) :
    8 ≤ Nat.card E := by
  classical
  have hcomm := hE.1
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hE.2 x hx
    rwa [pow_two] at this
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => hcomm.is_comm.comm x y }
  have hsq : ∀ x : E, x * x = 1 := fun x => Subtype.ext (hE2 x x.2)
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) (fun x => by
    show (2 : ℕ) • x = 0
    apply Additive.toMul.injective
    simp [pow_two, hsq (Additive.toMul x)])
  let a' : Additive E := Additive.ofMul ⟨a, ha⟩
  let b' : Additive E := Additive.ofMul ⟨b, hb⟩
  let c' : Additive E := Additive.ofMul ⟨c, hc⟩
  let v : Fin 3 → Additive E := ![a', b', c']
  have hinv : ∀ x y : G, x ∈ E → y ∈ E → x * y = 1 → x = y := by
    intro x y hx hy hxy
    have := hE2 x hx
    have h2 : y = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact (mul_eq_one_comm.1 hxy)
    rw [h2, inv_eq_of_mul_eq_one_right this]
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_three] at hg
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hg
    have key : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
      rcases hz (g 0) with h0 | h0 <;> rcases hz (g 1) with h1 | h1 <;>
        rcases hz (g 2) with h2 | h2 <;> rw [h0, h1, h2] at hg <;> simp only [zero_smul, one_smul,
          add_zero, zero_add] at hg
      · exact ⟨h0, h1, h2⟩
      · exact absurd (by simpa [c'] using congrArg (fun z => (Additive.toMul z : E).1) hg) hc1
      · exact absurd (by simpa [b'] using congrArg (fun z => (Additive.toMul z : E).1) hg) hb1
      · have := congrArg (fun z => (Additive.toMul z : E).1) hg
        simp [b', c'] at this
        exact absurd (hinv b c hb hc this) hbc
      · exact absurd (by simpa [a'] using congrArg (fun z => (Additive.toMul z : E).1) hg) ha1
      · have := congrArg (fun z => (Additive.toMul z : E).1) hg
        simp [a', c'] at this
        exact absurd (hinv a c ha hc this) hac
      · have := congrArg (fun z => (Additive.toMul z : E).1) hg
        simp [a', b'] at this
        exact absurd (hinv a b ha hb this) hab
      · have := congrArg (fun z => (Additive.toMul z : E).1) hg
        simp [a', b', c'] at this
        refine absurd ?_ habc
        have hab' : a * b ∈ E := E.mul_mem ha hb
        have h4 : (a * b) * c = 1 := this
        exact (hinv _ _ hab' hc h4).symm
    fin_cases i
    · exact key.1
    · exact key.2.1
    · exact key.2.2
  have h3 := hli.fintype_card_le_finrank
  have hfin : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
  rw [Nat.card_zmod] at hcard
  have hcE : Nat.card E = Nat.card (Additive E) := Nat.card_congr Additive.toMul.symm
  rw [hcE, hcard]
  have : (3 : ℕ) ≤ Module.finrank (ZMod 2) (Additive E) := by simpa using h3
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ Module.finrank (ZMod 2) (Additive E) := Nat.pow_le_pow_right (by norm_num) this

theorem mul_comm_self_eq {x : G} (hx2 : x * x = 1) (n : G) : x * ⁅x, n⁆ = n * x * n⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  simp only [commutatorElement_def, hxi]
  calc x * (x * n * x * n⁻¹) = (x * x) * n * x * n⁻¹ := by group
    _ = n * x * n⁻¹ := by rw [hx2]; group

theorem false_of_three_commutators [Finite G] {T T₁ : Subgroup G} (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLc : Nat.card (normIn T T₁) ≤ 4) {Tx : Subgroup G}
    (hTx : ∃ g : G, Tx = conjSubgroup g T) {x : G} (hx : x ∈ Tx) (hx1 : x ≠ 1)
    (hxD : x ∈ classD T) (hx2 : x * x = 1) {L N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hLN : L ≤ N) (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hLnot : ¬ L ≤ Subgroup.normalizer (Tx : Set G)) {n₁ n₂ n₃ : G} (h₁ : n₁ ∈ N)
    (h₂ : n₂ ∈ N) (h₃ : n₃ ∈ N) (i1 : ⁅x, n₁⁆ ≠ 1) (i2 : ⁅x, n₂⁆ ≠ 1) (i3 : ⁅x, n₃⁆ ≠ 1)
    (i12 : ⁅x, n₁⁆ ≠ ⁅x, n₂⁆) (i13 : ⁅x, n₁⁆ ≠ ⁅x, n₃⁆) (i23 : ⁅x, n₂⁆ ≠ ⁅x, n₃⁆)
    (i123 : ⁅x, n₃⁆ ≠ ⁅x, n₁⁆ * ⁅x, n₂⁆) : False := by
  have hxa : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hmem : ∀ n ∈ N, ⁅x, n⁆ ∈ commSub x N := fun n hn =>
    (mem_commSub_iff hN hxa hxN).2 ⟨n, hn, rfl⟩
  have hle : commSub x N ≤ N ⊓ Subgroup.centralizer ({x} : Set G) := commSub_le hN hxa hxN
  have hEN : IsElemAbelian 2 (commSub x N) := isElemAbelian_of_le hN (hle.trans inf_le_left)
  have hE8 : 8 ≤ Nat.card (commSub x N) :=
    eight_le_card_of_indep hEN (hmem n₁ h₁) (hmem n₂ h₂) (hmem n₃ h₃) i1 i2 i3 i12 i13 i23 i123
  refine false_of_commutator_subgroup hP hTc hLc hTx hx hx1 hLnot hEN hE8 ?_ ?_ ?_
  · intro k hk
    exact Subgroup.mem_centralizer_iff.1 (hle hk).2 x (Set.mem_singleton x)
  · intro k hk l hl
    exact elemAbelian_mul_comm hN (hle hk).1 (hLN hl)
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := (mem_commSub_iff hN hxa hxN).1 hk
    rw [mul_comm_self_eq hx2]
    have := classD_conj hxD n⁻¹
    simpa using this

end CFSG.CGT.T75R
